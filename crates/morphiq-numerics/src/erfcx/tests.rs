use super::*;
use crate::normal::erfcx_slice;
use crate::random::{SplitMix64, unit_closed_open};
use crate::test_exact::{entries, word};
use std::vec::Vec;

#[test]
fn independently_rounded_witnesses_match() {
    for case in entries(
        include_str!("../../../reference/fixtures/erfcx.json"),
        &["cases"],
    ) {
        let x = word(case, "x");
        let y = word(case, "y");
        assert_eq!(erfcx(x).to_bits(), y.to_bits(), "x={:016x}", x.to_bits());
        if special(x).is_none() {
            assert_eq!(
                accurate::accurate(x).to_f64().to_bits(),
                y.to_bits(),
                "accurate x={:016x}",
                x.to_bits()
            );
        }
    }
}

pub(crate) fn corpus() -> Vec<f64> {
    let mut xs: Vec<f64> = entries(
        include_str!("../../../reference/fixtures/erfcx.json"),
        &["cases"],
    )
    .into_iter()
    .map(|case| word(case, "x"))
    .collect();
    let mut rng = SplitMix64::new(0x34_51ad);
    for _ in 0..32768 {
        let u = unit_closed_open(rng.next_u64());
        xs.extend([
            -26.628 + 26.128 * u,
            -0.5 + 16.5 * u,
            16. + 496. * u,
            512. + 4096. * u,
            f64::from_bits(rng.next_u64()),
        ]);
    }
    for (low, width) in [(-26.628, 26.128), (-0.5, 16.5), (16., 496.), (512., 4096.)] {
        for _ in 0..4096 {
            xs.push(low + width * unit_closed_open(rng.next_u64()));
        }
    }
    xs
}

#[test]
fn erfcx_lanes_return_scalar_bits_on_mixed_regions_and_remainders() {
    let xs = corpus();
    for n in (0..=17).chain([xs.len()]) {
        let xs = &xs[..n];
        let mut out = std::vec![0.; n];
        erfcx_slice(xs, &mut out);
        for (&x, &y) in xs.iter().zip(&out) {
            assert_eq!(y.to_bits(), erfcx(x).to_bits(), "x={:016x}", x.to_bits());
        }
    }
}

#[test]
fn positive_finite_tail_never_loses_mass() {
    let mut previous = 1.;
    for exponent in 0..=1023u64 {
        for fraction in [0, 1 << 51, (1 << 52) - 1] {
            let x = f64::from_bits(((exponent + 1023) << 52) | fraction);
            let y = erfcx(x);
            assert!(y > 0. && y <= previous, "x={x:e}, y={y:e}");
            previous = y;
        }
    }
}

#[test]
#[should_panic(expected = "erfcx_slice: slices of different lengths")]
fn slice_rejects_length_mismatch() {
    erfcx_slice(&[0.], &mut []);
}

#[test]
#[ignore = "local fallback-rate measurement"]
fn erfcx_fallback_rates() {
    let mut rng = SplitMix64::new(0x34_fa11);
    for (low, width) in [(-0.5, 16.5), (16., 496.), (512., 4096.), (-26.628, 26.128)] {
        let mut rejected = 0;
        for _ in 0..1 << 20 {
            let x = low + width * unit_closed_open(rng.next_u64());
            let (h, l, _) = fast_value(x);
            if decide(h, l, EPS_T).is_none() {
                rejected += 1;
            }
        }
        std::eprintln!("[{low},{}): {rejected}/1048576", low + width);
    }
}

#[test]
fn subnormal_grid_test_agrees_with_single_rounding_of_q256() {
    let mut rng = SplitMix64::new(0x34_5ab0);
    let mut xs = Vec::new();
    for _ in 0..100_000 {
        let x = f64::from_bits(
            X_SUB.to_bits() + rng.next_u64() % (f64::MAX.to_bits() - X_SUB.to_bits() + 1),
        );
        assert_eq!(
            erfcx(x).to_bits(),
            accurate::accurate(x).to_f64().to_bits(),
            "x={:016x}",
            x.to_bits()
        );
        xs.push(x);
    }
    let mut out = std::vec![0.; xs.len()];
    erfcx_slice(&xs, &mut out);
    for (&x, &y) in xs.iter().zip(&out) {
        assert_eq!(erfcx(x).to_bits(), y.to_bits());
    }
}

#[test]
fn representative_fast_paths_decide_and_match_the_oracle() {
    // Returning Q256 unconditionally would preserve numerical tests while
    // losing the fast-path contract. These oracle-backed witnesses catch
    // that regression, including unnormalized exponential-stage outputs.
    let cases = entries(
        include_str!("../../../reference/fixtures/erfcx.json"),
        &["cases"],
    );
    for x in [0.3, 32., 1024., -2., -20., 1e308] {
        let got = match region(x) {
            Region::T => fast_t(x),
            Region::YA => fast_ya(x),
            Region::YB => fast_yb(x),
            Region::N => fast_n(x),
        }
        .unwrap_or_else(|| panic!("representative fast path rejected x={x:e}"));
        let case = cases
            .iter()
            .find(|case| word(case, "x").to_bits() == x.to_bits())
            .unwrap();
        assert_eq!(got.to_bits(), word(case, "y").to_bits());
    }
}

/// Which part of `erfcx` decides `x`, and its value: `erfcx`'s branches, for
/// the native measurements' path counts.
#[cfg(feature = "simd")]
fn decided_by(x: f64) -> (&'static str, f64) {
    if let Some(y) = special(x) {
        return ("screen", y);
    }
    let (name, fast) = match region(x) {
        Region::T => ("table", fast_t(x)),
        Region::YA => ("asymptotic", fast_ya(x)),
        Region::YB => ("reciprocal", fast_yb(x)),
        Region::N => ("negative", fast_n(x)),
    };
    match fast {
        Some(y) => (name, y),
        None => ("accurate", accurate::accurate(x).to_f64()),
    }
}

/// Same-host timing of `erfcx`, scalar and per lane backend
/// (`lanes::tests::bench`); no timing assertion.
#[cfg(feature = "simd")]
#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance() {
    use crate::lanes::tests::bench::{Draw, function, tables};
    use core::mem::size_of_val;
    tables(&[
        ("erfcx::tables::T", size_of_val(&super::tables::T)),
        ("erfcx::tables::PA", size_of_val(&super::tables::PA)),
        (
            "erfcx::accurate_tables::F_AT_C",
            size_of_val(&super::accurate_tables::F_AT_C),
        ),
        (
            "erfcx::accurate_tables::RECIP",
            size_of_val(&super::accurate_tables::RECIP),
        ),
        (
            "erfcx::accurate_tables::T2",
            size_of_val(&super::accurate_tables::T2),
        ),
    ]);
    static ERFCX_SCREENED: [f64; 6] = [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        -27.0,
        0.0,
        1e-20,
    ];
    static ERFCX_BROAD: Draw = Draw::Uniform(-26.6, 4122.6);
    static ERFCX_MIXED: [Draw; 6] = [
        Draw::Uniform(-0.5, 16.5),
        Draw::Uniform(16.0, 496.0),
        Draw::Uniform(512.0, 4096.0),
        Draw::Uniform(-26.6, 26.1),
        Draw::Bits(0x7fc2_0dd7_5042_9b6e, 0x002d_f228_afbd_6491),
        Draw::Values(&ERFCX_SCREENED),
    ];
    static ERFCX_TABLE: Draw = Draw::Uniform(-0.5, 16.5);
    function::<super::lanes::Erfcx>(
        "erfcx",
        decided_by,
        &[
            ("table", ERFCX_TABLE),
            ("positive_common", Draw::Uniform(0.0, 6.0)),
            ("asymptotic", Draw::Uniform(16.0, 496.0)),
            ("reciprocal", Draw::Uniform(512.0, 4096.0)),
            ("negative", Draw::Uniform(-26.6, 26.1)),
            (
                "subnormal",
                Draw::Bits(0x7fc2_0dd7_5042_9b6e, 0x002d_f228_afbd_6491),
            ),
            ("screened", Draw::Values(&ERFCX_SCREENED)),
            ("mixed", Draw::Mixed(&ERFCX_MIXED)),
            ("fallback", Draw::Fallback(&ERFCX_BROAD)),
        ],
    );
}
