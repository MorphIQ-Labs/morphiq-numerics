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
