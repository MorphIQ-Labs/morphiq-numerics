//! The fast paths against the accurate paths, their pass rates, and every
//! unrounded result against its certified bound (docs/ln.md §4–§7).

use super::{EPS, Reduced, TWO_M7, decide, ln_1p_double_word, series, split};
use crate::double_word::DoubleWord;
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::Exact;
use serde_json::Value;

fn double_word(y: DoubleWord) -> Exact {
    Exact::of(Q128::from_f64(y.hi())).add(&Exact::of(Q128::from_f64(y.lo())))
}

/// The fixture's 192-bit references for `function`: `(x, value)`.
fn precise(function: &str) -> std::vec::Vec<(f64, Exact)> {
    let fixture: Value =
        serde_json::from_str(include_str!("../../../reference/fixtures/ln.json")).unwrap();
    fixture["precise"][function]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let x = f64::from_bits(u64::from_str_radix(c["x"].as_str().unwrap(), 16).unwrap());
            let v = Exact::of_hex(c["m"].as_str().unwrap(), c["e"].as_i64().unwrap());
            (
                x,
                if c["negative"].as_bool().unwrap() {
                    v.neg()
                } else {
                    v
                },
            )
        })
        .collect()
}

#[test]
fn every_unrounded_ln_is_within_its_certified_bound() {
    for (x, reference) in precise("ln") {
        let reduced = Reduced::of(x);
        // §4: 2^-64. §6: 2^-123.
        assert!(
            double_word(reduced.fast_value()).within(&reference, 1, 64),
            "fast, ln({x:e})"
        );
        let y = Exact::of(reduced.accurate_value(reduced.z_exact()));
        assert!(y.within(&reference, 1, 123), "accurate, ln({x:e})");
    }
}

#[test]
fn every_unrounded_ln_1p_is_within_its_certified_bound() {
    for (x, reference) in precise("ln_1p") {
        let (fast, accurate) = if x.abs() < TWO_M7 {
            let z = Q128::from_f64(x);
            (ln_1p_double_word(DoubleWord::from_f64(x)), z.mul(series(z)))
        } else {
            let (h, l) = split(x);
            let reduced = Reduced::of(h);
            (
                reduced.fast_value().add_f64(l / h),
                reduced.accurate_value(reduced.z_prime(l)),
            )
        };
        // §7: the fast path within 2^-63 (2^-64 on the z = x branch), the
        // accurate path within 2^-123.
        assert!(
            double_word(fast).within(&reference, 1, 63),
            "fast, ln_1p({x:e})"
        );
        assert!(
            Exact::of(accurate).within(&reference, 1, 123),
            "accurate, ln_1p({x:e})"
        );
    }
}

/// The analytic miss rate of the rounding test with `ε₁ = 2^−63`: an
/// argument misses when its value lies within `ε₁·|Y|` of a breakpoint, a
/// fraction `2·ε₁·|Y| / ulp(Y) ≤ 2^−9` of each gap.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 512.0;

#[test]
fn ln_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6c6e_5f70_6173_7331);
    let (mut tried, mut missed) = (0u32, 0u32);
    for n in 0..(1u32 << 20) {
        // Every positive finite encoding, and arguments near 1.
        let x = if n % 2 == 0 {
            f64::from_bits(1 + rng.next_u64() % 0x7fef_ffff_ffff_ffff)
        } else {
            f64::from_bits(0x3fe0_0000_0000_0000 + rng.next_u64() % (1 << 53))
        };
        if x == 1.0 {
            continue;
        }
        let reduced = Reduced::of(x);
        tried += 1;
        match decide(reduced.fast_value()) {
            Some(y) => {
                let accurate = reduced.accurate_value(reduced.z_exact()).to_f64();
                assert_eq!(y.to_bits(), accurate.to_bits(), "ln({x:e})");
            }
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("ln fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

#[test]
fn ln_1p_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6c6e_3170_7061_7331);
    let (mut tried, mut missed) = (0u32, 0u32);
    for _ in 0..(1u32 << 20) {
        // Magnitudes from 2^-54 to 2^1023, either sign where ln_1p is defined.
        let e = 969 + rng.next_u64() % 1077;
        let x = f64::from_bits((e << 52) | (rng.next_u64() >> 12) | (rng.next_u64() & 1) << 63);
        if x <= -1.0 {
            continue;
        }
        tried += 1;
        let (fast, accurate) = if x.abs() < TWO_M7 {
            let z = Q128::from_f64(x);
            (
                decide(ln_1p_double_word(DoubleWord::from_f64(x))),
                z.mul(series(z)),
            )
        } else {
            let (h, l) = split(x);
            let reduced = Reduced::of(h);
            (
                decide(reduced.fast_value().add_f64(l / h)),
                reduced.accurate_value(reduced.z_prime(l)),
            )
        };
        match fast {
            Some(y) => assert_eq!(y.to_bits(), accurate.to_f64().to_bits(), "ln_1p({x:e})"),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("ln_1p fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

/// The rounding test's constant is `ε₁·(1 + 2^−50)` with `ε₁ = 2^−63` (§5).
#[test]
fn rounding_test_constant_is_its_definition() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(EPS.to_bits(), (two(-63) * (1.0 + two(-50))).to_bits());
}

#[test]
fn ln_1p_of_a_double_word_is_within_its_certified_bound() {
    let fixture: Value =
        serde_json::from_str(include_str!("../../../reference/fixtures/ln.json")).unwrap();
    let word = |c: &Value, k: &str| {
        f64::from_bits(u64::from_str_radix(c[k].as_str().unwrap(), 16).unwrap())
    };
    let cases = fixture["precise"]["ln_1p_z"].as_array().unwrap();
    assert!(cases.len() > 500);
    for c in cases {
        let (z_hi, z_lo) = (word(c, "z_hi"), word(c, "z_lo"));
        let v = Exact::of_hex(c["m"].as_str().unwrap(), c["e"].as_i64().unwrap());
        let reference = if c["negative"].as_bool().unwrap() {
            v.neg()
        } else {
            v
        };
        // §4, step 4: 3·2^-66 (formal/ln/p.g).
        let p = ln_1p_double_word(DoubleWord::sum(z_hi, z_lo));
        assert!(
            double_word(p).within(&reference, 3, 66),
            "ln(1 + {z_hi:e} + {z_lo:e})"
        );
    }
}

/// §5's test at its boundary: `y_hi` returned exactly when `|y_lo| + EPS·|y_hi|`
/// is below half the smaller gap, for either sign and at a power of two, where
/// the gap toward zero is half the other.
#[test]
fn the_rounding_test_decides_at_its_boundary() {
    for y_hi in [1.5, -1.5, 1.0, -1.0, 0.75, -0.75, 600.25, -600.25] {
        let magnitude = f64::abs(y_hi);
        let mut gap = crate::ulp::ulp(magnitude);
        if magnitude.to_bits() & super::FRACTION == 0 {
            gap *= 0.5;
        }
        let margin = EPS * magnitude;
        for (y_lo, decided) in [
            (0.5 * gap - 2.0 * margin, true),
            (0.5 * gap - 0.5 * margin, false),
            (-(0.5 * gap - 2.0 * margin), true),
            (-(0.5 * gap - 0.5 * margin), false),
        ] {
            let y = DoubleWord::sum(y_hi, y_lo);
            assert_eq!(decide(y).is_some(), decided, "({y_hi:e}, {y_lo:e})");
        }
    }
}
