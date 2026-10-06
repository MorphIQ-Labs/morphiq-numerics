//! `expm1`'s unrounded results against their certified bounds, its fast paths
//! against its accurate paths, and its rounding-test constant (docs/expm1.md).

use super::{
    EPS, SMALL, X_MINUS_ONE, X_OVERFLOW, general_accurate, general_fast, small_accurate, small_fast,
};
use crate::double_word::DoubleWord;
use crate::exp::Reduced;
use crate::ln::decide_with;
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::{Exact, entries, field, word};

fn double_word(y: DoubleWord) -> Exact {
    Exact::of(Q128::from_f64(y.hi())).add(&Exact::of(Q128::from_f64(y.lo())))
}

#[test]
fn every_unrounded_result_is_within_its_certified_bound() {
    let fixture = include_str!("../../../reference/fixtures/expm1.json");
    let cases = entries(fixture, &["precise"]);
    assert_eq!(cases.len(), 1200);
    for c in cases {
        let x = word(c, "x");
        let v = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        let reference = if field(c, "negative") == "true" {
            v.neg()
        } else {
            v
        };
        if x.abs() < SMALL {
            // §3: 13·2^-66 ≈ 2^-62.3. §4: 2^-123.
            assert!(
                double_word(small_fast(x)).within(&reference, 13, 66),
                "small fast, expm1({x:e})"
            );
            assert!(
                Exact::of(small_accurate(x)).within(&reference, 1, 123),
                "small accurate, expm1({x:e})"
            );
        } else {
            // §5: 2^-62 and 2^-118.
            let reduced = Reduced::of(x);
            assert!(
                double_word(general_fast(&reduced)).within(&reference, 1, 62),
                "fast, expm1({x:e})"
            );
            assert!(
                Exact::of(general_accurate(&reduced)).within(&reference, 1, 118),
                "accurate, expm1({x:e})"
            );
        }
    }
}

/// The analytic miss rate with `ε₁ = 2^−62`: at most `2·ε₁·2^53 = 2^−8`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 256.0;

#[test]
fn fast_paths_agree_with_the_accurate_paths_and_mostly_decide() {
    let mut rng = SplitMix64::new(0x6578_6d31_7061_7373);
    for (name, small) in [("small", true), ("general", false)] {
        let (mut tried, mut missed) = (0u32, 0u32);
        for _ in 0..(1u32 << 19) {
            #[allow(clippy::cast_precision_loss)] // 53-bit integer
            let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
            let x = if small {
                // 2^-54 <= |x| < 2^-5, every binade.
                let e = 969 + rng.next_u64() % 49;
                f64::from_bits((e << 52) | (rng.next_u64() >> 12) | ((rng.next_u64() & 1) << 63))
            } else {
                X_MINUS_ONE + u * (X_OVERFLOW - X_MINUS_ONE)
            };
            if small != (x.abs() < SMALL) || x.abs() < f64::from_bits(0x3c90_0000_0000_0000) {
                continue;
            }
            tried += 1;
            let (fast, accurate) = if small {
                (small_fast(x), small_accurate(x))
            } else {
                let reduced = Reduced::of(x);
                (general_fast(&reduced), general_accurate(&reduced))
            };
            match decide_with(fast, EPS) {
                Some(y) => assert_eq!(y.to_bits(), accurate.to_f64().to_bits(), "expm1({x:e})"),
                None => missed += 1,
            }
        }
        let rate = f64::from(missed) / f64::from(tried);
        std::eprintln!(
            "expm1 {name} fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})"
        );
        assert!(
            rate <= 4.0 * ANALYTIC_MISS_RATE,
            "{name} miss rate {rate:e}"
        );
    }
}

/// The rounding test's constant is `ε₁·(1 + 2^−50)` with `ε₁ = 2^−62` (§6).
#[test]
fn rounding_test_constant_is_its_definition() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(EPS.to_bits(), (two(-62) * (1.0 + two(-50))).to_bits());
}
