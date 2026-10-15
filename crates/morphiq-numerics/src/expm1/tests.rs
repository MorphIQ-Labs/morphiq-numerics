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

#[test]
fn stage_subtraction_budget_contains_independent_reference_values() {
    use super::stages::{E_A, E_B, parts};
    for c in entries(
        include_str!("../../../reference/fixtures/expm1.json"),
        &["precise"],
    ) {
        let x = word(c, "x");
        if !(x > -37.0 && x < 704.0 && x.abs() >= SMALL) {
            continue;
        }
        let mut reference = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        if field(c, "negative") == "true" {
            reference = reference.neg();
        }
        let r = crate::exp::Stages::of(x);
        let k = i32::try_from(r.exponent()).unwrap();
        let reference = reference.mul(&Exact::pow2(-i64::from(k)));
        for ((h, l), base) in [(r.a_value(), E_A), (r.b_value(), E_B)] {
            let (s, lo, eps) = parts(h, l, k, base);
            let center = Exact::of_f64(s).add(&Exact::of_f64(lo));
            let margin = Exact::of_f64(lo)
                .abs()
                .add(&Exact::of_f64(eps))
                .mul(&Exact::pow2(-53));
            assert!(
                center
                    .sub(&reference)
                    .abs()
                    .add(&margin)
                    .cmp(&Exact::of_f64(eps))
                    .is_le(),
                "expm1({x:e})"
            );
        }
    }
}

#[test]
fn exponential_stages_agree_with_accurate_results_and_mostly_decide() {
    let mut rng = SplitMix64::new(0x6578_6d31_7374_6167);
    for (lo, hi) in [
        (-37.0, -SMALL),
        (SMALL, 704.0),
        (-1.0, -SMALL),
        (SMALL, 1.0),
    ] {
        let (mut a_missed, mut b_missed) = (0, 0);
        for _ in 0..(1 << 18) {
            #[allow(clippy::cast_precision_loss)] // 53-bit integer
            let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
            let x = lo + (hi - lo) * u;
            let r = crate::exp::Stages::of(x);
            let k = i32::try_from(r.exponent()).unwrap();
            let expected = general_accurate(&Reduced::of(x)).to_f64();
            for ((h, l), base, missed) in [
                (r.a_value(), super::stages::E_A, &mut a_missed),
                (r.b_value(), super::stages::E_B, &mut b_missed),
            ] {
                match super::stages::subtract(h, l, k, base) {
                    Some(v) => assert_eq!(v.to_bits(), expected.to_bits(), "expm1({x:e})"),
                    None => *missed += 1,
                }
            }
        }
        std::eprintln!(
            "expm1 stages ({lo},{hi}): A misses {a_missed}, B misses {b_missed} of 262144"
        );
        assert!(b_missed < 256);
    }
}

/// Which part of `expm1` decides `x`, and its value: `expm1`'s branches, for
/// the native measurements' path counts.
#[cfg(feature = "simd")]
fn decided_by(x: f64) -> (&'static str, f64) {
    use super::{
        EPS, SMALL, TINY, X_MINUS_ONE, X_OVERFLOW, general_accurate, general_fast, small_accurate,
        small_fast, stages,
    };
    let magnitude = x.abs();
    if x.is_nan() || x >= X_OVERFLOW || x <= X_MINUS_ONE || magnitude < TINY {
        return ("screen", super::expm1(x));
    }
    if magnitude < SMALL {
        if let Some(y) = decide_with(small_fast(x), EPS) {
            return ("small_fast", y);
        }
        return ("small_accurate", small_accurate(x).to_f64());
    }
    if let Some(y) = stages::stages(x) {
        return ("stages", y);
    }
    let reduced = Reduced::of(x);
    if let Some(y) = decide_with(general_fast(&reduced), EPS) {
        return ("fast", y);
    }
    ("accurate", general_accurate(&reduced).to_f64())
}

/// Same-host timing of `expm1`, scalar and per lane backend
/// (`lanes::tests::bench`); no timing assertion.
#[cfg(feature = "simd")]
#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance() {
    use crate::lanes::tests::bench::{Draw, function, tables};
    use core::mem::size_of_val;
    tables(&[
        ("expm1::POLY", size_of_val(&super::tables::POLY)),
        (
            "expm1::RECIPROCALS",
            size_of_val(&super::tables::RECIPROCALS),
        ),
    ]);
    static EXPM1_SCREENED: [f64; 6] = [f64::NAN, f64::INFINITY, -40.0, 710.0, 1e-300, 0.0];
    static EXPM1_DOMAIN: Draw = Draw::Uniform(-37.4, 746.4);
    static EXPM1_MIXED: [Draw; 4] = [
        Draw::Uniform(-30.0, 30.0),
        Draw::Uniform(-1.0 / 32.0, 1.0 / 16.0),
        Draw::Values(&EXPM1_SCREENED),
        Draw::Uniform(-37.4, 746.4),
    ];
    static EXPM1_SMALL: Draw = Draw::Uniform(-1.0 / 32.0, 1.0 / 16.0);
    function::<crate::expm1::lanes::Expm1>(
        "expm1",
        decided_by,
        &[
            ("common", Draw::Uniform(-30.0, 30.0)),
            ("small", EXPM1_SMALL),
            ("domain", EXPM1_DOMAIN),
            ("screened", Draw::Values(&EXPM1_SCREENED)),
            ("mixed", Draw::Mixed(&EXPM1_MIXED)),
            ("fallback", Draw::Fallback(&EXPM1_DOMAIN)),
            ("fallback_small", Draw::Fallback(&EXPM1_SMALL)),
        ],
    );
}
