//! `exp2`'s unrounded results against their certified bounds, and its fast
//! path against its accurate path (docs/exp2.md).

use super::{Reduced, X_OVERFLOW, X_ZERO};
use crate::exp::decide_scaled;
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::{Exact, entries, field, word};

#[test]
fn every_unrounded_result_is_within_its_certified_bound() {
    let fixture = include_str!("../../../reference/fixtures/exp2.json");
    let cases = entries(fixture, &["precise"]);
    assert_eq!(cases.len(), 1200);
    for c in cases {
        let x = word(c, "x");
        let reference = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        let reduced = Reduced::of(x);
        // §4: below 2^-123.9 (1097/1024 * 2^-124 < 2^-123.9).
        let y = Exact::of(reduced.accurate_value());
        assert!(
            y.within(&reference, 1097, 134),
            "accurate path, exp2({x:e})"
        );
        if reduced.k >= -1021 {
            // §3: eps_1 = 2^-69, relative to 2^x / 2^k.
            let y = reduced.fast_value();
            let y = Exact::of(Q128::from_f64(y.hi()))
                .add(&Exact::of(Q128::from_f64(y.lo())))
                .mul(&Exact::pow2(i64::from(reduced.k)));
            assert!(y.within(&reference, 1, 69), "fast path, exp2({x:e})");
        }
    }
}

/// The analytic miss rate of the rounding test with `ε₁ = 2^−69`, as for `exp`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 32768.0;

#[test]
fn fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6578_7032_7061_7373);
    let (mut tried, mut missed) = (0u32, 0u32);
    for _ in 0..(1u32 << 20) {
        #[allow(clippy::cast_precision_loss)] // 53-bit integer
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = X_ZERO + u * (X_OVERFLOW - X_ZERO);
        let reduced = Reduced::of(x);
        if reduced.k < -1021 {
            continue;
        }
        tried += 1;
        match decide_scaled(reduced.fast_value(), reduced.k) {
            Some(y) => assert_eq!(
                y.to_bits(),
                reduced.accurate_value().to_f64().to_bits(),
                "exp2({x:e})"
            ),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("exp2 fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

#[test]
fn exponential_stages_meet_their_unscaled_bounds() {
    for c in entries(
        include_str!("../../../reference/fixtures/exp2.json"),
        &["precise"],
    ) {
        let x = word(c, "x");
        if !(x.abs() >= f64::from_bits((1023 - 55) << 52) && x.abs() < 1016.0) {
            continue;
        }
        let r = super::stages::Stages::of(x);
        let reference =
            Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap()).mul(&Exact::pow2(-r.k));
        for ((h, l), bound) in [
            (
                r.a_value(),
                Exact::of_f64(302.0)
                    .mul(&Exact::pow2(-69))
                    .add(&Exact::pow2(-63)),
            ),
            (r.b_value(), Exact::of_f64(209.0).mul(&Exact::pow2(-78))),
        ] {
            let value = Exact::of_f64(h).add(&Exact::of_f64(l));
            assert!(
                value.sub(&reference).abs().cmp(&bound).is_le(),
                "exp2({x:e})"
            );
        }
    }
}

#[test]
fn exponential_stages_agree_with_accurate_results_and_mostly_decide() {
    let mut rng = SplitMix64::new(0x6578_7032_7374_6167);
    let mut missed = 0;
    for _ in 0..(1 << 20) {
        #[allow(clippy::cast_precision_loss)] // 53-bit integer
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = -1016.0 + 2032.0 * u;
        if let Some(v) = super::stages::stages(x) {
            assert_eq!(
                v.to_bits(),
                Reduced::of(x).accurate_value().to_f64().to_bits(),
                "exp2({x:e})"
            );
        } else {
            missed += 1;
        }
    }
    std::eprintln!("exp2 stages: {missed} of 1048576 fall through both stages");
    assert!(missed < 128);
}

#[test]
fn dyadic_reduction_boundaries_and_neighbors_round_correctly() {
    // Every table boundary and midpoint at representative exponents, including
    // both screen edges. The accurate path is supplemented by independent
    // fixtures and the unrounded bound test above.
    for k in [-1016.0, -1000.0, -2.0, -1.0, 0.0, 1.0, 2.0, 1000.0, 1015.0] {
        for j in 0..=1024 {
            let x = k + f64::from(j) / 1024.0;
            for x in [x.next_down(), x, x.next_up()] {
                assert_eq!(
                    super::exp2(x).to_bits(),
                    Reduced::of(x).accurate_value().to_f64().to_bits(),
                    "exp2({x:e})"
                );
            }
        }
    }
}

/// The predecessor of 1/128 is the tight residual case missed by the old
/// 2^-59 derivation. Check both signs against exact dyadic values.
#[test]
fn fallback_residual_reaches_the_proved_lower_bound() {
    for sign in [-1.0, 1.0] {
        let x = sign * 0.007_812_5_f64.next_down();
        let reduced = Reduced::of(x);
        let expected = Exact::of_f64(-sign).mul(&Exact::pow2(-60));
        assert!(Exact::of_f64(reduced.r).cmp(&expected).is_eq());
        let reconstructed = Exact::of_f64(f64::from(reduced.k))
            .add(&Exact::of_f64(f64::from(u32::try_from(reduced.j).unwrap())).mul(&Exact::pow2(-7)))
            .add(&Exact::of_f64(reduced.r));
        assert!(reconstructed.cmp(&Exact::of_f64(x)).is_eq());
    }
}
