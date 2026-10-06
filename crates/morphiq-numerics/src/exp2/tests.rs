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
