//! The fast path against the accurate path, and its pass rate (docs/exp.md §4,
//! §8).

use super::{EPS, Reduced, X_OVERFLOW, X_ZERO, small, small_parts};
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::{Exact, entries, field, word};

/// The analytic miss rate of the rounding test (§4): about `2^−15`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 32768.0;

#[test]
fn fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6578_705f_7061_7373);
    let samples = 1u32 << 20;
    let (mut tried, mut missed) = (0u32, 0u32);
    for _ in 0..samples {
        // Uniform over the arguments with a finite, nonzero result.
        #[allow(clippy::cast_precision_loss)] // 53-bit integer
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = X_ZERO + u * (X_OVERFLOW - X_ZERO);
        let reduced = Reduced::of(x);
        if reduced.k < -1021 {
            continue;
        }
        tried += 1;
        match reduced.fast() {
            Some(y) => assert_eq!(y.to_bits(), reduced.accurate().to_bits(), "exp({x:e})"),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("exp fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

#[test]
fn small_arguments_agree_with_the_general_accurate_path() {
    let mut rng = SplitMix64::new(0x6578_705f_736d_616c);
    for _ in 0..20_000 {
        // 2^-54 <= |x| < 2^-30, every binade.
        let e = 969 + rng.next_u64() % 24;
        let x = f64::from_bits((e << 52) | (rng.next_u64() >> 12) | (rng.next_u64() & 1) << 63);
        if (-f64::from_bits(0x3c90_0000_0000_0000)..f64::from_bits(0x3ca0_0000_0000_0000))
            .contains(&x)
        {
            continue;
        }
        assert_eq!(
            small(x).to_bits(),
            Reduced::of(x).accurate().to_bits(),
            "exp({x:e})"
        );
    }
}

/// The fixture's 192-bit references: `(x, e^x)`.
fn precise() -> std::vec::Vec<(f64, Exact)> {
    let fixture = include_str!("../../../reference/fixtures/exp.json");
    entries(fixture, &["precise"])
        .into_iter()
        .map(|c| {
            let e = field(c, "e").parse().unwrap();
            (word(c, "x"), Exact::of_hex(field(c, "m"), e))
        })
        .collect()
}

#[test]
fn every_unrounded_result_is_within_its_certified_bound() {
    let small_arguments = f64::from_bits(0x3e10_0000_0000_0000);
    let cases = precise();
    assert_eq!(cases.len(), 1200);
    for (x, reference) in cases {
        let reduced = Reduced::of(x);
        // §6, general case: below 2^-123.9 (1097/1024 * 2^-124 < 2^-123.9).
        let y = Exact::of(reduced.accurate_value());
        assert!(y.within(&reference, 1097, 134), "accurate path, exp({x:e})");
        if reduced.k >= -1021 {
            // §4: eps_1 = 2^-69, relative to 2^(j/128) e^r = e^x / 2^k.
            let y = reduced.fast_value();
            let y = Exact::of(Q128::from_f64(y.hi()))
                .add(&Exact::of(Q128::from_f64(y.lo())))
                .mul(&Exact::pow2(i64::from(reduced.k)));
            assert!(y.within(&reference, 1, 69), "fast path, exp({x:e})");
        }
        if x.abs() < small_arguments {
            // §6, small arguments: within 2^-178, absolutely; e^x < 2 here.
            let (h, w) = small_parts(x);
            let error = Exact::of(Q128::from_f64(h))
                .add(&Exact::of(w))
                .sub(&reference)
                .abs();
            assert!(
                error.cmp(&Exact::pow2(-178)) != core::cmp::Ordering::Greater,
                "small path, exp({x:e})"
            );
        }
    }
}

/// The rounding test's constant is `ε₁·(1 + 2^−50)` with `ε₁ = 2^−69` (§5).
/// Results can't check it: the fast path's actual error is far below `ε₁`, so
/// a smaller constant would rarely change a result, but it would void §5's
/// proof.
#[test]
fn rounding_test_constant_is_its_definition() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(EPS.to_bits(), (two(-69) * (1.0 + two(-50))).to_bits());
}
