//! Oracle-free properties of the bivariate normal CDF: the measure's own
//! identities (reflection, monotonicity, symmetry, the marginal limits) must
//! hold within the reported bounds. Reference values are in
//! `crates/reference/tests/bivariate_normal.rs`.
//!
//! The properties are ported from ferro-risk's
//! `tests/bivariate_normal_property.rs` at commit `72db248c` (proptest
//! strategies replaced by seeded SplitMix64 draws, so a failure replays).

use super::*;
use crate::random::SplitMix64;

/// The smallest positive binary64; a subnormal result is exact to half of it.
const QUANTUM: f64 = f64::MIN_POSITIVE * f64::EPSILON;

fn unit(rng: &mut SplitMix64) -> f64 {
    (rng.next_u64() >> 11) as f64 / (1u64 << 53) as f64
}

fn argument(rng: &mut SplitMix64) -> f64 {
    match rng.next_u64() % 6 {
        0 => 0.0,
        1 | 2 => (unit(rng) * 2.0 - 1.0) * 8.0,
        _ => (unit(rng) * 2.0 - 1.0) * 40.0,
    }
}

fn correlation(rng: &mut SplitMix64) -> f64 {
    let canonical = 0.786_151_377_757_423_3;
    let edge = 1.0_f64.next_down();
    match rng.next_u64() % 10 {
        0 => canonical,
        1 => -canonical,
        2 => 0.0,
        3 => edge,
        4 => -edge,
        5 => edge.next_down(),
        6 => -edge.next_down(),
        _ => (unit(rng) * 2.0 - 1.0) * 0.95,
    }
}

fn bounded(x: f64, y: f64, rho: f64) -> BoundedProbability {
    let p = bivariate_norm_cdf_bounded(x, y, rho);
    assert!(
        (0.0..=1.0).contains(&p.value) && p.error.is_finite() && p.error >= 0.0,
        "{p:?} at ({x}, {y}, {rho})"
    );
    p
}

#[test]
fn independent_origin_is_a_quarter() {
    assert_eq!(bivariate_norm_cdf(0.0, 0.0, 0.0), 0.25);
}

#[test]
fn equicorrelated_origin_matches_sheppard() {
    // P(X <= 0, Y <= 0) = 1/4 + asin(rho) / (2 pi).
    let got = bivariate_norm_cdf(0.0, 0.0, 0.5);
    assert!((got - 1.0 / 3.0).abs() < 2.5e-16, "{got}");
}

/// `Phi2(a, b, rho) + Phi2(a, -b, -rho) = Phi(a)`: the two bounded values
/// reproduce the marginal within their own bounds.
#[test]
fn reflection_holds_within_the_reported_bounds() {
    let mut rng = SplitMix64::new(0x38);
    for _ in 0..4000 {
        let (a, b, rho) = (
            argument(&mut rng),
            argument(&mut rng),
            correlation(&mut rng),
        );
        let first = bounded(a, b, rho);
        let second = bounded(a, -b, -rho);
        let marginal = norm_cdf(a);
        let gap = (first.value + second.value - marginal).abs();
        let allowed = first.error + second.error + 8.0 * f64::EPSILON * marginal + 4.0 * QUANTUM;
        assert!(
            gap <= allowed,
            "gap {gap:e} > {allowed:e}: {first:?} {second:?} at a={a} b={b} rho={rho}"
        );
    }
}

/// Near unit correlation the result turns over within `sqrt(1 - rho^2)` of
/// `a = b`; the reflection must still close within the bounds there.
#[test]
fn reflection_holds_at_the_unit_correlation_edge() {
    let mut rng = SplitMix64::new(0x39);
    for _ in 0..2000 {
        let a = (unit(&mut rng) * 2.0 - 1.0) * 4.0;
        let gap = (unit(&mut rng) * 2.0 - 1.0) * 1e-7;
        for rho in [1.0_f64.next_down(), -1.0_f64.next_down()] {
            let b = if rho > 0.0 { a + gap } else { -a + gap };
            let first = bounded(a, b, rho);
            let second = bounded(a, -b, -rho);
            let marginal = norm_cdf(a);
            let residual = (first.value + second.value - marginal).abs();
            let allowed =
                first.error + second.error + 8.0 * f64::EPSILON * marginal + 4.0 * QUANTUM;
            assert!(
                residual <= allowed,
                "{residual:e} > {allowed:e} at a={a} rho={rho}"
            );
        }
    }
}

/// The CDF is nondecreasing in each argument, so bounded values at ordered
/// arguments cannot invert by more than their bounds.
#[test]
fn monotonicity_holds_within_the_reported_bounds() {
    let mut rng = SplitMix64::new(0x3a);
    for _ in 0..4000 {
        let (a, b, rho) = (
            argument(&mut rng),
            argument(&mut rng),
            correlation(&mut rng),
        );
        let step = unit(&mut rng) * 4.0;
        let lower = bounded(a, b, rho);
        let upper = bounded(a + step, b, rho);
        assert!(
            upper.value + upper.error + lower.error >= lower.value,
            "{lower:?} {upper:?} at ({a}, {b}, {rho}) step {step}"
        );
    }
}

/// Symmetry is structural: swapped arguments run the same arithmetic.
#[test]
fn swapped_arguments_are_bit_identical() {
    let mut rng = SplitMix64::new(0x3b);
    for _ in 0..4000 {
        let (a, b, rho) = (
            argument(&mut rng),
            argument(&mut rng),
            correlation(&mut rng),
        );
        let (p, q) = (bounded(a, b, rho), bounded(b, a, rho));
        assert_eq!(p.value.to_bits(), q.value.to_bits());
        assert_eq!(p.error.to_bits(), q.error.to_bits());
    }
}

/// The reusable evaluator is the one-shot function behind a built table.
#[test]
fn the_reusable_evaluator_returns_the_one_shot_bits() {
    let mut rng = SplitMix64::new(0x3c);
    for _ in 0..600 {
        let rho = correlation(&mut rng);
        let table = BivariateNormal::new(rho).unwrap();
        assert_eq!(table.correlation().to_bits(), rho.to_bits());
        for _ in 0..8 {
            let (a, b) = (argument(&mut rng), argument(&mut rng));
            assert_eq!(
                table.cdf(a, b).to_bits(),
                bivariate_norm_cdf(a, b, rho).to_bits()
            );
            assert_eq!(
                table.cdf_bounded(a, b),
                bivariate_norm_cdf_bounded(a, b, rho)
            );
        }
    }
}

/// At and above the relative floor the bound is the published contract.
#[test]
fn the_bound_is_the_published_contract() {
    let mut rng = SplitMix64::new(0x3d);
    for _ in 0..4000 {
        let (a, b, rho) = (
            (unit(&mut rng) * 2.0 - 1.0) * 8.0,
            (unit(&mut rng) * 2.0 - 1.0) * 8.0,
            correlation(&mut rng),
        );
        let p = bounded(a, b, rho);
        if p.value >= RELATIVE_FLOOR {
            assert_eq!(
                p.error,
                (RELATIVE_ERROR_BOUND * p.value).min(ABSOLUTE_ERROR_BOUND)
            );
        } else {
            assert_eq!(p.error, ABSOLUTE_ERROR_BOUND);
        }
    }
}

/// A tail value that underflows still bounds the positive probability it lost.
#[test]
fn underflowed_tail_keeps_a_positive_bound() {
    for (a, b, rho) in [(-38.5, -38.5, 0.5), (-38.0, -30.0, 0.786_151_377_757_423_3)] {
        let p = bivariate_norm_cdf_bounded(a, b, rho);
        assert!(p.value < f64::MIN_POSITIVE, "{p:?}");
        assert!(p.error > 0.0, "{p:?} cannot bound a positive probability");
    }
}

#[test]
fn nan_and_out_of_range_inputs_are_nan_with_a_nan_bound() {
    for (a, b, rho) in [
        (f64::NAN, 0.0, 0.5),
        (0.0, f64::NAN, 0.5),
        (0.0, 0.0, f64::NAN),
        (1e-315, 2.0, f64::NAN),
        (0.0, 0.0, 1.0 + f64::EPSILON),
        (0.0, 0.0, -1.5),
        (0.0, 0.0, f64::INFINITY),
    ] {
        let p = bivariate_norm_cdf_bounded(a, b, rho);
        assert!(p.value.is_nan() && p.error.is_nan(), "{p:?}");
        assert!(bivariate_norm_cdf(a, b, rho).is_nan());
    }
    assert_eq!(
        BivariateNormal::new(f64::NAN).unwrap_err(),
        InvalidCorrelation
    );
    assert_eq!(BivariateNormal::new(1.5).unwrap_err(), InvalidCorrelation);
    assert!(BivariateNormal::new(-1.0).is_ok() && BivariateNormal::new(1.0).is_ok());
}

/// Infinite and saturated thresholds take the exact limits; the quadratures'
/// squares overflow there.
#[test]
fn infinite_and_saturated_thresholds_take_the_exact_limits() {
    for (a, b, rho, expected) in [
        (f64::NEG_INFINITY, 0.0, 0.5, 0.0),
        (f64::INFINITY, -1.0, 0.5, norm_cdf(-1.0)),
        (-1.0, f64::INFINITY, -0.5, norm_cdf(-1.0)),
        (f64::INFINITY, f64::INFINITY, 0.3, 1.0),
        (
            3.037_841_545_524_638e140,
            -1.294_348_911_554_409_9e306,
            -7.1e-15,
            0.0,
        ),
        (
            3.3422e-319,
            3.046_634_548_494_395_7e130,
            0.968_749_534_338_684_3,
            0.5,
        ),
    ] {
        let p = bivariate_norm_cdf_bounded(a, b, rho);
        assert_eq!(p.value, expected, "({a}, {b}, {rho})");
        assert_eq!(bivariate_norm_cdf(a, b, rho), expected, "({a}, {b}, {rho})");
        assert!(p.error <= ABSOLUTE_ERROR_BOUND, "{p:?}");
    }
}

/// The exact degenerate limits `rho = -1, 0, 1`.
#[test]
fn degenerate_correlations_take_their_closed_forms() {
    let mut rng = SplitMix64::new(0x3e);
    for _ in 0..500 {
        let (a, b) = (argument(&mut rng), argument(&mut rng));
        let (lo, hi) = (a.min(b), a.max(b));
        assert_eq!(bivariate_norm_cdf(a, b, 0.0), norm_cdf(lo) * norm_cdf(hi));
        assert_eq!(bivariate_norm_cdf(a, b, 1.0), norm_cdf(lo));
        if hi < 39.0 && lo > -39.0 {
            assert_eq!(
                bivariate_norm_cdf(a, b, -1.0),
                (norm_cdf(lo) - norm_cdf(-hi)).max(0.0)
            );
        }
    }
}

/// The correlation-dependent rule limits and the Genz split are where a wrong
/// constant would hide: walk each at adjacent doubles and require the result
/// to be continuous to the absolute bound.
#[test]
fn results_are_continuous_across_every_rule_limit() {
    let limits = [
        0.055,
        0.20,
        0.38,
        0.54,
        0.66,
        0.75,
        0.81,
        0.89,
        GENZ_CORRELATION_SPLIT,
    ];
    let points = [
        (0.0, 0.0),
        (1.0, 1.0),
        (-2.0, -2.0),
        (1.5, -1.5),
        (3.0, 3.0),
        (-3.0, 0.5),
    ];
    for limit in limits {
        for sign in [1.0_f64, -1.0] {
            let below = sign * limit.next_down();
            let above = sign * limit.next_up();
            for (a, b) in points {
                let p = bivariate_norm_cdf(a, b, below);
                let q = bivariate_norm_cdf(a, b, above);
                // The value changes with rho at rate at most 1/(2 pi) per unit.
                let slope = (above - below).abs() / TAU;
                assert!(
                    (p - q).abs() <= 2.0 * ABSOLUTE_ERROR_BOUND + slope,
                    "({a}, {b}) at {limit}: {p:e} vs {q:e}"
                );
            }
        }
    }
}

/// The table's angular range is the library's correctly rounded `asin` of the
/// correlation, so it is odd in `rho` and shares that function's bits.
#[test]
fn angular_range_is_the_correctly_rounded_asin() {
    let mut rng = SplitMix64::new(0x3f);
    for _ in 0..20_000 {
        let rho = unit(&mut rng) * 0.925;
        let (Ok(pos), Ok(neg)) = (BivariateNormal::new(rho), BivariateNormal::new(-rho)) else {
            panic!("rho = {rho} is a valid correlation");
        };
        assert_eq!(pos.asr.to_bits(), asin(rho).to_bits());
        assert_eq!(neg.asr.to_bits(), (-pos.asr).to_bits());
    }
}

/// The invariants of ferro-risk's `bvn_bounded_invariants` fuzz target
/// (commit `72db248c`), over arbitrary binary64 bit patterns: NaN in, NaN
/// out; otherwise a probability with a finite bound never looser than the
/// contract; swapped arguments identical; the reflection identity within the
/// two bounds.
#[test]
fn arbitrary_bit_patterns_keep_the_invariants() {
    let mut rng = SplitMix64::new(0x40);
    for _ in 0..60_000 {
        let a = f64::from_bits(rng.next_u64());
        let b = if matches!(rng.next_u64() % 3, 0) {
            argument(&mut rng)
        } else {
            f64::from_bits(rng.next_u64())
        };
        let rho = match rng.next_u64() % 4 {
            0 => f64::from_bits(rng.next_u64()),
            1 => correlation(&mut rng),
            _ => (unit(&mut rng) * 2.0 - 1.0) * 1.0,
        };
        if !rho.is_nan() && !(-1.0..=1.0).contains(&rho) {
            continue;
        }
        let context = std::format!("a={a:e} b={b:e} rho={rho:e}");
        let p = bivariate_norm_cdf_bounded(a, b, rho);
        if a.is_nan() || b.is_nan() || rho.is_nan() {
            assert!(
                p.value.is_nan() && p.error.is_nan(),
                "NaN input returned {p:?} at {context}"
            );
            continue;
        }
        assert!(
            (0.0..=1.0).contains(&p.value) && p.error.is_finite() && p.error >= 0.0,
            "not a bounded probability: {p:?} at {context}"
        );
        assert!(
            p.error <= ABSOLUTE_ERROR_BOUND,
            "looser than the contract: {p:?} at {context}"
        );
        assert_eq!(
            p,
            bivariate_norm_cdf_bounded(b, a, rho),
            "asymmetric at {context}"
        );
        if a.is_finite() && b.is_finite() {
            let reflected = bivariate_norm_cdf_bounded(a, -b, -rho);
            let marginal = norm_cdf(a);
            let gap = (p.value + reflected.value - marginal).abs();
            let allowed = p.error + reflected.error + 8.0 * f64::EPSILON * marginal + 4.0 * QUANTUM;
            assert!(
                gap <= allowed,
                "reflection gap {gap:e} > {allowed:e} at {context}"
            );
        }
    }
}

#[test]
#[should_panic(expected = "cdf_slice: slices of different lengths")]
fn cdf_slice_rejects_slices_of_different_lengths() {
    BivariateNormal::new(0.5)
        .unwrap()
        .cdf_slice(&[0.0, 1.0], &[0.0, 1.0], &mut [0.0]);
}

#[test]
#[should_panic(expected = "cdf_bounded_slice: slices of different lengths")]
fn cdf_bounded_slice_rejects_slices_of_different_lengths() {
    BivariateNormal::new(0.5).unwrap().cdf_bounded_slice(
        &[0.0],
        &[0.0, 1.0],
        &mut [BoundedProbability {
            value: 0.0,
            error: 0.0,
        }],
    );
}

#[test]
#[should_panic(expected = "bivariate_norm_cdf_slice: slices of different lengths")]
fn paired_slice_rejects_slices_of_different_lengths() {
    bivariate_norm_cdf_slice(&[0.0, 1.0], &[0.0, 1.0], &[0.5], &mut [0.0, 0.0]);
}

#[test]
#[should_panic(expected = "bivariate_norm_cdf_bounded_slice: slices of different lengths")]
fn paired_bounded_slice_rejects_slices_of_different_lengths() {
    bivariate_norm_cdf_bounded_slice(
        &[0.0],
        &[0.0],
        &[0.5],
        &mut [
            BoundedProbability {
                value: 0.0,
                error: 0.0,
            },
            BoundedProbability {
                value: 0.0,
                error: 0.0,
            },
        ],
    );
}
