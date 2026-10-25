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

/// The reported bound is the bound of the correlation, whatever the value, and
/// no value is given a relative bound.
#[test]
fn the_reported_bound_is_the_correlations() {
    let mut rng = SplitMix64::new(0x3d);
    for _ in 0..4000 {
        let (a, b, rho) = (
            (unit(&mut rng) * 2.0 - 1.0) * 8.0,
            (unit(&mut rng) * 2.0 - 1.0) * 8.0,
            correlation(&mut rng),
        );
        let p = bounded(a, b, rho);
        assert_eq!(p.error, absolute_error_bound(rho));
        assert!(p.error <= ABSOLUTE_ERROR_BOUND);
        assert_eq!(
            BivariateNormal::new(rho).unwrap().absolute_error_bound(),
            absolute_error_bound(rho)
        );
    }
}

/// The bound is the proved bound of the rule `|rho|` selects: it grows with the
/// rule, is the same for both signs, and is NaN where the correlation is invalid.
#[test]
fn the_bound_follows_the_selected_rule() {
    for (index, limit) in LOW_RULE_LIMITS.into_iter().enumerate() {
        // A rule serves the correlations below its limit; the limit itself is the next rule's.
        for sign in [1.0, -1.0] {
            assert_eq!(
                absolute_error_bound(sign * limit.next_down()),
                LOW_RULE_BOUNDS[index]
            );
            assert_eq!(
                absolute_error_bound(sign * limit),
                LOW_RULE_BOUNDS[index + 1]
            );
        }
        assert!(LOW_RULE_BOUNDS[index] < LOW_RULE_BOUNDS[index + 1]);
    }
    assert_eq!(
        absolute_error_bound(0.9),
        LOW_RULE_BOUNDS[LOW_RULE_BOUNDS.len() - 1]
    );
    for rho in [f64::NAN, 1.5, -1.5, f64::INFINITY] {
        assert!(absolute_error_bound(rho).is_nan());
    }
    assert!(absolute_error_bound(0.5) <= ABSOLUTE_ERROR_BOUND);
}

/// The high-correlation branch carries its own proved bound for each sign, and
/// the whole function's bound is the largest of all of them.
#[test]
fn the_high_branch_bound_depends_on_the_sign_of_the_correlation() {
    for rho in [0.925, 0.95, 0.999, 1.0 - f64::EPSILON] {
        assert_eq!(absolute_error_bound(rho), HIGH_BOUND_POSITIVE);
        assert_eq!(absolute_error_bound(-rho), HIGH_BOUND_NEGATIVE);
        let table = BivariateNormal::new(-rho).unwrap();
        assert_eq!(table.absolute_error_bound(), HIGH_BOUND_NEGATIVE);
    }
    let largest = LOW_RULE_BOUNDS
        .iter()
        .copied()
        .chain([
            HIGH_BOUND_POSITIVE,
            HIGH_BOUND_NEGATIVE,
            CLOSED_FORM_BOUND,
            SINGLE_PHI_BOUND,
        ])
        .fold(0.0, f64::max);
    assert_eq!(largest, ABSOLUTE_ERROR_BOUND);
}

/// The integrand is zero from `phi = 700` on (from `hk >= 16`, from `hk / 2 +
/// bs / (2 xs) = 700`), and positive just below it.
#[test]
fn the_integrand_stops_at_the_exponent_cutoff() {
    // `bs = 0` and `hk >= 16`: the cutoff is on `hk / 2`.
    assert_eq!(integrand_term(0.0001, 1.0, 0.0, 1400.0), 0.0);
    assert!(integrand_term(0.0001, 1.0, 0.0, 1399.999).is_sign_positive());
    assert!(integrand_term(0.0001, 1.0, 0.0, 1399.999) > 0.0);
    // A node past the old cutoff of 100 is computed.
    assert!(integrand_term(0.0001, 1.0, 0.0, 300.0) > 0.0);
    // Below `HK_SPLIT` the cutoff is on `phi = hk / (1 + rs)`: `xs = 0.75` gives `rs = 0.5`.
    assert!(integrand_term(0.75, 1.0, 0.0, 15.999) > 0.0);
    assert_eq!(integrand_term(0.75, 1.0, 1100.0, 15.999), 0.0);
}

/// From `HK_SPLIT` on the two exponentials are the integrand's one: they agree with
/// `exp(-phi) / rs` to the single exponential's own rounding.
#[test]
fn the_split_exponent_agrees_with_the_single_exponential() {
    for &(xs, bs, hk) in &[
        (0.01, 0.0, 16.0),
        (0.1, 3.0, 40.0),
        (0.0001, 0.0, 120.0),
        (0.14, 1.0, 16.0),
        (0.05, 0.2, 60.0),
    ] {
        let rs = sqrt(1.0 - xs);
        let phi = bs / (2.0 * xs) + hk / (1.0 + rs);
        let single = exp(-phi) / rs;
        let split = integrand_term(xs, 1.0, bs, hk);
        assert!(
            ((split - single) / single).abs() < 1e-13,
            "xs {xs:e} bs {bs:e} hk {hk:e}: {split:e} against {single:e}"
        );
    }
}

/// The remainder correction is the integral it names: three values from a 50-digit
/// quadrature of `exp(-bs/(2 x^2) - hk/2) (G - T)` (the correction is negative: `G < T`), to the
/// rounding of its evaluation, which is under 5% of the smallest.
#[test]
fn the_closed_form_remainder_is_the_taylor_remainder_it_integrates() {
    for &(s, bs, hk, expected) in &[
        (0.003, 0.0, 100.0, -1.3241224e-38),
        (0.003, 1e-6, 100.0, -1.225685e-38),
        (0.0029, 0.0, 196.0, -1.3706128e-58),
    ] {
        let (c, d) = ((4.0 - hk) / 8.0, (12.0 - hk) / 16.0);
        let got = closed_form_remainder(s, bs, hk, c, d);
        assert!(
            ((got - expected) / expected).abs() < 5e-2,
            "s {s:e} bs {bs:e} hk {hk:e}: {got:e} against {expected:e}"
        );
    }
}

/// The closed form's remainder correction is far below its cap where it is used, and a
/// correction beyond the cap, or a NaN, is dropped.
#[test]
fn the_closed_form_remainder_is_within_its_cap_and_dropped_beyond_it() {
    let (s, hk) = (0.003, 16.0);
    let (c, d) = ((4.0 - hk) / 8.0, (12.0 - hk) / 16.0);
    let r = closed_form_remainder(s, 0.0, hk, c, d);
    assert!(r != 0.0 && r.abs() < REMAINDER_CAP / 10.0, "{r:e}");
    assert_eq!(closed_form_remainder(s, 0.0, hk, 1e9, d), 0.0);
    assert_eq!(closed_form_remainder(s, f64::NAN, hk, c, d), 0.0);
}

/// Where both thresholds are far below zero and the correlation is high, the
/// correlation integral is most of the result, so it is computed out to
/// `hk = 1400`: the leading term alone is `1.6` off in relative terms at
/// `P(-12, -12; 0.99)`.
#[test]
fn the_high_branch_keeps_the_integral_in_the_deep_tail() {
    // Reference values from a 60-digit adaptive Gauss-Legendre integral of Plackett's identity
    // (`generators/bivariate_normal_reference.py`, kind `deep`), rounded to binary64.
    let rows = [
        (-12.0, -12.0, 0.99, 6.959e-34),
        (-14.0, -14.0, 0.99, 2.483e-45),
        (-20.0, -20.0, 0.999, 1.800e-89),
    ];
    for (x, y, rho, expected) in rows {
        let got = bivariate_norm_cdf(x, y, rho);
        let relative = ((got - expected) / expected).abs();
        assert!(
            relative < 1e-3,
            "P({x}, {y}; {rho}) = {got:e}, expected {expected:e}"
        );
    }
}

/// A refused correlation says so when displayed.
#[test]
fn the_refusal_describes_the_correlation() {
    use core::fmt::Write;
    struct Buffer([u8; 64], usize);
    impl Write for Buffer {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            let end = self.1 + s.len();
            self.0
                .get_mut(self.1..end)
                .ok_or(core::fmt::Error)?
                .copy_from_slice(s.as_bytes());
            self.1 = end;
            Ok(())
        }
    }
    let mut buffer = Buffer([0; 64], 0);
    write!(buffer, "{}", BivariateNormal::new(1.5).unwrap_err()).unwrap();
    let message = core::str::from_utf8(&buffer.0[..buffer.1]).unwrap();
    assert!(message.contains("correlation"), "{message}");
}

/// The panel rule has 16 nodes above `s = 0.095` and 15 at it and below.
#[test]
fn the_panel_rule_changes_just_above_its_threshold() {
    let at = panel_rule(0.095);
    let above = panel_rule(f64::from_bits(0.095_f64.to_bits() + 1));
    let nodes = |rule: &PanelRule| 2 * rule.w.len() + usize::from(rule.centre.is_some());
    assert_eq!(nodes(&at), 15);
    assert_eq!(nodes(&above), 16);
}

/// The paired batch reports each pair's own value and correlation's bound, across blocks.
#[test]
fn the_paired_batch_bounds_every_pair_across_blocks() {
    const N: usize = 200;
    const RHOS: [f64; 5] = [0.03, -0.5, 0.85, 0.97, -0.97];
    let rhos: [f64; N] = core::array::from_fn(|i| RHOS[i % 5]);
    let x: [f64; N] = core::array::from_fn(|i| 0.3 + i as f64 * 0.01);
    let y: [f64; N] = core::array::from_fn(|i| -0.4 + i as f64 * 0.005);
    let mut out = [BoundedProbability {
        value: 0.0,
        error: 0.0,
    }; N];
    bivariate_norm_cdf_bounded_slice(&x, &y, &rhos, &mut out);
    for i in 0..N {
        assert_eq!(out[i].error, absolute_error_bound(rhos[i]));
        assert_eq!(
            out[i].value.to_bits(),
            bivariate_norm_cdf(x[i], y[i], rhos[i]).to_bits()
        );
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
    let limits = [0.20, 0.29, 0.66, 0.75, 0.89, GENZ_CORRELATION_SPLIT];
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

/// `(x, y, rho, hi, lo)`: the exact probability is `hi + lo` (`hi` its nearest
/// binary64), from the Plackett angle integral at 45 digits. The first row is
/// the case on which the 20-node rule of the high branch erred by `2.58e-16`;
/// the others sit at the peak of that rule's truncation (`hk` near 0,
/// `bs` near `0.3 a^2`) for six correlations of both signs.
const HIGH_PEAK_ROWS: [(f64, f64, f64, f64, f64); 25] = [
    (
        -0.21101192279835226,
        -0.0014549743776884816,
        0.925,
        0.3876704315868698,
        -1.9616592491630367e-17,
    ),
    (
        -0.20811655388267403,
        0.0,
        0.925,
        0.38862410990278545,
        -2.9282061430886732e-18,
    ),
    (
        -0.14568158771787182,
        0.0006243496616480221,
        0.925,
        0.4050506705260554,
        2.471889548220608e-17,
    ),
    (
        -0.20811655388267403,
        0.0,
        -0.925,
        0.028944871103249024,
        -7.474807813567373e-20,
    ),
    (
        -0.14568158771787182,
        0.0006243496616480221,
        -0.925,
        0.037210417124143115,
        2.669367754496203e-18,
    ),
    (
        -0.20132063977645204,
        0.0,
        0.93,
        0.39229988705075464,
        -1.5726497963100065e-17,
    ),
    (
        -0.1409244478435164,
        0.0006039619193293561,
        0.93,
        0.408226201719964,
        -1.1958328435162889e-17,
    ),
    (
        -0.20132063977645204,
        0.0,
        -0.93,
        0.02792404531961158,
        1.3570084962644228e-18,
    ),
    (
        -0.1409244478435164,
        0.0006039619193293561,
        -0.93,
        0.035907616487057516,
        2.675801323220421e-18,
    ),
    (
        -0.18686893802876928,
        0.0,
        0.94,
        0.4001015616802987,
        1.8301367161405224e-17,
    ),
    (
        -0.13080825662013848,
        0.0005606068140863079,
        0.94,
        0.4149520780065759,
        1.2255730632086178e-17,
    ),
    (
        -0.18686893802876928,
        0.0,
        -0.94,
        0.025780135331868077,
        -7.398048704163813e-19,
    ),
    (
        -0.13080825662013848,
        0.0005606068140863079,
        -0.94,
        0.03316828982433925,
        -9.10612181072792e-19,
    ),
    (
        -0.16421084008067197,
        0.0,
        0.954,
        0.4122977931377612,
        2.2572317011902916e-17,
    ),
    (
        -0.11494758805647037,
        0.0004926325202420158,
        0.954,
        0.42543135529466247,
        1.883353644172071e-17,
    ),
    (
        -0.16421084008067197,
        0.0,
        -0.954,
        0.022484790760588267,
        1.1533744155028461e-18,
    ),
    (
        -0.11494758805647037,
        0.0004926325202420158,
        -0.954,
        0.02894982856080852,
        -4.817560791814889e-19,
    ),
    (
        -0.12049865144473604,
        0.0,
        0.9755,
        0.4357323136060003,
        -8.887333777394924e-18,
    ),
    (
        -0.08434905601131522,
        0.00036149595433420816,
        0.9755,
        0.4454652610153546,
        1.1045215697449183e-18,
    ),
    (
        -0.12049865144473604,
        0.0,
        -0.9755,
        0.016311760320838694,
        -9.835968180311198e-19,
    ),
    (
        -0.08434905601131522,
        0.00036149595433420816,
        -0.9755,
        0.021025349984488514,
        1.55924498106176e-18,
    ),
    (
        -0.05470374758643128,
        0.0,
        0.995,
        0.47085780859383164,
        2.6750567354771798e-17,
    ),
    (
        -0.03829262331050189,
        0.00016411124275929383,
        0.995,
        0.4753162323014182,
        1.3223054561440868e-17,
    ),
    (
        -0.05470374758643128,
        0.0,
        -0.995,
        0.007329433252832581,
        1.1423594707885076e-19,
    ),
    (
        -0.03829262331050189,
        0.00016411124275929383,
        -0.995,
        0.009456876353390143,
        1.9646190328222654e-19,
    ),
];

#[test]
fn high_correlation_peak_rows_meet_the_published_bound() {
    for (x, y, rho, hi, lo) in HIGH_PEAK_ROWS {
        let got = bivariate_norm_cdf(x, y, rho);
        // `got - hi` is exact (the two are within a factor of two).
        let error = (got - hi) - lo;
        assert!(
            error.abs() <= ABSOLUTE_ERROR_BOUND,
            "({x}, {y}, {rho}): {got} is {error:e} from the exact value"
        );
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

/// The tails' relative accuracy follows the rule's node count, so no rule has
/// fewer nodes than the canonical Genz implementation uses at the same
/// correlation: 6 below 0.3, 12 up to 0.75, 20 above (docs/bivariate_normal.md
/// section 4). Walked over every correlation of a fine grid and the doubles
/// next to each Genz threshold.
#[test]
fn no_rule_has_fewer_nodes_than_the_canonical_implementation() {
    let genz = |m: f64| {
        if m < 0.3 {
            6
        } else if m < 0.75 {
            12
        } else {
            20
        }
    };
    let edges = [0.3, 0.75]
        .into_iter()
        .flat_map(|e: f64| [e.next_down(), e, e.next_up()]);
    let rhos = (1..925).map(|i| f64::from(i) / 1000.0).chain(edges);
    for rho in rhos {
        for signed in [rho, -rho] {
            let (_, weights) = low_correlation_rule(signed);
            assert!(
                2 * weights.len() >= genz(rho),
                "{} nodes at {signed}, Genz uses {}",
                2 * weights.len(),
                genz(rho)
            );
        }
    }
}

/// The split exponent and the remainder correction are what bring the high branch's relative
/// error on the diagonal from `3e-15` (`P(-14, -14; 0.999)`) and `3e-11` (`P(-36, -36; 0.99)`) to
/// the values here; the references are 50-digit quadratures of Plackett's identity.
#[test]
fn the_high_branch_keeps_its_relative_accuracy_on_the_diagonal() {
    for &(x, rho, expected, tolerance) in &[
        (-14.0, 0.999, 5.868_397_061_334_767e-45, 2e-16),
        (-36.0, 0.99, 4.455_063_213_036_484e-286, 1e-14),
        (-25.0, 0.99, 2.319_854_744_485_69e-139, 5e-15),
        (-10.0, 0.99, 3.612_601_676_232_516e-24, 1e-15),
    ] {
        let got = bivariate_norm_cdf(x, x, rho);
        assert!(
            ((got - expected) / expected).abs() < tolerance,
            "P({x}, {x}; {rho}) = {got:e}, expected {expected:e}"
        );
    }
}
