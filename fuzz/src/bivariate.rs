//! The bivariate normal distribution against an independent MPFR evaluation of
//! Plackett's identity, and the contract in docs/bivariate_normal.md.
//!
//! The reference integrates from correlation -1, whose probability is closed
//! form, in the angle `t = asin(r)`:
//!
//! P(h, k; rho) = P(h, k; -1)
//!   + 1/(2 pi) int_{-pi/2}^{asin rho} exp(-(h² + k² - 2hk sin t) / (2 cos² t)) dt
//!
//! by tanh-sinh quadrature, split at the integrand's peak. The rule is refined
//! until two successive levels agree to [`TOLERANCE`]; an unresolved integral
//! fails explicitly.
use morphiq_numerics::{bivariate_normal as bvn, normal};
use rug::{Float, float::Constant};

const PRECISION: u32 = 128;
/// Successive quadrature levels must agree to 2^-73, about 1e-22.
const TOLERANCE: u32 = 73;
const LEVELS: u32 = 12;

fn value(x: f64) -> Float {
    Float::with_val(PRECISION, x)
}

fn cdf(x: &Float) -> Float {
    let argument: Float = -x.clone() / value(2.0).sqrt();
    argument.erfc() >> 1_u32
}

/// The integrand, zero where the angle's cosine vanishes.
fn integrand(h: &Float, k: &Float, t: &Float) -> Float {
    let (sin, cos) = t.clone().sin_cos(Float::new(PRECISION));
    let square: Float = Float::with_val(PRECISION, cos.square_ref());
    if square.is_zero() {
        return value(0.0);
    }
    // h² + k² - 2hk s = (h - ks)² + k² cos² t, which does not cancel.
    let product: Float = Float::with_val(PRECISION, k * &sin);
    let difference: Float = Float::with_val(PRECISION, h - &product);
    let numerator: Float = difference.square();
    let twice: Float = square * 2_u32;
    let half_k: Float = Float::with_val(PRECISION, k.square_ref()) >> 1_u32;
    let exponent: Float = -(numerator / twice + half_k);
    exponent.exp()
}

/// Tanh-sinh quadrature of `f` over `[a, b]`.
fn integrate(f: impl Fn(&Float) -> Float, a: &Float, b: &Float) -> Float {
    let half: Float = Float::with_val(PRECISION, b - a) >> 1_u32;
    if half.is_zero() {
        return value(0.0);
    }
    let middle: Float = Float::with_val(PRECISION, a + b) >> 1_u32;
    let half_pi: Float = Float::with_val(PRECISION, Constant::Pi) >> 1_u32;
    // The weighted contribution at abscissa u and, if u > 0, at -u.
    let node = |u: &Float| -> Option<Float> {
        let (sinh, cosh) = u.clone().sinh_cosh(Float::new(PRECISION));
        let s: Float = Float::with_val(PRECISION, &half_pi * &sinh);
        let c = s.clone().cosh();
        let weight: Float = Float::with_val(PRECISION, &half_pi * &cosh) / c.square();
        // Nodes whose weights fall below the tolerance end the sum.
        if weight < (value(1.0) >> 100_u32) {
            return None;
        }
        let x = s.tanh();
        let offset: Float = Float::with_val(PRECISION, &half * &x);
        let mut sum = f(&Float::with_val(PRECISION, &middle + &offset));
        if !u.is_zero() {
            sum += f(&Float::with_val(PRECISION, &middle - &offset));
        }
        Some(sum * weight)
    };
    let mut total = node(&value(0.0)).expect("central node");
    let mut previous: Option<Float> = None;
    for level in 0..=LEVELS {
        let step: Float = value(1.0) >> level;
        // Level 0 takes every multiple of the step; later levels only the odd.
        let mut index = 1_u32;
        loop {
            let u: Float = Float::with_val(PRECISION, &step * index);
            match node(&u) {
                Some(term) => total += term,
                None => break,
            }
            index += if level == 0 { 1 } else { 2 };
        }
        let estimate: Float = Float::with_val(PRECISION, &total * &step) * &half;
        if let Some(previous) = previous
            && level >= 3
        {
            let change: Float = Float::with_val(PRECISION, &estimate - &previous).abs();
            if change <= (value(1.0) >> TOLERANCE) {
                return estimate;
            }
        }
        previous = Some(estimate);
    }
    panic!("bivariate oracle unresolved on [{a}, {b}]: last estimate {previous:?}");
}

/// P(h, k; rho) for finite thresholds of magnitude below 39.
fn reference(h: f64, k: f64, rho: f64) -> Float {
    let (x, y) = (value(h), value(k));
    if rho == 1.0 {
        return cdf(&x.min(&y));
    }
    let countermonotone = {
        let difference: Float = cdf(&x) - cdf(&-y.clone());
        difference.max(&value(0.0))
    };
    if rho == -1.0 {
        return countermonotone;
    }
    // Above h + k = 0 the survival identity keeps the integrand's side:
    // P(h, k) = 1 - Phi(-h) - Phi(-k) + P(-h, -k).
    if h + k > 0.0 {
        let mut total = value(1.0);
        total -= cdf(&-x);
        total -= cdf(&-y);
        return total + reference(-h, -k, rho);
    }
    let start: Float = -(Float::with_val(PRECISION, Constant::Pi) >> 1_u32);
    let end = value(rho).asin();
    // The exponent is largest where sin t is the smaller threshold ratio.
    let ratio = if h.abs() < k.abs() { h / k } else { k / h };
    let mut cuts = vec![start.clone()];
    if ratio.is_finite() && ratio.abs() <= 1.0 {
        let peak = value(ratio).asin();
        if peak > start && peak < end {
            cuts.push(peak);
        }
    }
    cuts.push(end);
    let mut sum = value(0.0);
    for pair in cuts.windows(2) {
        sum += integrate(|t| integrand(&x, &y, t), &pair[0], &pair[1]);
    }
    let two_pi: Float = Float::with_val(PRECISION, Constant::Pi) * 2_u32;
    sum / two_pi + countermonotone
}

/// The published allowance for a correlation: section 6's bounds, rounded up in
/// the fourth digit as that section says `absolute_error_bound` returns them.
fn allowance(rho: f64) -> f64 {
    let a = rho.abs();
    if a == 1.0 || a < f64::EPSILON {
        1.7e-16
    } else if a >= 0.925 {
        if rho > 0.0 { 2.709e-16 } else { 3.334e-16 }
    } else {
        [
            (0.20, 2.071e-16),
            (0.29, 2.311e-16),
            (0.66, 2.761e-16),
            (0.75, 2.951e-16),
            (0.89, 3.481e-16),
            (0.925, 3.721e-16),
        ]
        .into_iter()
        .find(|&(limit, _)| a < limit)
        .expect("low-correlation band")
        .1
    }
}

fn check_accuracy(actual: f64, expected: &Float, bound: f64) {
    let error: Float = Float::with_val(PRECISION, actual - expected).abs();
    // The reference's own error is far below this slack.
    let slack: Float = value(1.0) >> 70_u32;
    assert!(
        error <= Float::with_val(PRECISION, bound) + slack,
        "bivariate bound violation: got {actual:e}, expected {expected}, bound {bound:e}"
    );
}

fn check(x: f64, y: f64, rho: f64) {
    let result = bvn::bivariate_norm_cdf(x, y, rho);
    let bounded = bvn::bivariate_norm_cdf_bounded(x, y, rho);
    let name = format!(
        "x={:016x} y={:016x} rho={:016x}",
        x.to_bits(),
        y.to_bits(),
        rho.to_bits()
    );
    assert_eq!(
        bvn::bivariate_norm_cdf(y, x, rho).to_bits(),
        result.to_bits(),
        "symmetry {name}"
    );
    let admitted = !rho.is_nan() && rho.abs() <= 1.0;
    match bvn::BivariateNormal::new(rho) {
        Ok(evaluator) => {
            assert!(admitted && evaluator.correlation().to_bits() == rho.to_bits());
            assert_eq!(
                evaluator.cdf(x, y).to_bits(),
                result.to_bits(),
                "evaluator {name}"
            );
            let repeated = evaluator.cdf_bounded(x, y);
            assert_eq!(
                format!("{repeated:?}"),
                format!("{bounded:?}"),
                "bounded {name}"
            );
        }
        Err(_) => assert!(!admitted),
    }
    if x.is_nan() || y.is_nan() || !admitted {
        assert!(result.is_nan() && bounded.error.is_nan(), "NaN {name}");
        return;
    }
    assert!(
        (0.0..=1.0).contains(&result) && !result.is_sign_negative(),
        "range {name}"
    );
    assert_eq!(
        bounded.value.to_bits(),
        result.to_bits(),
        "bounded value {name}"
    );
    assert!(
        bounded.error >= 0.0 && bounded.error <= allowance(rho).max(5.7e-17),
        "reported bound {name}: {:e}",
        bounded.error
    );
    if x <= -39.0 || y <= -39.0 {
        assert_eq!(result.to_bits(), 0, "lower saturation {name}");
    } else if x >= 39.0 || y >= 39.0 {
        let expected = if x >= 39.0 && y >= 39.0 {
            1.0
        } else {
            normal::norm_cdf(x.min(y))
        };
        assert_eq!(
            result.to_bits(),
            expected.to_bits(),
            "upper saturation {name}"
        );
    } else {
        check_accuracy(result, &reference(x, y, rho), allowance(rho));
    }
}

/// Byte 0 shapes up to eight triples of little-endian encodings `(x, y, rho)`:
/// as given, or folded into the finite thresholds and valid correlations.
pub fn check_input(data: &[u8]) {
    let Some((&shape, data)) = data.split_first() else {
        return;
    };
    let triples: Vec<[f64; 3]> = data
        .as_chunks::<24>()
        .0
        .iter()
        .take(8)
        .map(|t| {
            let word = |i: usize| u64::from_le_bytes(t[8 * i..8 * i + 8].try_into().unwrap());
            if shape % 3 == 0 {
                [0, 1, 2].map(|i| f64::from_bits(word(i)))
            } else {
                // Thresholds in [-40, 40]; correlations across [-1, 1], or
                // within 2^-3 of an end.
                let unit = |w: u64| (w >> 11) as f64 / (1_u64 << 53) as f64;
                let threshold = |w| unit(w) * 80.0 - 40.0;
                let w = word(2);
                let rho = if shape % 3 == 1 {
                    unit(w) * 2.0 - 1.0
                } else {
                    let near = 1.0 - unit(w) * unit(w) * 0.125;
                    if w & 1 == 0 { near } else { -near }
                };
                let x = threshold(word(0));
                let y = if shape / 3 % 2 == 1 {
                    // Nearly equal or opposite thresholds sharpen the integrand.
                    let offset = unit(word(1)) * 0.01;
                    if w & 2 == 0 { x + offset } else { -x + offset }
                } else {
                    threshold(word(1))
                };
                [x, y, rho]
            }
        })
        .collect();
    for &[x, y, rho] in &triples {
        check(x, y, rho);
    }
    let [xs, ys, rhos] = [0, 1, 2].map(|i| triples.iter().map(|t| t[i]).collect::<Vec<_>>());
    let mut out = vec![0.0; triples.len()];
    bvn::bivariate_norm_cdf_slice(&xs, &ys, &rhos, &mut out);
    for (t, got) in triples.iter().zip(&out) {
        assert_eq!(
            got.to_bits(),
            bvn::bivariate_norm_cdf(t[0], t[1], t[2]).to_bits(),
            "slice"
        );
    }
    let blank = bvn::bivariate_norm_cdf_bounded(f64::NAN, 0.0, 0.0);
    let mut bounded = vec![blank; triples.len()];
    bvn::bivariate_norm_cdf_bounded_slice(&xs, &ys, &rhos, &mut bounded);
    for (t, got) in triples.iter().zip(&bounded) {
        let want = bvn::bivariate_norm_cdf_bounded(t[0], t[1], t[2]);
        assert_eq!(format!("{got:?}"), format!("{want:?}"), "bounded slice");
    }
    if let Some(&[_, _, rho]) = triples.first()
        && let Ok(evaluator) = bvn::BivariateNormal::new(rho)
    {
        assert_eq!(
            evaluator.absolute_error_bound().to_bits(),
            bvn::absolute_error_bound(rho).to_bits()
        );
        evaluator.cdf_bounded_slice(&xs, &ys, &mut bounded);
        for (t, got) in triples.iter().zip(&bounded) {
            let want = evaluator.cdf_bounded(t[0], t[1]);
            assert_eq!(
                format!("{got:?}"),
                format!("{want:?}"),
                "evaluator bounded slice"
            );
        }
        evaluator.cdf_slice(&xs, &ys, &mut out);
        for (t, got) in triples.iter().zip(&out) {
            assert_eq!(
                got.to_bits(),
                evaluator.cdf(t[0], t[1]).to_bits(),
                "evaluator slice"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_reference_matches_closed_forms() {
        // At the origin P = 1/4 + asin(rho) / (2 pi), for every correlation.
        for rho in [-0.999999, -0.93, -0.5, 0.0, 0.3, 0.925, 0.999999] {
            let two_pi: Float = Float::with_val(PRECISION, Constant::Pi) * 2_u32;
            let exact: Float = value(rho).asin() / two_pi + value(0.25);
            let error: Float = Float::with_val(PRECISION, reference(0.0, 0.0, rho) - exact).abs();
            assert!(error < value(1.0) >> 70_u32, "rho {rho}: {error}");
        }
        // Independence factorizes.
        for (h, k) in [(-6.0, -6.0), (1.5, -2.0), (3.0, 4.0)] {
            let product: Float = cdf(&value(h)) * cdf(&value(k));
            let error: Float = Float::with_val(PRECISION, reference(h, k, 0.0) - product).abs();
            assert!(error < value(1.0) >> 70_u32, "({h}, {k}): {error}");
        }
    }

    #[test]
    fn regime_limits_and_special_values_satisfy_the_contract() {
        let correlations = [
            -1.0,
            -0.9999999,
            -0.925,
            -0.924,
            -0.5,
            -1.0e-17,
            0.0,
            0.199,
            0.29,
            0.66,
            0.75,
            0.89,
            0.925,
            0.999999999,
            1.0,
        ];
        for rho in correlations {
            for (x, y) in [
                (0.0, 0.0),
                (-6.0, -6.0),
                (-0.21101192279835226, -0.0014549743776884816),
                (2.0, -2.0),
                (-38.0, -30.0),
                (40.0, 1.0),
                (f64::NEG_INFINITY, 1.0),
                (f64::INFINITY, f64::INFINITY),
                (f64::NAN, 0.0),
            ] {
                check(x, y, rho);
            }
        }
        check(0.0, 0.0, 1.5);
        check(0.0, 0.0, f64::NAN);
    }

    #[test]
    fn the_accuracy_check_rejects_an_excess_error() {
        let expected = reference(0.5, -0.25, 0.4);
        let near = expected.to_f64();
        check_accuracy(near, &expected, 2.761e-16);
        assert!(
            std::panic::catch_unwind(|| check_accuracy(near + 1.0e-15, &expected, 2.761e-16))
                .is_err()
        );
    }

    #[test]
    fn shaped_packets_cover_sharp_integrands() {
        for shape in 0..6_u8 {
            let mut data = vec![shape];
            for i in 1..=24_u64 {
                data.extend_from_slice(&i.wrapping_mul(0x9e37_79b9_7f4a_7c15).to_le_bytes());
            }
            check_input(&data);
        }
    }
}
