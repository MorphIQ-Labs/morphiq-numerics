//! The bivariate normal distribution function.
//!
//! `bivariate_norm_cdf(x, y, rho)` is `P(X <= x, Y <= y)` for a standard
//! normal pair with correlation `rho`, and [`BivariateNormal`] evaluates it
//! repeatedly at one correlation, reusing the work that depends on `rho` alone.
//! The derivation, the error budget and what is and is not proved are in
//! `docs/bivariate_normal.md`.
//!
//! The contract is an absolute error bound, not correct rounding: the result
//! is within [`ABSOLUTE_ERROR_BOUND`] of the exact probability, and
//! [`BoundedProbability`] carries that bound with the value. A relative
//! guarantee is not made below [`RELATIVE_FLOOR`]; a caller that divides by a
//! small probability must carry the absolute bound itself.

use crate::eft::{two_prod, two_sum};
use crate::elementary::{asin, exp, sin, sqrt};
use crate::normal::norm_cdf;
use core::f64::consts::TAU;

#[cfg(feature = "simd")]
mod lanes;
mod tables;
use tables::{
    GL4_W, GL4_X, GL6_W, GL6_X, GL8_W, GL8_X, GL10_W, GL10_X, GL12_W, GL12_X, GL14_W, GL14_X,
    GL16_W, GL16_X, GL20_W, GL20_X, GL24_W, GL24_X,
};

#[cfg(test)]
mod tests;

/// The bound on `|result - exact|` that every finite evaluation meets.
pub const ABSOLUTE_ERROR_BOUND: f64 = 2.5e-16;

/// A result at or above this value is also accurate relative to itself, to
/// [`RELATIVE_ERROR_BOUND`]; below it only the absolute bound holds.
pub const RELATIVE_FLOOR: f64 = 1.0e-3;

/// The relative error of a result at or above [`RELATIVE_FLOOR`].
pub const RELATIVE_ERROR_BOUND: f64 = 1.0e-13;

/// `|rho|` at which the low-correlation quadrature gives way to the
/// high-correlation series (Genz's value; `docs/bivariate_normal.md` section 4).
const GENZ_CORRELATION_SPLIT: f64 = 0.925;

/// Beyond `|x| = 39` the standard normal CDF is exactly 0 or 1 in binary64
/// (`Phi(-39)` is about `1.4e-333`, below half the least subnormal), so the
/// result there is the limit and both quadratures would form `inf * 0`.
const SATURATED_THRESHOLD: f64 = 39.0;

/// `sqrt(2 pi)` rounded to nearest.
const SQRT_TAU: f64 = f64::from_bits(0x4004_0d93_1ff6_2706);

/// A product of the two distribution functions at or above this has an exact
/// `two_prod` error term (the exactness domain is `2^-969`).
const PRODUCT_EXACT_FLOOR: f64 = 1.0e-270;

/// The largest rule, and so the length of the per-correlation tables.
const MAX_NODES: usize = 24;

/// A probability with a bound on its absolute error.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BoundedProbability {
    /// The probability, in `[0, 1]`, or NaN for a NaN or out-of-range input.
    pub value: f64,
    /// A bound on `|value - P|`, or NaN with a NaN value.
    pub error: f64,
}

/// The correlation was NaN or outside `[-1, 1]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidCorrelation;

impl core::fmt::Display for InvalidCorrelation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("the correlation must lie in [-1, 1]")
    }
}

/// Which closed form or quadrature a correlation selects. One classifier
/// serves the one-shot functions and [`BivariateNormal`], so the reusable
/// evaluator cannot select a different regime than the one-shot path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Regime {
    Independent,
    Comonotone,
    Countermonotone,
    Low,
    High,
}

impl Regime {
    /// `None` for NaN or `|rho| > 1`.
    fn of(rho: f64) -> Option<Self> {
        if rho.is_nan() || rho.abs() > 1.0 {
            None
        } else if rho.abs() < f64::EPSILON {
            Some(Regime::Independent)
        } else if rho == 1.0 {
            // Only the exact endpoints are degenerate: at `1 - EPSILON` the pair
            // still smooths over `sqrt(2 EPSILON)`, and snapping it to the limit
            // would miss results near `x = y` by about 1e-9.
            Some(Regime::Comonotone)
        } else if rho == -1.0 {
            Some(Regime::Countermonotone)
        } else if rho.abs() < GENZ_CORRELATION_SPLIT {
            Some(Regime::Low)
        } else {
            Some(Regime::High)
        }
    }
}

/// The least rule whose proved Bernstein-ellipse truncation bound is at or
/// below `2e-17` for `|rho|` up to its limit (`docs/bivariate_normal.md`
/// section 4, `docs/bivariate_normal_truncation.md`).
fn low_correlation_rule(rho: f64) -> (&'static [f64], &'static [f64]) {
    let m = rho.abs();
    if m <= 0.055 {
        (&GL4_X, &GL4_W)
    } else if m <= 0.20 {
        (&GL6_X, &GL6_W)
    } else if m <= 0.38 {
        (&GL8_X, &GL8_W)
    } else if m <= 0.54 {
        (&GL10_X, &GL10_W)
    } else if m <= 0.66 {
        (&GL12_X, &GL12_W)
    } else if m <= 0.75 {
        (&GL14_X, &GL14_W)
    } else if m <= 0.81 {
        (&GL16_X, &GL16_W)
    } else if m <= 0.89 {
        (&GL20_X, &GL20_W)
    } else {
        (&GL24_X, &GL24_W)
    }
}

/// A bivariate normal distribution function at one correlation, with the
/// `rho`-dependent quadrature table built once.
///
/// [`Self::cdf`] performs the same arithmetic as [`bivariate_norm_cdf`] at the
/// same correlation: the one-shot function builds this table and evaluates it,
/// so the two are bit-identical by construction.
#[derive(Clone, Copy, Debug)]
pub struct BivariateNormal {
    rho: f64,
    regime: Regime,
    nodes: usize,
    /// `asin(rho)`, the quadrature's angular range.
    asr: f64,
    kw: [f64; MAX_NODES],
    /// `1 / (4 (1 - sin theta))` of each node's angle `theta`.
    p: [f64; MAX_NODES],
    /// `1 / (4 (1 + sin theta))`.
    q: [f64; MAX_NODES],
}

impl BivariateNormal {
    /// Build the table for `rho`, or `Err` if `rho` is NaN or outside `[-1, 1]`.
    ///
    /// The cost is one `asin` and `n` `sincos` evaluations for the `n`-node
    /// rule of the low-correlation regime, and nothing for the others.
    pub fn new(rho: f64) -> Result<Self, InvalidCorrelation> {
        let regime = Regime::of(rho).ok_or(InvalidCorrelation)?;
        let mut table = BivariateNormal {
            rho,
            regime,
            nodes: 0,
            asr: 0.0,
            kw: [0.0; MAX_NODES],
            p: [0.25; MAX_NODES],
            q: [0.25; MAX_NODES],
        };
        if regime == Regime::Low {
            let asr = asin(rho);
            let (abscissas, weights) = low_correlation_rule(rho);
            let k = asr / (2.0 * TAU);
            table.asr = asr;
            table.nodes = 2 * abscissas.len();
            for i in 0..abscissas.len() {
                for (slot, sign) in [(2 * i, 1.0_f64), (2 * i + 1, -1.0)] {
                    let s = sin(asr * (sign * abscissas[i] + 1.0) / 2.0);
                    table.kw[slot] = weights[i] * k;
                    table.p[slot] = 0.25 / (1.0 - s);
                    table.q[slot] = 0.25 / (1.0 + s);
                }
            }
        }
        Ok(table)
    }

    /// The correlation this table was built for.
    #[must_use]
    pub const fn correlation(&self) -> f64 {
        self.rho
    }

    /// `P(X <= x, Y <= y)` at this table's correlation.
    ///
    /// NaN for a NaN argument. Infinite arguments give the exact limit.
    /// Symmetric in `x` and `y` by construction: the arguments are ordered
    /// before any arithmetic.
    #[must_use]
    pub fn cdf(&self, x: f64, y: f64) -> f64 {
        let (x, y) = if x <= y { (x, y) } else { (y, x) };
        if let Some(limit) = degenerate_limit(x, y) {
            return limit;
        }
        match self.regime {
            Regime::Independent => norm_cdf(x) * norm_cdf(y),
            Regime::Comonotone => norm_cdf(x),
            // `P(X <= x, Y <= y)` at `rho = -1` is `max(0, Phi(x) + Phi(y) - 1)`,
            // written as `Phi(x) - Phi(-y)` so a small result keeps its digits.
            Regime::Countermonotone => (norm_cdf(x) - norm_cdf(-y)).max(0.0),
            Regime::Low => self.low(x, y),
            Regime::High => high_correlation(-x, -y, self.rho),
        }
    }

    /// [`Self::cdf`] with its absolute error bound.
    ///
    /// The bound is [`ABSOLUTE_ERROR_BOUND`] everywhere, and
    /// `RELATIVE_ERROR_BOUND * value` where that is smaller, which holds for a
    /// result at or above [`RELATIVE_FLOOR`]. The closed-form regimes
    /// (independent, comonotone, countermonotone) are within a few units in the
    /// last place of the exact value, which the same bound covers.
    #[must_use]
    pub fn cdf_bounded(&self, x: f64, y: f64) -> BoundedProbability {
        bounded(self.cdf(x, y))
    }

    /// [`Self::cdf`] of every pair `(x[i], y[i])`, written to `out`:
    /// `out[i]` is `self.cdf(x[i], y[i])`, bit for bit, on every target and
    /// with or without the `simd` feature.
    ///
    /// With `simd` the pairs are evaluated in SIMD lanes when the correlation
    /// selects the low-correlation quadrature, each lane performing the
    /// scalar operation sequence; a high-correlation or closed-form
    /// correlation, a NaN or saturated pair is the scalar function's, per lane
    /// (`docs/bivariate_normal.md` section 12).
    ///
    /// # Panics
    ///
    /// If `x`, `y` and `out` don't have the same length.
    pub fn cdf_slice(&self, x: &[f64], y: &[f64], out: &mut [f64]) {
        assert!(
            x.len() == y.len() && y.len() == out.len(),
            "cdf_slice: slices of different lengths"
        );
        #[cfg(feature = "simd")]
        lanes::map(x, y, lanes::Correlations::One(self), out);
        #[cfg(not(feature = "simd"))]
        for ((o, &x), &y) in out.iter_mut().zip(x).zip(y) {
            *o = self.cdf(x, y);
        }
    }

    /// [`Self::cdf_bounded`] of every pair `(x[i], y[i])`, written to `out`,
    /// bit for bit; the values are [`Self::cdf_slice`]'s.
    ///
    /// # Panics
    ///
    /// If `x`, `y` and `out` don't have the same length.
    pub fn cdf_bounded_slice(&self, x: &[f64], y: &[f64], out: &mut [BoundedProbability]) {
        assert!(
            x.len() == y.len() && y.len() == out.len(),
            "cdf_bounded_slice: slices of different lengths"
        );
        bounded_in_blocks(x, y, out, |_, x, y, values| self.cdf_slice(x, y, values));
    }

    /// The Genz low-correlation quadrature for ordered `x <= y`:
    /// `Phi(x) Phi(y) + sum_i kw_i exp(-(d p_i + m q_i))`, `d = (x - y)^2`,
    /// `m = (x + y)^2`, with `kw_i = w_i asr / (4 pi)` over the rule's nodes in
    /// node order. `d p_i + m q_i` is the exponent `(x^2 + y^2 - 2 x y sin t_i) /
    /// (2 cos^2 t_i)` written as a sum of two non-negative terms, so it carries no
    /// cancellation. The terms are accumulated as a double-word, the product of the
    /// two distribution functions is kept as a double-word, and the two are summed
    /// without rounding until the one final addition, so the result is rounded once
    /// (`docs/bivariate_normal_budget.md`).
    fn low(&self, x: f64, y: f64) -> f64 {
        let e1 = x - y;
        let d = e1 * e1;
        let e2 = x + y;
        let m = e2 * e2;
        let (mut high, mut low) = (0.0, 0.0);
        for i in 0..self.nodes {
            let term = self.kw[i] * exp(-(d * self.p[i] + m * self.q[i]));
            let (s, e) = two_sum(high, term);
            high = s;
            low += e;
        }
        let (hi, lo) = two_prod(norm_cdf(x), norm_cdf(y));
        // `two_prod` is exact for products of at least 2^-969; a smaller product is
        // below 2^-900 and its rounding error is irrelevant.
        let lo = if hi >= PRODUCT_EXACT_FLOOR { lo } else { 0.0 };
        let (sum, err) = two_sum(hi, high);
        clamp_to_probability(sum + (err + (low + lo)))
    }
}

/// NaN for a NaN input, else the exact limit at a saturated threshold, for
/// ordered `x <= y`.
fn degenerate_limit(x: f64, y: f64) -> Option<f64> {
    if x.is_nan() || y.is_nan() {
        Some(f64::NAN)
    } else if x <= -SATURATED_THRESHOLD {
        Some(0.0)
    } else if y >= SATURATED_THRESHOLD {
        Some(norm_cdf(x))
    } else {
        None
    }
}

/// A probability is in `[0, 1]`; a cancelled sum can land a rounding step
/// outside it, and the clamp is honest because the result is only claimed
/// to the absolute bound there.
fn clamp_to_probability(value: f64) -> f64 {
    if value.is_nan() {
        value
    } else {
        value.clamp(0.0, 1.0)
    }
}

/// `P(X <= x, Y <= y)` for a standard bivariate normal pair with correlation
/// `rho`, within [`ABSOLUTE_ERROR_BOUND`] of the exact probability.
///
/// NaN if `rho` is NaN or outside `[-1, 1]`, or if an argument is NaN.
///
/// ```
/// use morphiq_numerics::bivariate_normal::bivariate_norm_cdf;
/// use morphiq_numerics::normal::norm_cdf;
///
/// // At zero correlation the pair is independent.
/// assert_eq!(bivariate_norm_cdf(0.0, 0.0, 0.0), norm_cdf(0.0) * norm_cdf(0.0));
/// ```
#[must_use]
pub fn bivariate_norm_cdf(x: f64, y: f64, rho: f64) -> f64 {
    match BivariateNormal::new(rho) {
        Ok(table) => table.cdf(x, y),
        Err(InvalidCorrelation) => f64::NAN,
    }
}

/// [`bivariate_norm_cdf`] with its absolute error bound; both fields are NaN
/// for an invalid correlation or a NaN argument.
#[must_use]
pub fn bivariate_norm_cdf_bounded(x: f64, y: f64, rho: f64) -> BoundedProbability {
    match BivariateNormal::new(rho) {
        Ok(table) => table.cdf_bounded(x, y),
        Err(InvalidCorrelation) => BoundedProbability {
            value: f64::NAN,
            error: f64::NAN,
        },
    }
}

/// [`BivariateNormal::cdf_bounded`]'s bound for a value.
fn bounded(value: f64) -> BoundedProbability {
    if value.is_nan() {
        return BoundedProbability {
            value,
            error: f64::NAN,
        };
    }
    let error = if value >= RELATIVE_FLOOR {
        (RELATIVE_ERROR_BOUND * value).min(ABSOLUTE_ERROR_BOUND)
    } else {
        ABSOLUTE_ERROR_BOUND
    };
    BoundedProbability { value, error }
}

/// Fill `out` with the bound of each value `fill` writes for the pairs,
/// in blocks, so the bounded form needs no allocation.
fn bounded_in_blocks(
    x: &[f64],
    y: &[f64],
    out: &mut [BoundedProbability],
    fill: impl Fn(usize, &[f64], &[f64], &mut [f64]),
) {
    const BLOCK: usize = 64;
    let mut values = [0.0; BLOCK];
    for (block, ((x, y), out)) in x
        .chunks(BLOCK)
        .zip(y.chunks(BLOCK))
        .zip(out.chunks_mut(BLOCK))
        .enumerate()
    {
        let values = &mut values[..x.len()];
        fill(block * BLOCK, x, y, values);
        for (o, &v) in out.iter_mut().zip(values.iter()) {
            *o = bounded(v);
        }
    }
}

/// [`bivariate_norm_cdf`] of every triple `(x[i], y[i], rho[i])`, written to
/// `out`: `out[i]` is `bivariate_norm_cdf(x[i], y[i], rho[i])`, bit for bit,
/// on every target and with or without the `simd` feature. NaN where the
/// correlation is invalid.
///
/// With `simd` the triples are evaluated in SIMD lanes, a lane at its own
/// correlation, so a batch may mix regimes and rule lengths; a lane the
/// screen doesn't admit is the scalar function's
/// (`docs/bivariate_normal.md` section 12).
///
/// # Panics
///
/// If `x`, `y`, `rho` and `out` don't have the same length.
pub fn bivariate_norm_cdf_slice(x: &[f64], y: &[f64], rho: &[f64], out: &mut [f64]) {
    assert!(
        x.len() == y.len() && y.len() == rho.len() && rho.len() == out.len(),
        "bivariate_norm_cdf_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    lanes::map(x, y, lanes::Correlations::Each(rho), out);
    #[cfg(not(feature = "simd"))]
    for (((o, &x), &y), &rho) in out.iter_mut().zip(x).zip(y).zip(rho) {
        *o = bivariate_norm_cdf(x, y, rho);
    }
}

/// [`bivariate_norm_cdf_bounded`] of every triple `(x[i], y[i], rho[i])`,
/// written to `out`, bit for bit; the values are
/// [`bivariate_norm_cdf_slice`]'s.
///
/// # Panics
///
/// If `x`, `y`, `rho` and `out` don't have the same length.
pub fn bivariate_norm_cdf_bounded_slice(
    x: &[f64],
    y: &[f64],
    rho: &[f64],
    out: &mut [BoundedProbability],
) {
    assert!(
        x.len() == y.len() && y.len() == rho.len() && rho.len() == out.len(),
        "bivariate_norm_cdf_bounded_slice: slices of different lengths"
    );
    bounded_in_blocks(x, y, out, |start, x, y, values| {
        bivariate_norm_cdf_slice(x, y, &rho[start..start + x.len()], values);
    });
}

/// Genz's upper-tail high-correlation algorithm (BVND, `|rho| >= 0.925`), in
/// his variable names so the transcription can be checked line by line.
/// `dh` and `dk` are the negated thresholds, `P(X >= dh, Y >= dk)`.
fn high_correlation(dh: f64, dk: f64, rho: f64) -> f64 {
    // Genz reflects `k` and `hk` together for negative correlation.
    let (k, hk) = if rho < 0.0 {
        (-dk, -(dh * dk))
    } else {
        (dk, dh * dk)
    };
    let ass = (1.0 - rho.abs()) * (1.0 + rho.abs());
    let mut a = sqrt(ass);
    let bs = (dh - k) * (dh - k);
    let c = (4.0 - hk) / 8.0;
    let d = (12.0 - hk) / 16.0;
    let asr = -(bs / ass + hk) / 2.0;

    let mut bvn = if asr > -100.0 {
        a * exp(asr) * (1.0 - c * (bs - ass) * (1.0 - d * bs / 5.0) / 3.0 + c * d * ass * ass / 5.0)
    } else {
        0.0
    };

    if -hk < 100.0 {
        let b = sqrt(bs);
        bvn -= exp(-hk / 2.0)
            * SQRT_TAU
            * norm_cdf(-b / a)
            * b
            * (1.0 - c * bs * (1.0 - d * bs / 5.0) / 3.0);
    }

    a /= 2.0;
    for i in 0..GL20_X.len() {
        for sign in [1.0_f64, -1.0] {
            let x = a * (sign * GL20_X[i] + 1.0);
            let xs = x * x;
            let asr = -(bs / xs + hk) / 2.0;
            if asr > -100.0 {
                let rs = sqrt(1.0 - xs);
                let one_plus_rs = 1.0 + rs;
                bvn += a
                    * GL20_W[i]
                    * exp(asr)
                    * (exp(-hk * xs / (2.0 * one_plus_rs * one_plus_rs)) / rs
                        - (1.0 + c * xs * (1.0 + d * xs)));
            }
        }
    }

    bvn = -bvn / TAU;
    let result = if rho > 0.0 {
        bvn + norm_cdf(-dh.max(dk))
    } else {
        -bvn + (norm_cdf(-dh) - norm_cdf(dk)).max(0.0)
    };
    clamp_to_probability(result)
}
