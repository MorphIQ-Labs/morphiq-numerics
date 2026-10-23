//! The bivariate normal distribution function.
//!
//! `bivariate_norm_cdf(x, y, rho)` is `P(X <= x, Y <= y)` for a standard
//! normal pair with correlation `rho`, and [`BivariateNormal`] evaluates it
//! repeatedly at one correlation, reusing the work that depends on `rho` alone.
//! The derivation, the error budget and what is and is not proved are in
//! `docs/bivariate_normal.md`.
//!
//! The contract is an absolute error bound, not correct rounding: the result
//! is within [`absolute_error_bound`]`(rho)` of the exact probability, which is
//! at most [`ABSOLUTE_ERROR_BOUND`], and [`BoundedProbability`] carries that
//! bound with the value. No relative guarantee is made: a caller that divides
//! by a small probability must carry the absolute bound itself, and refuse the
//! quotient where the bound is not far below the value.

use crate::eft::{two_prod, two_sum};
use crate::elementary::sqrt;
#[cfg(not(test))]
use crate::elementary::{asin, exp, sin};
#[cfg(not(test))]
use crate::normal::norm_cdf;
use core::f64::consts::TAU;
#[cfg(test)]
use trace::{asin, exp, norm_cdf, sin};

#[cfg(feature = "simd")]
mod lanes;
mod tables;
use tables::{
    GL4_W, GL4_X, GL6_W, GL6_X, GL8_W, GL8_X, GL10_W, GL10_X, GL12_W, GL12_X, GL14_W, GL14_X,
    GL15_W, GL15_W0, GL15_XM, GL15_XP, GL16_W, GL16_X, GL16_XM, GL16_XP, GL20_W, GL20_X, GL24_W,
    GL24_X,
};

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(crate) mod trace;

/// The bound on `|result - exact|` that every finite evaluation meets, at any
/// correlation: the largest of [`absolute_error_bound`]'s values.
pub const ABSOLUTE_ERROR_BOUND: f64 = 3.721e-16;

/// The proved bound of each low-correlation rule, indexed like
/// [`LOW_RULE_LIMITS`]: `190, 207, 231, 257, 276, 295, 309, 348, 372` times
/// `1e-18` (`formal/bivariate/BvnBudget.v`, `low_4` to `low_24`), each rounded
/// up in the fourth digit.
const LOW_RULE_BOUNDS: [f64; 9] = [
    1.901e-16, 2.071e-16, 2.311e-16, 2.571e-16, 2.761e-16, 2.951e-16, 3.091e-16, 3.481e-16,
    3.721e-16,
];

/// The largest `|rho|` each low-correlation rule serves; the last rule serves up
/// to the Genz split.
const LOW_RULE_LIMITS: [f64; 8] = [0.055, 0.20, 0.38, 0.54, 0.66, 0.75, 0.81, 0.89];

/// The bound of the closed-form regimes: the independent product
/// `Phi(x) Phi(y)` and the countermonotone difference carry two `norm_cdf`
/// errors and one rounding, `3 * 2^-54` plus the contract's `2^-112` terms.
const CLOSED_FORM_BOUND: f64 = 1.7e-16;

/// The comonotone value and the saturated limits are one `norm_cdf` result,
/// within `2^-54 + 2^-112`.
const SINGLE_PHI_BOUND: f64 = 5.7e-17;

/// The proved bound of the high-correlation branch for `rho > 0`: `2708e-19`
/// (`formal/bivariate/BvnHighEnd.v`, `high_pos_end`), rounded up in the fourth
/// digit.
const HIGH_BOUND_POSITIVE: f64 = 2.709e-16;

/// The proved bound of the high-correlation branch for `rho < 0`: `3333e-19`
/// (`high_neg_end_diff`, `high_neg_end_zero`), rounded up in the fourth digit.
const HIGH_BOUND_NEGATIVE: f64 = 3.334e-16;

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
    const RULES: [(&[f64], &[f64]); 9] = [
        (&GL4_X, &GL4_W),
        (&GL6_X, &GL6_W),
        (&GL8_X, &GL8_W),
        (&GL10_X, &GL10_W),
        (&GL12_X, &GL12_W),
        (&GL14_X, &GL14_W),
        (&GL16_X, &GL16_W),
        (&GL20_X, &GL20_W),
        (&GL24_X, &GL24_W),
    ];
    let m = rho.abs();
    let index = LOW_RULE_LIMITS
        .iter()
        .position(|&limit| m <= limit)
        .unwrap_or(LOW_RULE_LIMITS.len());
    RULES[index]
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

    /// [`Self::cdf`] with its absolute error bound, [`Self::absolute_error_bound`].
    #[must_use]
    pub fn cdf_bounded(&self, x: f64, y: f64) -> BoundedProbability {
        bounded(self.cdf(x, y), self.absolute_error_bound())
    }

    /// The bound on `|cdf(x, y) - P|` at this correlation, for every finite
    /// threshold pair; see [`absolute_error_bound`].
    #[must_use]
    pub fn absolute_error_bound(&self) -> f64 {
        regime_bound(self.regime, self.nodes, self.rho)
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
        let bound = self.absolute_error_bound();
        bounded_in_blocks(
            x,
            y,
            out,
            |_| bound,
            |_, x, y, values| self.cdf_slice(x, y, values),
        );
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

/// Panels of the high-correlation quadrature are `[s / 2, s]` for `s = a, a/2,
/// a/4, ...` while `s` exceeds this. On the remaining `[0, s]` the integrand is
/// integrated analytically (`docs/bivariate_normal_high.md` sections 1.4, 1.5).
const PANEL_FLOOR: f64 = 0.003;

/// The integral of the high branch is zero to `1e-22` from this `hk` on, and
/// is not computed (`docs/bivariate_normal_high.md` section 1.7, A3).
const HK_CUTOFF: f64 = 100.0;

/// A Gauss-Legendre rule of the panels: the positive abscissas' weights, the
/// unit squares `((3 + t)/4)^2` and `((3 - t)/4)^2` of the abscissas `t`, and
/// the weight of the centre node at 0 (`None` for an even order).
struct PanelRule {
    w: &'static [f64],
    plus: &'static [f64],
    minus: &'static [f64],
    centre: Option<f64>,
}

/// The rule of the panel of scale `s`: 16 nodes above `0.095`, 15 below.
fn panel_rule(s: f64) -> PanelRule {
    if s > 0.095 {
        PanelRule {
            w: &GL16_W,
            plus: &GL16_XP,
            minus: &GL16_XM,
            centre: None,
        }
    } else {
        PanelRule {
            w: &GL15_W,
            plus: &GL15_XP,
            minus: &GL15_XM,
            centre: Some(GL15_W0),
        }
    }
}

/// The bound on `|bivariate_norm_cdf(x, y, rho) - P|` for every finite pair of
/// thresholds, or NaN where `rho` is NaN or outside `[-1, 1]`.
///
/// For `|rho| < 0.925` it is the proved bound of the quadrature rule that
/// `|rho|` selects, from `1.9e-16` to `3.72e-16` (`docs/bivariate_normal_budget.md`);
/// the closed-form regimes carry at most `1.7e-16`.
#[must_use]
pub fn absolute_error_bound(rho: f64) -> f64 {
    match Regime::of(rho) {
        None => f64::NAN,
        Some(regime) => regime_bound(regime, 2 * low_correlation_rule(rho).0.len(), rho),
    }
}

/// The bound of a regime; `nodes` is the low rule's length, `rho` the correlation.
fn regime_bound(regime: Regime, nodes: usize, rho: f64) -> f64 {
    match regime {
        Regime::Independent | Regime::Countermonotone => CLOSED_FORM_BOUND,
        Regime::Comonotone => SINGLE_PHI_BOUND,
        Regime::Low => LOW_RULE_BOUNDS[rule_index(nodes)],
        Regime::High if rho < 0.0 => HIGH_BOUND_NEGATIVE,
        Regime::High => HIGH_BOUND_POSITIVE,
    }
}

/// The index of the low rule with this many nodes.
fn rule_index(nodes: usize) -> usize {
    match nodes {
        4 => 0,
        6 => 1,
        8 => 2,
        10 => 3,
        12 => 4,
        14 => 5,
        16 => 6,
        20 => 7,
        _ => 8,
    }
}

/// [`BivariateNormal::cdf_bounded`]'s result for a value and its bound.
fn bounded(value: f64, bound: f64) -> BoundedProbability {
    if value.is_nan() {
        return BoundedProbability {
            value,
            error: f64::NAN,
        };
    }
    BoundedProbability {
        value,
        error: bound,
    }
}

/// Fill `out` with the bound of each value `fill` writes for the pairs,
/// in blocks, so the bounded form needs no allocation.
fn bounded_in_blocks(
    x: &[f64],
    y: &[f64],
    out: &mut [BoundedProbability],
    bound: impl Fn(usize) -> f64,
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
        for (i, (o, &v)) in out.iter_mut().zip(values.iter()).enumerate() {
            *o = bounded(v, bound(block * BLOCK + i));
        }
    }
}

/// The integrand of the high-correlation integral at a node of the panel, times
/// its weight: `weight * exp(-phi) / rs` with `xs = x^2` (the panel's `s^2`
/// times the node's unit square), `rs = sqrt(1 - xs)` and
/// `phi = bs / (2 xs) + hk / (1 + rs)`; zero where `exp(-phi)` is below `e^-100`.
/// `phi` is not negative on the branch's domain, so every term is positive.
fn integrand_term(xs: f64, weight: f64, bs: f64, hk: f64) -> f64 {
    let rs = sqrt(1.0 - xs);
    let phi = bs / (2.0 * xs) + hk / (1.0 + rs);
    if phi < 100.0 {
        weight * (exp(-phi) / rs)
    } else {
        0.0
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
    bounded_in_blocks(
        x,
        y,
        out,
        |i| absolute_error_bound(rho[i]),
        |start, x, y, values| {
            bivariate_norm_cdf_slice(x, y, &rho[start..start + x.len()], values);
        },
    );
}

/// Genz's upper-tail high-correlation algorithm (BVND, `|rho| >= 0.925`), with
/// the integral `J` of `exp(-bs/(2 x^2) - hk/(1 + rs)) / rs` over `[0, a]`
/// taken on graded panels above `0.003` (a double-word sum of positive terms,
/// whose truncation is provably bounded) and in closed form below, where
/// Genz's Taylor-corrected moments are accurate to `2.3e-18`.
/// `dh` and `dk` are the negated thresholds, `P(X >= dh, Y >= dk)`.
/// `docs/bivariate_normal_high.md` derives each line.
fn high_correlation(dh: f64, dk: f64, rho: f64) -> f64 {
    // Genz reflects `k` and `hk` together for negative correlation.
    let (k, hk) = if rho < 0.0 {
        (-dk, -(dh * dk))
    } else {
        (dk, dh * dk)
    };
    let bs = (dh - k) * (dh - k);

    // `J`, the quantity `bvn` below accumulates (its negative over `TAU`).
    let mut bvn = 0.0;
    if hk < HK_CUTOFF {
        let ass = (1.0 - rho.abs()) * (1.0 + rho.abs());
        let a = sqrt(ass);
        let c = (4.0 - hk) / 8.0;
        let d = (12.0 - hk) / 16.0;

        // The panels cover `[x_m, a]`, `x_m` the first scale at or below the
        // floor. Their terms are positive and sum to up to 0.41, so the sum is a
        // double-word: `two_sum` per term, the low parts added in order.
        let (mut high, mut low) = (0.0, 0.0);
        let mut s = a;
        while s > PANEL_FLOOR {
            let rule = panel_rule(s);
            let half_width = s / 4.0;
            let s2 = s * s;
            let mut add = |xs_unit: f64, w: f64| {
                let term = half_width * integrand_term(s2 * xs_unit, w, bs, hk);
                let (sum, err) = two_sum(high, term);
                high = sum;
                low += err;
            };
            for i in 0..rule.w.len() {
                add(rule.plus[i], rule.w[i]);
                add(rule.minus[i], rule.w[i]);
            }
            if let Some(w0) = rule.centre {
                add(0.5625, w0);
            }
            s /= 2.0;
        }
        let panels = high + low;

        // Genz's closed form for `int_0^s E T dx` on the rest, `s <= 0.003`.
        // From `b = 20 s` on, `E <= e^-200` there and the integral is below
        // `1e-46`: the closed form is not evaluated.
        let b = sqrt(bs);
        if b < 20.0 * s {
            let ass = s * s;
            let asr = -(bs / ass + hk) / 2.0;
            bvn = s
                * exp(asr)
                * (1.0 - c * (bs - ass) * (1.0 - d * bs / 5.0) / 3.0 + c * d * ass * ass / 5.0);
            bvn -= exp(-hk / 2.0)
                * SQRT_TAU
                * norm_cdf(-b / s)
                * b
                * (1.0 - c * bs * (1.0 - d * bs / 5.0) / 3.0);
        }
        bvn += panels;
    }

    bvn = -bvn / TAU;
    let result = if rho > 0.0 {
        bvn + norm_cdf(-dh.max(dk))
    } else if -dh > dk {
        // `-bvn` is the integral's share, `g`. The second term is
        // `Phi(-dh) - Phi(dk)`, positive here: the exact difference of the two
        // values is kept as the double-word `s + e`, so it carries no rounding
        // of its own, and `g` joins it once (`BvnHighAssembly.v`).
        let g = -bvn;
        let (hi, lo) = two_sum(norm_cdf(-dh), -norm_cdf(dk));
        hi + (lo + g)
    } else {
        // `Phi(-dh) <= Phi(dk)`: the reflection's difference term is zero.
        -bvn
    };
    clamp_to_probability(result)
}
