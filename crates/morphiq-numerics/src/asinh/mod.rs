//! `asinh`: the inverse hyperbolic sine rounded to nearest, ties to even.
//!
//! The derivation and every bound are in
//! [`docs/asinh.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/asinh.md);
//! section numbers below refer to it.

#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod tables;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord;
use crate::eft::two_prod_d;
use crate::exact::sqrt;
use crate::ln::{Reduced, decide_with};
use crate::q256::Q256;
use tables::{EXP_STEPS, INV_LN2, LN2, LN2_Q256, POLY0};

/// `asinh x = x` for every `|x|` up to this (§1): `0x1.7137449123ef6p−26`, the
/// greatest argument whose `asinh` rounds to `x`.
const ASINH_IS_X: f64 = f64::from_bits(0x3e57_1374_4912_3ef6);
/// `2^−7`: the series serves `|x|` below it, the logarithm of `x + √(x² + 1)`
/// from it (§3).
const TWO_M7: f64 = f64::from_bits(0x3f80_0000_0000_0000);
/// `2^28`: from it `asinh x = ln 2x + 1/(4x²)` to far beyond the precision (§3).
const TWO_28: f64 = f64::from_bits(0x41b0_0000_0000_0000);
/// `1.5·2^52`, which rounds `y/ln 2` to an integer (§4).
const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−63` (§5).
const EPS: f64 = f64::from_bits(0x3c00_0000_0000_0004);

/// `asinh x`, correctly rounded: the binary64 number nearest to the inverse
/// hyperbolic sine of `x`, ties to even, for every binary64 `x` (§5).
///
/// `asinh(±0) = ±0` and `asinh(±∞) = ±∞`; a NaN gives itself.
#[must_use]
pub fn asinh(x: f64) -> f64 {
    let magnitude = x.abs();
    // A NaN, ±0 and ±∞ are their own images, as is every x up to the threshold.
    if x.is_nan() || magnitude <= ASINH_IS_X || magnitude == f64::INFINITY {
        return x;
    }
    let y = fast(magnitude);
    let value = decide_with(y, EPS).unwrap_or_else(|| accurate(magnitude, y));
    value.copysign(x)
}

/// The fast path (§3): `asinh x` as a double-word, for `x` in
/// `(ASINH_IS_X, ∞)`.
fn fast(x: f64) -> DoubleWord {
    if x < TWO_M7 {
        series(x)
    } else if x < TWO_28 {
        logarithm(x)
    } else {
        large(x)
    }
}

/// `x + x³·P(x²)`, `x < 2^−7` (§3).
fn series(x: f64) -> DoubleWord {
    let x2 = x * x;
    let [p0, p1, p2, p3] = POLY0;
    let p = p0 + x2 * (p1 + x2 * (p2 + x2 * p3));
    DoubleWord::from_f64(x).add_f64((x * x2) * p)
}

/// `ln(x + √(x² + 1))`, `2^−7 ≤ x < 2^28` (§3): `v = x + s`, `s = √(x² + 1)`
/// as double-words, then `ln v_hi + RN(v_lo/v_hi)`.
fn logarithm(x: f64) -> DoubleWord {
    // x >= 2^-7: x² is inside two_prod_d's domain.
    let (square, square_error) = two_prod_d(x, x);
    // u = 1 + x² to double-word accuracy.
    let u = DoubleWord::sum(1.0, square).add_f64(square_error);
    let root = sqrt(u.hi());
    let (root_square, root_square_error) = two_prod_d(root, root);
    // u − root² up to a rounding of order 2^−106·u; its Newton correction.
    let residual = ((u.hi() - root_square) - root_square_error) + u.lo();
    let s = DoubleWord::sum(root, residual / (2.0 * root));
    let v = DoubleWord::sum(x, s.hi()).add_f64(s.lo());
    Reduced::of(v.hi()).fast_value().add_f64(v.lo() / v.hi())
}

/// `ln x + ln 2 + 1/(4x²)`, `x ≥ 2^28` (§3).
fn large(x: f64) -> DoubleWord {
    let ln_2x = Reduced::of(x)
        .fast_value()
        .add(DoubleWord::sum(LN2.0, LN2.1));
    ln_2x.add_f64((0.25 / x) / x)
}

/// The accurate path (§4): two Newton steps for `sinh y = x` in `Q256` from the
/// fast value, then one rounding.
#[cold]
#[inline(never)]
fn accurate(x: f64, y: DoubleWord) -> f64 {
    accurate_value(x, y).to_f64()
}

/// The accurate value before rounding (§4), for the internal cross-check.
pub(crate) fn accurate_value(x: f64, y: DoubleWord) -> Q256 {
    let x = Q256::from_f64(x);
    let start = Q256::from_f64(y.hi()).add(Q256::from_f64(y.lo()));
    newton(x, newton(x, start))
}

/// `y + (x − sinh y)/cosh y`, in `Q256` (§4).
fn newton(x: Q256, y: Q256) -> Q256 {
    let (m, k) = exp(y);
    let e = m.mul_pow2(k);
    let e_inverse = recip(m).mul_pow2(-k);
    let sinh = e.add(e_inverse.neg()).mul_pow2(-1);
    let cosh = e.add(e_inverse).mul_pow2(-1);
    y.add(x.add(sinh.neg()).mul(recip(cosh)))
}

/// `e^y` as `(m, k)` with `e^y = m·2^k`, `m = exp r`, `r = y − k·ln 2`,
/// `|r| ≤ 0.3467`, for `0 ≤ y ≤ 711` (§4).
fn exp(y: Q256) -> (Q256, i32) {
    let k = (y.to_f64() * INV_LN2 + SHIFTER) - SHIFTER;
    let r = y.add(
        Q256::from_f64(k)
            .mul(Q256::new(false, LN2_Q256.0, LN2_Q256.1))
            .neg(),
    );
    let mut h = Q256::ONE;
    for &(m, e) in EXP_STEPS.iter().rev() {
        h = Q256::ONE.add(r.mul(Q256::new(false, m, e)).mul(h));
    }
    #[allow(clippy::cast_possible_truncation)] // |k| <= 1025
    (h, k as i32)
}

/// `1/c`, with `c` scaled into `[1, 2)` first so that `Q256::recip`'s
/// binary64 start is finite for every `c` here, however large (§4).
fn recip(c: Q256) -> Q256 {
    let top = c.top();
    c.mul_pow2(-top).recip().mul_pow2(-top)
}

/// The fast path's double-word at `x` in `(ASINH_IS_X, ∞)` and the rounding
/// test's decision, for the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_fast(x: f64) -> (DoubleWord, Option<f64>) {
    let y = fast(x);
    (y, decide_with(y, EPS))
}

/// The accurate path's exponential at `y`, as `(m, k)` with `e^y = m 2^k`, for
/// the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_exp(y: Q256) -> (Q256, i32) {
    exp(y)
}

/// The accurate path's `Q256` value at `x` from the fast value `y`, before
/// rounding, for the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_accurate(x: f64, y: DoubleWord) -> Q256 {
    accurate_value(x, y)
}
