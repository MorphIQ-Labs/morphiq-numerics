//! `asin`: the inverse sine rounded to nearest, ties to even.
//!
//! The derivation and every bound are in
//! [`docs/asin.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/asin.md);
//! section numbers below refer to it.

#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod tables;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord;
use crate::eft::two_prod_d;
use crate::exact::sqrt;
use crate::ln::decide_with;
use crate::q256::Q256;
use crate::trig::{accurate_sin_cos, half_pi};
use tables::{HALF_PI, POLY0, SEGMENTS};

/// `asin x = x` for every `|x|` below this (§2): `0x1.7137449123ef6p−26`, the
/// least argument whose `asin` is not `x`.
const ASIN_IS_X: f64 = f64::from_bits(0x3e57_1374_4912_3ef6);
/// The binary64 nearest `π/2`, which is `asin(±1)`.
const HALF_PI_F64: f64 = f64::from_bits(0x3ff9_21fb_5444_2d18);
/// The largest binary64 below `√½` (§3): from `x` above it, `asin x` exceeds
/// `π/4` and is computed through its complement.
const SPLIT: f64 = f64::from_bits(0x3fe6_a09e_667f_3bcc);
/// `1.5·2^52`, which rounds `64 z` to an integer (§4).
const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−62` (§6).
const EPS: f64 = f64::from_bits(0x3c10_0000_0000_0004);

/// `asin x`, correctly rounded: the binary64 number nearest to the inverse sine
/// of `x`, ties to even, for every binary64 `x` (§6).
///
/// `asin(±0) = ±0` and `asin(±1) = ±π/2`; a NaN and every `|x| > 1` give NaN.
#[must_use]
pub fn asin(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    let magnitude = x.abs();
    if magnitude > 1.0 {
        return f64::NAN;
    }
    if magnitude < ASIN_IS_X {
        return x;
    }
    if magnitude == 1.0 {
        return HALF_PI_F64.copysign(x);
    }
    let reduced = Reduced::of(magnitude);
    let (y, start) = reduced.fast();
    let value = decide_with(y, EPS).unwrap_or_else(|| reduced.accurate(start));
    value.copysign(x)
}

/// Which side of `√½` an argument lies on, with what the fast path computes
/// from it (§3).
#[derive(Clone, Copy)]
enum Reduced {
    /// `x <= SPLIT`: `asin x`.
    Direct { x: f64 },
    /// `x > SPLIT`: `asin x = π/2 − δ` with `δ = 2·asin(√((1 − x)/2))`.
    Complement { x: f64, z: DoubleWord },
}

impl Reduced {
    /// `x` in `[ASIN_IS_X, 1)`.
    fn of(x: f64) -> Self {
        if x <= SPLIT {
            return Self::Direct { x };
        }
        // 1 − x is exact for x in [1/2, 1), and so is the halving: u is the
        // exact (1 − x)/2.
        let u = (1.0 - x) * 0.5;
        let s = sqrt(u);
        // s >= 2^-27, so s² is inside two_prod_d's domain.
        let (square, square_error) = two_prod_d(s, s);
        // u − s² exactly, up to a rounding of order 2^−106·u; s_lo is its
        // Newton correction to the square root.
        let residual = (u - square) - square_error;
        let z = DoubleWord::sum(s, residual / (2.0 * s));
        Self::Complement { x, z }
    }

    /// The fast path (§4): the double-word approximation `y` of the positive
    /// result, and the value Newton's step starts from: `y`, or for the
    /// complement `δ`, which is accurate relative to `δ` where `π/2 − y` is not.
    fn fast(self) -> (DoubleWord, DoubleWord) {
        match self {
            Self::Direct { x } => {
                let y = series(DoubleWord::from_f64(x));
                (y, y)
            }
            Self::Complement { z, .. } => {
                let delta = series(z).mul_f64_d(2.0);
                (DoubleWord::sum(HALF_PI.0, HALF_PI.1).sub(delta), delta)
            }
        }
    }

    /// The accurate path (§5): [`Self::accurate_value`] rounded.
    #[cold]
    #[inline(never)]
    fn accurate(self, start: DoubleWord) -> f64 {
        self.accurate_value(start).to_f64()
    }

    /// One Newton step in `Q256` from `start` (§5), before rounding.
    fn accurate_value(self, start: DoubleWord) -> Q256 {
        let start = Q256::from_f64(start.hi()).add(Q256::from_f64(start.lo()));
        match self {
            Self::Direct { x } => {
                // y₁ = y₀ + (x − sin y₀)/cos y₀.
                let (sin, cos) = accurate_sin_cos(start);
                let residual = Q256::from_f64(x).add(sin.neg());
                start.add(residual.mul(cos.recip()))
            }
            Self::Complement { x, .. } => {
                // δ solves cos δ = x: δ₁ = δ₀ + (cos δ₀ − x)/sin δ₀, and the
                // result is π/2 − δ₁.
                let (sin, cos) = accurate_sin_cos(start);
                let residual = cos.add(Q256::from_f64(-x));
                let delta = start.add(residual.mul(sin.recip()));
                half_pi().add(delta.neg())
            }
        }
    }
}

/// `asin z` for a double-word `z` in `[0, SPLIT]` (§4): a table at `a = k/64`
/// and a polynomial in `t = z − a`; below `1/128`, the series in `z`.
fn series(z: DoubleWord) -> DoubleWord {
    let (z_hi, z_lo) = (z.hi(), z.lo());
    let i = (z_hi * 64.0 + SHIFTER) - SHIFTER;
    if i == 0.0 {
        let z2 = z_hi * z_hi;
        let [p0, p1, p2, p3] = POLY0;
        let p = p0 + z2 * (p1 + z2 * (p2 + z2 * p3));
        // asin z = z + z³·P(z²).
        return z.add_f64((z_hi * z2) * p);
    }
    // t = z − i/64: z_hi − i/64 is exact, by Sterbenz's lemma for i ≥ 1.
    let t = DoubleWord::sum(z_hi - i * 0.015_625, z_lo);
    let (t_hi, t_lo) = (t.hi(), t.lo());
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 1 <= i <= 45
    let [y_hi, y_lo, c_hi, c_lo, g0, g1, g2, g3, g4, g5, g6, g7, g8] = SEGMENTS[i as usize - 1];
    let g = g0
        + t_hi
            * (g1
                + t_hi
                    * (g2
                        + t_hi
                            * (g3
                                + t_hi
                                    * (g4 + t_hi * (g5 + t_hi * (g6 + t_hi * (g7 + t_hi * g8)))))));
    // asin(a + t) = asin a + c₁·t + t²·G(t), with c₁·t's leading product exact.
    // t_hi is zero or at least 2^-900 and c_hi at least 1 (docs/asin.md §4).
    let (p_hi, p_lo) = two_prod_d(t_hi, c_hi);
    let tail = p_lo + (t_hi * c_lo + t_lo * c_hi) + (t_hi * t_hi) * g;
    DoubleWord::sum(y_hi, y_lo).add(DoubleWord::fast_sum(p_hi, tail))
}

/// The reduction's branch and double-word, for the internal cross-check:
/// `true` with `z = (x, 0)` on the direct branch, `false` with the
/// complement's `z` (`x` in `[ASIN_IS_X, 1)`).
#[cfg(test)]
pub(crate) fn crosscheck_reduced(x: f64) -> (bool, f64, f64) {
    match Reduced::of(x) {
        Reduced::Direct { x } => (true, x, 0.0),
        Reduced::Complement { z, .. } => (false, z.hi(), z.lo()),
    }
}

/// `series` at the double-word `z`, for the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_series(z: DoubleWord) -> DoubleWord {
    series(z)
}

/// The fast path at `x` in `[ASIN_IS_X, 1)`: its result, the start of the
/// Newton step and the rounding test's decision, for the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_fast(x: f64) -> (DoubleWord, DoubleWord, Option<f64>) {
    let (y, start) = Reduced::of(x).fast();
    (y, start, decide_with(y, EPS))
}

/// The accurate path's `Q256` value at `x` in `[ASIN_IS_X, 1)` from `start`,
/// before rounding, for the internal cross-check: rounded to binary64 the
/// Newton step's correction, about `2^-63` relative, is invisible.
#[cfg(test)]
pub(crate) fn crosscheck_accurate(x: f64, start: DoubleWord) -> Q256 {
    Reduced::of(x).accurate_value(start)
}

/// `(sin, cos)` in `Q256` at `start`, as the accurate path computes them, for
/// the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_sin_cos(start: DoubleWord) -> (Q256, Q256) {
    accurate_sin_cos(Q256::from_f64(start.hi()).add(Q256::from_f64(start.lo())))
}

/// `Q256::recip`, which the accurate path uses, for the internal cross-check:
/// its third Newton step, below `2^-255` relative to the result, is invisible
/// through the accurate path's value.
#[cfg(test)]
pub(crate) fn crosscheck_recip(x: Q256) -> Q256 {
    x.recip()
}
