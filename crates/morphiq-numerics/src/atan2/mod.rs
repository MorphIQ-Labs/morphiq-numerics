//! `atan2`: the angle of `(x, y)` rounded to nearest, ties to even.
//!
//! The derivation and every bound are in
//! [`docs/atan2.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/atan2.md);
//! section numbers below refer to it.

#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod tables;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord;
use crate::eft::two_prod;
use crate::ln::decide_with;
use crate::q256::Q256;
use crate::trig::{accurate_sin_cos, half_pi};
use tables::{HALF_PI, POLY0, SEGMENTS};

/// `RN(π)`, `RN(π/2)`, `RN(π/4)` and `RN(3π/4)`: the results at the special
/// arguments, and for a ratio so small that the angle is a constant (§1).
const PI_F64: f64 = f64::from_bits(0x4009_21fb_5444_2d18);
const HALF_PI_F64: f64 = f64::from_bits(0x3ff9_21fb_5444_2d18);
const QUARTER_PI_F64: f64 = f64::from_bits(0x3fe9_21fb_5444_2d18);
const THREE_QUARTER_PI_F64: f64 = f64::from_bits(0x4002_d97c_7f33_21d2);
/// `1.5·2^52`, which rounds `64 t` to an integer (§4).
const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−62` (§6).
const EPS: f64 = f64::from_bits(0x3c10_0000_0000_0004);
/// `2^−900`: below this ratio the angle is `π/2`, `π` or the ratio itself (§3).
const TINY: f64 = f64::from_bits(0x07b0_0000_0000_0000);

/// Which of the four forms of the angle a pair takes (§3), with `φ = atan(n/d)`
/// for `n ≤ d` the smaller magnitude over the larger.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Form {
    /// `|y| ≤ |x|`, `x > 0`: `φ`.
    Phi,
    /// `|y| > |x|`, `x > 0`: `π/2 − φ`.
    HalfPiMinus,
    /// `|y| ≤ |x|`, `x < 0`: `π − φ`.
    PiMinus,
    /// `|y| > |x|`, `x < 0`: `π/2 + φ`.
    HalfPiPlus,
}

/// `atan2(y, x)`, the angle of the point `(x, y)` in `[−π, π]` to the positive
/// `x` axis: the binary64 number nearest to it, ties to even (§1, §6).
///
/// `atan2(±0, +0) = ±0`, `atan2(±0, −0) = ±π`; a NaN in either argument gives
/// NaN.
#[must_use]
pub fn atan2(y: f64, x: f64) -> f64 {
    if y.is_nan() || x.is_nan() {
        return f64::NAN;
    }
    let (a, b) = (y.abs(), x.abs());
    let negative = x.is_sign_negative();
    let magnitude = if a == 0.0 {
        if negative { PI_F64 } else { 0.0 }
    } else if b == 0.0 {
        HALF_PI_F64
    } else if a == f64::INFINITY {
        match (b == f64::INFINITY, negative) {
            (false, _) => HALF_PI_F64,
            (true, false) => QUARTER_PI_F64,
            (true, true) => THREE_QUARTER_PI_F64,
        }
    } else if b == f64::INFINITY {
        if negative { PI_F64 } else { 0.0 }
    } else {
        angle(a, b, negative)
    };
    magnitude.copysign(y)
}

/// The angle's magnitude for finite nonzero `a = |y|`, `b = |x|`.
fn angle(a: f64, b: f64, negative: bool) -> f64 {
    let form = match (a > b, negative) {
        (false, false) => Form::Phi,
        (true, false) => Form::HalfPiMinus,
        (false, true) => Form::PiMinus,
        (true, true) => Form::HalfPiPlus,
    };
    let (n, d) = if a > b { (b, a) } else { (a, b) };
    let quotient = n / d;
    if quotient < TINY {
        // φ < 2^−900 (§3).
        return match form {
            Form::Phi => tiny_phi(n, d, quotient),
            Form::HalfPiMinus | Form::HalfPiPlus => HALF_PI_F64,
            Form::PiMinus => PI_F64,
        };
    }
    let (y, phi) = fast(n, d, form);
    decide_with(y, EPS).unwrap_or_else(|| accurate(n, d, form, phi))
}

/// `atan(n/d)` for `n/d < 2^−900` (§3): `RN(n/d)`, unless `n/d` is exactly the
/// midpoint of two subnormals (or of the largest and `MIN_POSITIVE`), where
/// `atan` lies just below it and rounds down.
fn tiny_phi(n: f64, d: f64, quotient: f64) -> f64 {
    if quotient > f64::MIN_POSITIVE {
        // `atan t = t(1 − t²/3 + …)` is below `t` by a relative 2^−1800; `t` is
        // never a midpoint of normal numbers (53 bits cannot make 54), and the
        // nearest midpoint is at least 2^−107 away relatively otherwise. The
        // one midpoint with 53 bits, between the largest subnormal and
        // `MIN_POSITIVE`, rounds to `MIN_POSITIVE` and is tested below.
        return quotient;
    }
    let (mn, en) = odd_part(n);
    let (md, ed) = odd_part(d);
    // n/d = (mn/md)·2^(en − ed) is the midpoint (2m + 1)·2^−1075 exactly when
    // md divides mn and en − ed = −1075.
    if mn % md == 0 && en - ed == -1075 {
        let j = mn / md;
        return f64::from_bits((j - 1) / 2);
    }
    quotient
}

/// `x = m·2^e` with `m` odd, for a finite positive `x`.
fn odd_part(x: f64) -> (u64, i32) {
    let bits = x.to_bits();
    let biased = (bits >> 52) as i32;
    let fraction = bits & ((1 << 52) - 1);
    let (m, e) = if biased == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1 << 52), biased - 1075)
    };
    let shift = m.trailing_zeros();
    (m >> shift, e + shift as i32)
}

/// `x·2^−k` exactly, for the `k` the callers use (`|k| ≤ 1074`) and a result
/// inside the normal range: two multiplications by powers of two.
fn scale(x: f64, k: i32) -> f64 {
    let half = k / 2;
    x * pow2(-half) * pow2(-(k - half))
}

/// `2^e` for `|e| ≤ 1023`.
fn pow2(e: i32) -> f64 {
    #[allow(clippy::cast_sign_loss)] // 1023 + e >= 0
    f64::from_bits(((1023 + e) as u64) << 52)
}

/// The unbiased exponent of the leading bit of a finite positive `x`, a
/// subnormal's included.
fn exponent(x: f64) -> i32 {
    let bits = x.to_bits();
    let biased = (bits >> 52) as i32;
    if biased == 0 {
        let fraction = bits & ((1 << 52) - 1);
        -1011 - fraction.leading_zeros() as i32
    } else {
        biased - 1023
    }
}

/// The fast path (§3, §4): the double-word of the angle, and `φ` itself, which
/// the accurate path starts from.
fn fast(n: f64, d: f64, form: Form) -> (DoubleWord, DoubleWord) {
    // Both scaled by 2^−e so that d ∈ [1, 2): the ratio is unchanged, and the
    // division below stays clear of underflow.
    let e = exponent(d);
    let (ns, ds) = (scale(n, e), scale(d, e));
    let q = ns / ds;
    let (p, p_error) = two_prod(q, ds);
    // n' − p is exact by Sterbenz's lemma; its remainder is the quotient's error.
    let residual = (ns - p) - p_error;
    let t = DoubleWord::fast_sum(q, residual / ds);
    let phi = series(t);
    let half_pi = DoubleWord::sum(HALF_PI.0, HALF_PI.1);
    let y = match form {
        Form::Phi => phi,
        Form::HalfPiMinus => half_pi.sub(phi),
        Form::HalfPiPlus => half_pi.add(phi),
        Form::PiMinus => half_pi.mul_f64(2.0).sub(phi),
    };
    (y, phi)
}

/// `atan t` for a double-word `t` in `(0, 1]` (§4): a table at `a = k/64` and a
/// polynomial in `s = t − a`; below `1/128`, the series in `t`.
fn series(t: DoubleWord) -> DoubleWord {
    let (t_hi, t_lo) = (t.hi(), t.lo());
    let i = (t_hi * 64.0 + SHIFTER) - SHIFTER;
    if i == 0.0 {
        let t2 = t_hi * t_hi;
        let [p0, p1, p2, p3] = POLY0;
        let p = p0 + t2 * (p1 + t2 * (p2 + t2 * p3));
        // atan t = t + t³·P(t²).
        return t.add_f64((t_hi * t2) * p);
    }
    // s = t − i/64: t_hi − i/64 is exact, by Sterbenz's lemma for i ≥ 1.
    let s = DoubleWord::sum(t_hi - i * 0.015_625, t_lo);
    let (s_hi, s_lo) = (s.hi(), s.lo());
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 1 <= i <= 64
    let [y_hi, y_lo, c_hi, c_lo, g0, g1, g2, g3, g4, g5, g6, g7, g8] = SEGMENTS[i as usize - 1];
    let g = g0
        + s_hi
            * (g1
                + s_hi
                    * (g2
                        + s_hi
                            * (g3
                                + s_hi
                                    * (g4 + s_hi * (g5 + s_hi * (g6 + s_hi * (g7 + s_hi * g8)))))));
    // atan(a + s) = atan a + c₁·s + s²·G(s), with c₁·s's leading product exact.
    let (p_hi, p_lo) = two_prod(s_hi, c_hi);
    let tail = p_lo + (s_hi * c_lo + s_lo * c_hi) + (s_hi * s_hi) * g;
    DoubleWord::sum(y_hi, y_lo).add(DoubleWord::fast_sum(p_hi, tail))
}

/// The accurate path (§5): [`accurate_value`] rounded.
#[cold]
#[inline(never)]
fn accurate(n: f64, d: f64, form: Form, phi: DoubleWord) -> f64 {
    accurate_value(n, d, form, phi).to_f64()
}

/// One Newton step in `Q256` for `d sin φ = n cos φ` from `φ` (§5), then the
/// form's constant: `φ₁ = φ₀ + (n cos φ₀ − d sin φ₀)/(d cos φ₀ + n sin φ₀)`.
/// With `φ₀ = φ* + δ` the step lands at `φ* + δ − tan δ`, a cubic error.
pub(crate) fn accurate_value(n: f64, d: f64, form: Form, phi: DoubleWord) -> Q256 {
    let phi0 = Q256::from_f64(phi.hi()).add(Q256::from_f64(phi.lo()));
    let (sin, cos) = accurate_sin_cos(phi0);
    let (n, d) = (Q256::from_f64(n), Q256::from_f64(d));
    let numerator = n.mul(cos).add(d.mul(sin).neg());
    let denominator = d.mul(cos).add(n.mul(sin));
    let phi1 = phi0.add(numerator.mul(recip(denominator)));
    match form {
        Form::Phi => phi1,
        Form::HalfPiMinus => half_pi().add(phi1.neg()),
        Form::HalfPiPlus => half_pi().add(phi1),
        Form::PiMinus => half_pi().mul_pow2(1).add(phi1.neg()),
    }
}

/// `1/c`, with `c` scaled into `[1, 2)` first so that `Q256::recip`'s binary64
/// start is finite whatever `c` is (§5).
fn recip(c: Q256) -> Q256 {
    let top = c.top();
    c.mul_pow2(-top).recip().mul_pow2(-top)
}

/// The form with index `i` in `Phi`, `HalfPiMinus`, `PiMinus`, `HalfPiPlus`
/// order, for the internal cross-check.
#[cfg(test)]
fn form_by_index(i: usize) -> Form {
    [
        Form::Phi,
        Form::HalfPiMinus,
        Form::PiMinus,
        Form::HalfPiPlus,
    ][i]
}

/// The fast path at `n ≤ d` with `n/d ≥ 2^-900`: the angle's double-word, `φ`
/// and the rounding test's decision, for the internal cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_fast(
    n: f64,
    d: f64,
    form: usize,
) -> (DoubleWord, DoubleWord, Option<f64>) {
    let (y, phi) = fast(n, d, form_by_index(form));
    (y, phi, decide_with(y, EPS))
}

/// The accurate path's `Q256` value from `φ`, before rounding, for the internal
/// cross-check.
#[cfg(test)]
pub(crate) fn crosscheck_accurate(n: f64, d: f64, form: usize, phi: DoubleWord) -> Q256 {
    accurate_value(n, d, form_by_index(form), phi)
}
