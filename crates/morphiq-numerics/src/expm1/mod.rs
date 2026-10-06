//! `expm1`: `e^x − 1` rounded to nearest, ties to even, wherever the rounding
//! test decides, and within a proved bound otherwise.
//!
//! The derivation is in
//! [`docs/expm1.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/expm1.md);
//! section numbers below refer to it.

mod tables;

use crate::double_word::DoubleWord;
use crate::eft::two_prod;
use crate::exp::{Reduced, scale};
use crate::ln::decide_with;
use crate::q128::Q128;
use tables::{POLY, RECIPROCALS};

/// The least `x` whose `e^x − 1` rounds to `+∞` (§1; the reference fixture's
/// threshold "least x overflowing").
const X_OVERFLOW: f64 = f64::from_bits(0x4086_2e42_fefa_39f0);
/// The least `x` whose `e^x − 1` rounds to `−1` (§1; "least x rounding to -1").
const X_MINUS_ONE: f64 = f64::from_bits(0xc042_b708_8723_20e2);
/// `2^−54`: below it, `expm1(x) = x` (§1).
const TINY: f64 = f64::from_bits(0x3c90_0000_0000_0000);
/// `2^−5`: below it, the small-argument paths (§3, §4).
const SMALL: f64 = f64::from_bits(0x3fa0_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−62` (§6).
const EPS: f64 = f64::from_bits(0x3c10_0000_0000_0004);
/// The small-argument series degree: `RECIPROCALS` holds `1/2 ..= 1/(DEGREE + 1)`.
const DEGREE: usize = RECIPROCALS.len();

/// `e^x − 1`: correctly rounded whenever the rounding test decides it, and
/// otherwise within `(1/2 + 2^−65)` ulp (§6). Accurate as `x → 0`, where
/// `e^x − 1` cancels; `expm1(x) = x` for `|x| < 2^−54`.
///
/// `expm1(NaN)` is NaN, `expm1(+∞) = +∞`, `expm1(−∞) = −1` and
/// `expm1(±0) = ±0`.
#[must_use]
pub fn expm1(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x >= X_OVERFLOW {
        return f64::INFINITY;
    }
    if x <= X_MINUS_ONE {
        return -1.0;
    }
    let magnitude = x.abs();
    if magnitude < TINY {
        return x;
    }
    if magnitude < SMALL {
        if let Some(y) = decide_with(small_fast(x), EPS) {
            return y;
        }
        return small_accurate(x).to_f64();
    }
    let reduced = Reduced::of(x);
    if let Some(y) = decide_with(general_fast(&reduced), EPS) {
        return y;
    }
    general_accurate(&reduced).to_f64()
}

/// §3: `x + x²/2 + x³·W(x)` as a double-word, within `2^−62.3` of `e^x − 1`
/// for `2^−54 ≤ |x| < 2^−5` (`formal/expm1/tail.g`, `p.g`).
fn small_fast(x: f64) -> DoubleWord {
    let [c3, c4, c5, c6, c7, c8, c9] = POLY;
    let w8 = c8 + x * c9;
    let w7 = c7 + x * w8;
    let w6 = c6 + x * w7;
    let w5 = c5 + x * w6;
    let w4 = c4 + x * w5;
    let w = c3 + x * w4;
    // x² = s_hi + s_lo exactly; s_hi = RN(x²).
    let (s_hi, s_lo) = two_prod(x, x);
    let t = (x * s_hi) * w;
    // x²/2: halving is exact, and the pair stays a double-word.
    let half_square = DoubleWord::sum(0.5 * s_hi, 0.5 * s_lo);
    DoubleWord::from_f64(x).add(half_square).add_f64(t)
}

/// §4: `x·H_2` in `Q128`, `H_m = 1 + (x·(1/m))·H_(m+1)` from `H_(DEGREE+2) = 1`:
/// within `2^−123` of `e^x − 1` (`formal/expm1/accurate_level_*.g`,
/// `accurate_small.g`).
fn small_accurate(x: f64) -> Q128 {
    let xq = Q128::from_f64(x);
    let mut h = Q128::ONE;
    for m in (2..=DEGREE + 1).rev() {
        let (r, e) = RECIPROCALS[m - 2];
        h = Q128::ONE.add(xq.mul(Q128::new(false, r, e)).mul(h));
    }
    xq.mul(h)
}

/// §5: `(Y − 2^−k)·2^k` from `exp`'s fast path, within `2^−62` of `e^x − 1` for
/// `|x| ≥ 2^−5` (`formal/expm1/fast_general.g`). The scaling is exact.
fn general_fast(reduced: &Reduced) -> DoubleWord {
    let k = reduced.k;
    let m = reduced.fast_value().add_f64(-pow2(-k));
    DoubleWord::sum(scale(m.hi(), k), scale(m.lo(), k))
}

/// §5: `exp`'s accurate `e^x`, less 1, in `Q128`: within `2^−118` of `e^x − 1`
/// (`formal/expm1/accurate_general.g`).
fn general_accurate(reduced: &Reduced) -> Q128 {
    reduced.accurate_value().add(Q128::from_f64(-1.0))
}

/// `2^e` for `−1074 ≤ e ≤ 1023`, from its encoding.
fn pow2(e: i32) -> f64 {
    if e >= -1022 {
        #[allow(clippy::cast_sign_loss)] // e + 1023 >= 1
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        #[allow(clippy::cast_sign_loss)] // e + 1074 >= 0
        f64::from_bits(1 << ((e + 1074) as u32))
    }
}

#[cfg(test)]
mod tests;
