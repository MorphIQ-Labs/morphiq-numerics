//! `exp2`: `2^x` rounded to nearest, ties to even.
//!
//! The derivation is in
//! [`docs/exp2.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp2.md);
//! section numbers below refer to it. The reduction is `exp`'s with `ln 2`
//! factored out, and both paths after it are `exp`'s.

mod tables;

use crate::double_word::DoubleWord;
use crate::eft::two_prod;
use crate::exp::{accurate_at, decide_scaled, fast_at};
use crate::q128::Q128;
use tables::{LN2_HI, LN2_LO, LN2_Q128};

/// `1024`: from here `2^x` rounds to `+∞` (§1; the reference fixture's
/// threshold "least x overflowing").
const X_OVERFLOW: f64 = f64::from_bits(0x4090_0000_0000_0000);
/// `−1075`: to here `2^x` rounds to `+0` (§1; "largest x rounding to 0").
const X_ZERO: f64 = f64::from_bits(0xc090_cc00_0000_0000);
/// Between these, `2^x` rounds to 1 (§1; "least negative x rounding to 1" and
/// "least positive x above 1").
const ONE_LOW: f64 = f64::from_bits(0xbc97_1547_652b_82fe);
const ONE_HIGH: f64 = f64::from_bits(0x3ca7_1547_652b_82fe);
/// `1.5 · 2^52`: adding and subtracting it rounds to the nearest integer.
const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);
/// `128` and `1/128`.
const N: f64 = 128.0;
const INV_N: f64 = 0.007_812_5;

/// `2^x`, correctly rounded: the binary64 number nearest to `2^x`, ties to
/// even, for every binary64 `x`, subnormal results included. `2^n` is exact
/// for every integer `n` where it is representable.
///
/// `exp2(NaN)` is NaN, `exp2(+∞) = +∞` and `exp2(−∞) = +0`.
#[must_use]
pub fn exp2(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x >= X_OVERFLOW {
        return f64::INFINITY;
    }
    if x <= X_ZERO {
        return 0.0;
    }
    if (ONE_LOW..ONE_HIGH).contains(&x) {
        return 1.0;
    }
    let reduced = Reduced::of(x);
    if reduced.k >= -1021
        && let Some(y) = decide_scaled(reduced.fast_value(), reduced.k)
    {
        return y;
    }
    reduced.accurate_value().to_f64()
}

/// The reduction of §2: `x = k + j/128 + r`, `|r| ≤ 1/256`, `r` exact.
struct Reduced {
    j: usize,
    k: i32,
    r: f64,
}

impl Reduced {
    fn of(x: f64) -> Self {
        let n = (x * N + SHIFTER) - SHIFTER;
        // |n| ≤ 137,600, so the conversion is exact.
        #[allow(clippy::cast_possible_truncation)]
        let n_int = n as i32;
        #[allow(clippy::cast_sign_loss)] // rem_euclid is in [0, 128)
        let j = n_int.rem_euclid(128) as usize;
        Self {
            j,
            k: n_int.div_euclid(128),
            r: x - n * INV_N,
        }
    }

    /// §3: `r·ln 2` as a double-word, within `2^−113` of the exact product
    /// (`formal/exp2/reduction.g`), then `exp`'s fast path: within `2^−69` of
    /// `2^(j/128 + r)`.
    fn fast_value(&self) -> DoubleWord {
        let (p, e) = two_prod(self.r, LN2_HI);
        fast_at(DoubleWord::sum(p, e + self.r * LN2_LO), self.j)
    }

    /// §4: `r·ln 2` in `Q128`, then `exp`'s accurate path: `2^x` within
    /// `2^−123.9`.
    fn accurate_value(&self) -> Q128 {
        let (m, e) = LN2_Q128;
        let r_ln2 = Q128::from_f64(self.r).mul(Q128::new(false, m, e));
        accurate_at(r_ln2, self.j, self.k)
    }
}

#[cfg(test)]
mod tests;
