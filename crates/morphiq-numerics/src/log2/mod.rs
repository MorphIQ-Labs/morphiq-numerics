//! `log2` and `log10`: base-2 and base-10 logarithms rounded to nearest, ties
//! to even.
//!
//! The derivation is in
//! [`docs/log2.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/log2.md);
//! section numbers below refer to it. Both use `ln`'s exact reduction and its
//! certified paths, then scale by `1/ln 2` or `1/ln 10`.

mod tables;

use crate::double_word::DoubleWord;
use crate::ln::{Reduced, decide};
use crate::q128::Q128;
use tables::{INV_LN2_HI, INV_LN2_LO, INV_LN2_Q128, INV_LN10_HI, INV_LN10_LO, INV_LN10_Q128};

/// The special values shared with `ln` (§1), or `None` for a positive finite
/// `x ≠ 1`.
fn special(x: f64) -> Option<f64> {
    if x.is_nan() {
        Some(x)
    } else if x < 0.0 {
        Some(f64::NAN)
    } else if x == 0.0 {
        Some(f64::NEG_INFINITY)
    } else if x == f64::INFINITY {
        Some(x)
    } else if x == 1.0 {
        Some(0.0)
    } else {
        None
    }
}

fn q128((m, e): (u128, i32)) -> Q128 {
    Q128::new(false, m, e)
}

/// `log2 x`, correctly rounded: the binary64 number nearest to the base-2
/// logarithm of `x`, ties to even, for every binary64 `x`. `log2(2^n) = n`
/// exactly.
///
/// `log2(±0) = −∞`, `log2(+∞) = +∞` and `log2(1) = +0`; a NaN, a negative `x`
/// and `−∞` give NaN.
#[must_use]
pub fn log2(x: f64) -> f64 {
    if let Some(y) = special(x) {
        return y;
    }
    let reduced = Reduced::of(x);
    if let Some(v) = decide(log2_fast(&reduced)) {
        return v;
    }
    log2_accurate(&reduced).to_f64()
}

/// §3: `E + (ln y)·(1/ln 2)`, `E` added exactly where nonzero; within `2^−63`
/// of `log2 x` (`formal/log2/fast_log2.g`).
fn log2_fast(reduced: &Reduced) -> DoubleWord {
    let w = reduced
        .ln_y_fast()
        .mul(DoubleWord::sum(INV_LN2_HI, INV_LN2_LO));
    if reduced.e == 0 {
        w
    } else {
        DoubleWord::from_f64(f64::from(reduced.e)).add(w)
    }
}

/// §4: the same in `Q128`; within `2^−122` (`formal/log2/accurate_log2.g`).
fn log2_accurate(reduced: &Reduced) -> Q128 {
    let w = reduced
        .ln_y_accurate(reduced.z_exact())
        .mul(q128(INV_LN2_Q128));
    if reduced.e == 0 {
        w
    } else {
        Q128::from_f64(f64::from(reduced.e)).add(w)
    }
}

/// `log10 x`: correctly rounded whenever the rounding test decides it, and
/// otherwise within `(1/2 + 2^−69)` ulp (§5). `log10(10^n) = n` exactly for
/// `0 ≤ n ≤ 22`.
///
/// `log10(±0) = −∞`, `log10(+∞) = +∞` and `log10(1) = +0`; a NaN, a negative
/// `x` and `−∞` give NaN.
#[must_use]
pub fn log10(x: f64) -> f64 {
    if let Some(y) = special(x) {
        return y;
    }
    let reduced = Reduced::of(x);
    if let Some(v) = decide(log10_fast(&reduced)) {
        return v;
    }
    log10_accurate(&reduced).to_f64()
}

/// §5: `ln x` times `1/ln 10`; within `2^−63` (`formal/log2/fast_log10.g`).
fn log10_fast(reduced: &Reduced) -> DoubleWord {
    reduced
        .fast_value()
        .mul(DoubleWord::sum(INV_LN10_HI, INV_LN10_LO))
}

/// §5: the same in `Q128`; within `2^−122` (`formal/log2/accurate_log10.g`).
fn log10_accurate(reduced: &Reduced) -> Q128 {
    reduced
        .accurate_value(reduced.z_exact())
        .mul(q128(INV_LN10_Q128))
}

#[cfg(test)]
mod tests;
