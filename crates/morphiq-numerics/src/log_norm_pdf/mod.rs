//! `log_norm_pdf`: the logarithm of the standard normal density.
//!
//! The contract, the derivation and every bound are in
//! [`docs/log_norm_pdf.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/log_norm_pdf.md);
//! section and decision numbers below refer to it.

mod tables;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord;
use crate::ulp::ulp;
use tables::{C_HI, C_LO};

/// `2^−27`: below it the result is `−C_HI` (§2).
const TWO_M27: f64 = f64::from_bits(0x3e40_0000_0000_0000);
/// `2^500`: the top of regime M, where `two_prod(a, a/2)` stays in its domain (§3).
const TWO_500: f64 = f64::from_bits(0x5f30_0000_0000_0000);
/// `2^513`: from here `a²/2 ≥ 2^1025`, and the result overflows (§1).
const TWO_513: f64 = f64::from_bits(0x6000_0000_0000_0000);
/// `2^−16` and `2^32`: regime L's scaling of `a` and of the result (§4).
const TWO_M16: f64 = f64::from_bits(0x3ef0_0000_0000_0000);
const TWO_32: f64 = f64::from_bits(0x41f0_0000_0000_0000);

/// `ln φ(x) = −x²/2 − ln √(2π)`, the logarithm of the standard normal density:
/// correctly rounded wherever the rounding test of §3 decides it, and
/// otherwise within `(1/2 + 2^−50)` ulp (decision 1).
///
/// A NaN is returned unchanged; `±∞` and `|x| ≥ 2^513` give `−∞`. The result
/// depends on `|x|` only, and every finite result is at most
/// `−0.9189385332046728`, `RN(−ln √(2π))`.
#[must_use]
pub fn log_norm_pdf(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    let a = x.abs();
    if a < TWO_M27 {
        // §2: x²/2 cannot move ln √(2π) past a rounding midpoint.
        return -C_HI;
    }
    if a >= TWO_513 {
        return f64::NEG_INFINITY;
    }
    if a <= TWO_500 {
        // §3: Z = a²/2 + C as a double-word; Z_hi = RN(Z) is RN(S) wherever
        // the rounding test decides, and within (1/2 + 2^−50) ulp otherwise.
        let z = DoubleWord::product(a, a * 0.5).add(DoubleWord::sum(C_HI, C_LO));
        return -z.hi();
    }
    // §4: a²/2 = 2^32·(h + l) exactly; C only breaks a tie, away from zero.
    let scaled = a * TWO_M16;
    let square = DoubleWord::product(scaled, scaled * 0.5);
    let (h, l) = (square.hi(), square.lo());
    let r = if l == ulp(h) * 0.5 { h + ulp(h) } else { h };
    -(r * TWO_32)
}
