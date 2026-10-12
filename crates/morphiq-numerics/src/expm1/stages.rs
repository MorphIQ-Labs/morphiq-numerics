//! The exponential stages with compensated subtraction of one (§5.1).
//! `formal/exp/Expm1Stages.v` proves the complete screened computation.

use super::pow2;
use crate::eft::two_sum;
use crate::exp::Stages;
use crate::ln::stages::decide;

pub(super) const E_A: f64 = f64::from_bits(0x3c40_0000_0000_0000); // 2^-59
pub(super) const E_B: f64 = f64::from_bits(0x3bb0_0000_0000_0000); // 2^-68
const SUBTRACTION_ERROR: f64 = f64::from_bits(0x3cc0_0000_0000_0000); // 2^-51

#[inline]
pub(crate) fn stages(x: f64) -> Option<f64> {
    if !(x.abs() < 704.0 && x > -37.0 && x.abs() >= super::SMALL) {
        return None;
    }
    let reduced = Stages::of(x);
    #[allow(clippy::cast_possible_truncation)] // the screen proves -54 <= k <= 1016
    let k = reduced.exponent() as i32;
    let (h, l) = reduced.a_value();
    if let Some(y) = subtract(h, l, k, E_A) {
        return Some(y);
    }
    let (h, l) = reduced.b_value();
    subtract(h, l, k, E_B)
}

#[inline]
pub(super) fn subtract(h: f64, l: f64, k: i32, base: f64) -> Option<f64> {
    let (s, lo, eps) = parts(h, l, k, base);
    decide(s, lo, eps).map(|v| v * pow2(k))
}

#[inline]
pub(super) fn parts(h: f64, l: f64, k: i32, base: f64) -> (f64, f64, f64) {
    let (s, e) = two_sum(h, -pow2(-k));
    let lo = e + l;
    let eps = base + (e.abs() + l.abs()) * SUBTRACTION_ERROR;
    (s, lo, eps)
}
