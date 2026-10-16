//! Natural logarithm's reciprocal stage (docs/ln.md): all arithmetic is
//! binary64, in the order transcribed in formal/ln/LnStage.v.

use super::stage_tables::{H, L0, L1, T};
use super::stages::{A_H, K_H, K2_H, decide, reduce};

/// The normalizer supplies `x = 2^e · y`. Return the approximation, its
/// error bound, and the interval test's decision.
#[inline(always)]
pub(crate) fn parts(e: i32, y: f64) -> (f64, f64, f64, Option<f64>) {
    let (re, i, _, z) = reduce(y);
    #[allow(clippy::cast_precision_loss)] // total exponent is in [-1075, 1025]
    let e = (i64::from(e) + re) as f64;
    let (th, tl) = T[i];
    let ln1 = e * L1 + th;
    let ln0 = e * L0 + tl;
    let z2 = z * z;
    let t0 = z * H[0] - 0.5;
    let t1 = z * H[2] + H[1];
    let a1 = z2 * H[3] + t1;
    let p = z2 * a1 + t0;
    let q = z2 * p;
    let s = ln1 + z;
    let e1 = z - (s - ln1);
    let pre = e1 + ln0;
    let lo = pre + q;
    let eps = z2 * K_H + (s.abs() * K2_H + A_H);
    (s, lo, eps, decide(s, lo, eps))
}
