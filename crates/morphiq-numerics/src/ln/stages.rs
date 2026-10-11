//! `ln_1p`'s stages H and B (docs/ln.md, section 7): each returns `RN(ln(1 + x))`
//! when its rounding test proves it, and `None` otherwise. Every operation is
//! one IEEE 754 binary64 operation, in the order written; the proofs in
//! `formal/ln` transcribe this order, so no operation may be reordered or fused.

use super::stage_tables::{B, EL, H, L0, L1, OFF, R, T};
use crate::eft::two_prod;

/// `2^k` for `−1022 ≤ k ≤ 1023`, exactly.
const fn pow2(k: i32) -> f64 {
    #[allow(clippy::cast_sign_loss)] // 1023 + k is between 1 and 2046
    f64::from_bits(((1023 + k) as u64) << 52)
}

/// Stage H's bound `eps = K_H·z² + K2_H·|s| + A_H`: restated from the
/// certificates in `formal/ln` (docs/ln.md, section 7).
pub(super) const K_H: f64 = pow2(-49);
/// See [`K_H`].
pub(super) const K2_H: f64 = pow2(-83);
/// See [`K_H`].
pub(super) const A_H: f64 = pow2(-102);
/// Stage B's bound for `|x| < 2^−9`, `eps = |x|·(K_B·x² + EPS_B_REL)`:
/// restated from the certificates in `formal/ln`.
pub(super) const K_B: f64 = pow2(-51);
/// See [`K_B`].
pub(super) const EPS_B_REL: f64 = pow2(-102);
/// Stage B's absolute bound for `|x| ≥ 2^−9`: restated from the certificates
/// in `formal/ln`.
pub(super) const EPS_B: f64 = pow2(-78);

/// `bits(2^−46) << 1`, `bits(2^−54) << 1`: the screens' magnitude floors.
const TWO_M46_2X: u64 = pow2(-46).to_bits() << 1;
const TWO_M54_2X: u64 = pow2(-54).to_bits() << 1;
/// `bits(2^53)`, `bits(2^1020)`: the screens' upper limits, as signed words.
#[allow(clippy::cast_possible_wrap)] // below 2^63
const TWO_53_BITS: i64 = pow2(53).to_bits() as i64;
#[allow(clippy::cast_possible_wrap)] // below 2^63
const TWO_1020_BITS: i64 = pow2(1020).to_bits() as i64;
/// `bits(−1)`: a negative `x` is above −1 exactly when its encoding is below.
const MINUS_ONE_BITS: u64 = 0xbff0_0000_0000_0000;
/// `2^−9`, below which stage B takes `z = x`.
const TWO_M9: f64 = pow2(-9);
/// `2^53`, from which `1 + x` splits as `(x, 1)`.
const TWO_53: f64 = pow2(53);

/// Stage H's screen: `2^−46 ≤ |x|` and `−1 < x < 2^53`; false on NaN.
#[inline(always)]
pub(crate) fn stage_h_screen(x: f64) -> bool {
    let b = x.to_bits();
    #[allow(clippy::cast_possible_wrap)] // compared as a signed word
    let signed = b as i64;
    (b << 1) >= TWO_M46_2X && signed < TWO_53_BITS && b < MINUS_ONE_BITS
}

/// Stage B's screen: `2^−54 ≤ |x|` and `−1 < x < 2^1020`; false on NaN.
#[inline(always)]
pub(crate) fn stage_b_screen(x: f64) -> bool {
    let b = x.to_bits();
    #[allow(clippy::cast_possible_wrap)] // compared as a signed word
    let signed = b as i64;
    (b << 1) >= TWO_M54_2X && signed < TWO_1020_BITS && b < MINUS_ONE_BITS
}

/// The reduction shared by both stages: from `h`'s encoding, the exponent `E`,
/// the index `i`, `rs = R[i]·2^−E` and `z = y·R[i] − 1`, exactly, where
/// `h = 2^E·y`.
#[inline(always)]
pub(crate) fn reduce(h: f64) -> (i64, usize, f64, f64) {
    let hb = h.to_bits();
    let u = hb.wrapping_sub(OFF);
    #[allow(clippy::cast_possible_wrap)] // an arithmetic shift of the word
    let e = (u as i64) >> 52;
    #[allow(clippy::cast_possible_truncation)] // 9 bits
    let i = ((u >> 43) & 511) as usize;
    #[allow(clippy::cast_sign_loss)] // the exponent's two's complement
    let rs = f64::from_bits(R[i].wrapping_sub((e as u64) << 52));
    let hh = f64::from_bits(hb & !0x3ff);
    let hl = h - hh;
    let z = (hh * rs - 1.0) + hl * rs;
    (e, i, rs, z)
}

/// Stage H for `x` that passes [`stage_h_screen`]: `(s, lo, eps)` and the
/// test's result.
#[inline(always)]
pub(crate) fn stage_h_parts(x: f64) -> (f64, f64, f64, Option<f64>) {
    let s0 = 1.0 + x;
    let l = x - (s0 - 1.0);
    let (e, i, rs, z) = reduce(s0);
    let (th, tl) = T[i];
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)] // 7 bits
    let (eh, el) = EL[((e + 64) & 127) as usize];
    let ln1 = eh + th;
    let ln0 = el + tl;
    let lr = l * rs;
    let z2 = z * z;
    let t0 = z * H[0] - 0.5;
    let t1 = z * H[2] + H[1];
    let a1 = z2 * H[3] + t1;
    let p = z2 * a1 + t0;
    let q = z2 * p;
    let s = ln1 + z;
    let e1 = z - (s - ln1);
    let pre = e1 + (lr * (1.0 - z) + ln0);
    let lo = pre + q;
    let eps = z2 * K_H + (s.abs() * K2_H + A_H);
    (s, lo, eps, decide(s, lo, eps))
}

/// Stage H: `RN(ln(1 + x))` when its test proves it, for `x` that passes
/// [`stage_h_screen`].
#[inline(always)]
pub(super) fn stage_h(x: f64) -> Option<f64> {
    stage_h_parts(x).3
}

/// `B[0] + z·(B[1] + … + z·B[5])` by Horner's scheme.
#[inline(always)]
fn horner(z: f64) -> f64 {
    let mut acc = B[5];
    acc = z * acc + B[4];
    acc = z * acc + B[3];
    acc = z * acc + B[2];
    acc = z * acc + B[1];
    z * acc + B[0]
}

/// Stage B for `x` that passes [`stage_b_screen`]: `(s, lo, eps)` and the
/// test's result.
pub(crate) fn stage_b_parts(x: f64) -> (f64, f64, f64, Option<f64>) {
    if x.abs() < TWO_M9 {
        let (p, pl) = two_prod(x, x);
        let m = -0.5 * p;
        let s = x + m;
        let e1 = m - (s - x);
        let tail = (x * p) * horner(x);
        let lo = e1 + (-0.5 * pl + tail);
        let eps = x.abs() * (p * K_B + EPS_B_REL);
        return (s, lo, eps, decide(s, lo, eps));
    }
    let big = x >= TWO_53;
    let s0 = 1.0 + x;
    let l0 = x - (s0 - 1.0);
    let h = if big { x } else { s0 };
    let l = if big { 1.0 } else { l0 };
    let (e, i, rs, z) = reduce(h);
    let lr = l * rs;
    #[allow(clippy::cast_precision_loss)] // |E| ≤ 1020
    let ef = e as f64;
    let (th, tl) = T[i];
    let ln1 = ef * L1 + th;
    let ln0 = ef * L0 + tl;
    let (p, pl) = two_prod(z, z);
    let s1 = ln1 + z;
    let e1 = z - (s1 - ln1);
    let m = -0.5 * p;
    let s = s1 + m;
    let e2 = m - (s - s1);
    let zp = z * p;
    let tail = zp * horner(z);
    let lrt = lr * (((1.0 - z) + p) - zp);
    let lo = (e1 + e2) + ((ln0 + lrt) + (-0.5 * pl + tail));
    (s, lo, EPS_B, decide(s, lo, EPS_B))
}

/// Stage B: `RN(ln(1 + x))` when its test proves it, for `x` that passes
/// [`stage_b_screen`].
#[inline(always)]
pub(super) fn stage_b(x: f64) -> Option<f64> {
    stage_b_parts(x).3
}

/// The rounding test: `s + (lo − eps)` when it equals `s + (lo + eps)`.
#[inline(always)]
pub(crate) fn decide(s: f64, lo: f64, eps: f64) -> Option<f64> {
    let lb = s + (lo - eps);
    let ub = s + (lo + eps);
    #[allow(clippy::float_cmp)] // the test is equality
    (lb == ub).then_some(lb)
}
