//! `exp` on lanes ([`docs/lanes.md`] §4): `exp`'s screen, `Stages::of`, and
//! stages A and B with their rounding tests, operation for operation, with
//! `exp` itself on every lane they don't decide.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{INV_N, POLY_S, S_L1, S_L2, S_L2D, S_L3, S_T, SHIFTER};
use super::{E_A, E_B, HIGH_21, SPLIT, exp};
use crate::lanes::{Dw, Kernel, fast_two_sum};

/// `exp` as a lane kernel.
pub(crate) struct Exp;

impl Kernel for Exp {
    fn scalar(x: f64) -> f64 {
        exp(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let reduced = reduce(k, &x);
        let open = lanes_mask::<K>() & !reduced.screened;
        // Stage A on every lane; stage B only when a lane needs it.
        let (mut low, decided_a) = decide(k, stage_a(k, &reduced), E_A);
        let mut decided = decided_a & open;
        if open & !decided != 0 {
            let (low_b, decided_b) = decide(k, stage_b(k, &reduced), E_B);
            let take_b = open & !decided & decided_b;
            low = k.select(mask_from(k, take_b), low_b, low);
            decided |= take_b;
        }
        // The scaling: an exact product by 2^k, the value the scalar code
        // forms by adding k to the exponent field (§4; docs/exp.md §7).
        let mut out = k.store(k.mul(low, reduced.scale));
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if decided >> i & 1 == 0 {
                *o = exp(x.as_ref()[i]);
            }
        }
        out
    }
}

/// Bits `0..LANES` set.
#[inline(always)]
fn lanes_mask<K: Simd>() -> u64 {
    (1_u64 << K::LANES) - 1
}

/// The lane mask with lane `i` true when bit `i` of `bits` is set.
#[inline(always)]
fn mask_from<K: Simd>(k: K, bits: u64) -> K::M {
    let mut words = K::Words::default();
    for (i, w) in words.as_mut().iter_mut().enumerate() {
        *w = bits >> i & 1;
    }
    k.eq_u(k.load_bits(words), k.splat_bits(1))
}

/// `Stages::of` on every lane, with the table pair and `2^k` loaded per lane.
pub(super) struct Reduced<K: Simd> {
    n: K::F,
    r1: K::F,
    t_hi: K::F,
    t_lo: K::F,
    scale: K::F,
    /// The lanes (bit `i` set) that `exp`'s screen sends to the fallback.
    pub(super) screened: u64,
}

#[inline(always)]
pub(super) fn reduce<K: Simd>(k: K, x: &K::Array) -> Reduced<K> {
    let xv = k.load(*x);
    // The screen, |x| < 704: an ordered comparison, false for NaN as the
    // encoding comparison is.
    let screened = !k.mask_bits(k.lt(k.abs(xv), k.splat(704.0))) & lanes_mask::<K>();
    let t = k.add(k.mul(xv, k.splat(INV_N)), k.splat(SHIFTER));
    let n = k.sub(t, k.splat(SHIFTER));
    let t_lanes = k.store(t);
    let (mut t_hi, mut t_lo, mut scale) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for i in 0..K::LANES {
        // As `Stages::of`: n from the shifter's encoding; a screened lane
        // takes n = 0 and is discarded.
        #[allow(clippy::cast_possible_wrap)] // both encodings are below 2^63
        let n_int = if screened >> i & 1 == 1 {
            0
        } else {
            t_lanes.as_ref()[i].to_bits() as i64 - SHIFTER.to_bits() as i64
        };
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // in [0, 512)
        let j = (n_int & 511) as usize;
        let (hi, lo) = S_T[j];
        t_hi.as_mut()[i] = f64::from_bits(hi);
        t_lo.as_mut()[i] = f64::from_bits(lo);
        // 2^k, |k| ≤ 1016 past the screen (docs/exp.md §3).
        #[allow(clippy::cast_sign_loss)] // in [7, 2039]
        let biased = ((n_int >> 9) + 1023) as u64;
        scale.as_mut()[i] = f64::from_bits(biased << 52);
    }
    Reduced {
        n,
        r1: k.sub(xv, k.mul(n, k.splat(S_L1))),
        t_hi: k.load(t_hi),
        t_lo: k.load(t_lo),
        scale: k.load(scale),
        screened,
    }
}

/// `Stages::a_value` on every lane.
#[inline(always)]
pub(super) fn stage_a<K: Simd>(k: K, s: &Reduced<K>) -> Dw<K> {
    let r = k.sub(s.r1, k.mul(s.n, k.splat(S_L2D)));
    let [d3, d4, d5] = POLY_S;
    let p = k.add(
        k.splat(d3),
        k.mul(r, k.add(k.splat(d4), k.mul(r, k.splat(d5)))),
    );
    let u = k.add(r, k.mul(k.mul(r, r), k.add(k.splat(0.5), k.mul(r, p))));
    (s.t_hi, k.add(s.t_lo, k.mul(s.t_hi, u)))
}

/// `Stages::b_value` on every lane.
#[inline(always)]
pub(super) fn stage_b<K: Simd>(k: K, s: &Reduced<K>) -> Dw<K> {
    let p2 = k.mul(s.n, k.splat(S_L2));
    let r0 = k.sub(s.r1, p2);
    let r_h = k.sub(k.add(r0, k.splat(SPLIT)), k.splat(SPLIT));
    let r_t = k.sub(k.sub(k.sub(s.r1, r_h), p2), k.mul(s.n, k.splat(S_L3)));
    let r_hi = k.add(r_h, r_t);
    let [d3, d4, d5] = POLY_S;
    let p = k.add(
        k.splat(d3),
        k.mul(r_hi, k.add(k.splat(d4), k.mul(r_hi, k.splat(d5)))),
    );
    let q = k.mul(k.mul(r_hi, r_hi), k.add(k.splat(0.5), k.mul(r_hi, p)));
    let (th, tl) = (s.t_hi, s.t_lo);
    let a = k.to_float(k.and_u(k.to_bits(th), k.splat_bits(HIGH_21)));
    let rest = k.add(
        tl,
        k.add(
            k.mul(tl, r_hi),
            k.add(k.mul(k.sub(th, a), r_h), k.mul(th, k.add(r_t, q))),
        ),
    );
    let (y, e) = fast_two_sum(k, th, k.mul(a, r_h));
    (y, k.add(e, rest))
}

/// `decide` on every lane, before its scaling: `RN(y + RN(l − e))`, and the
/// lanes where it equals `RN(y + RN(l + e))`. On an unscreened lane both are
/// positive normal numbers (`y + l` lies near `[1, 2]`), so equal encodings
/// are equal numbers, as the scalar `==` tests.
#[inline(always)]
fn decide<K: Simd>(k: K, y: Dw<K>, e: f64) -> (K::F, u64) {
    let low = k.add(y.0, k.sub(y.1, k.splat(e)));
    let high = k.add(y.0, k.add(y.1, k.splat(e)));
    (low, k.mask_bits(k.eq_u(k.to_bits(low), k.to_bits(high))))
}

#[cfg(test)]
mod tests;
