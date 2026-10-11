//! `exp` on lanes ([`docs/lanes.md`] §4): `exp`'s screen, the reduction of
//! `Reduced::of`, `fast_at` and `decide_scaled`, operation for operation, with
//! `exp` itself on every lane they don't decide.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{INV_L, L1, L2, L3, POLY, SHIFTER, T_BITS};
use super::{EPS, ONE_HIGH, ONE_LOW, X_OVERFLOW, X_ZERO, exp};
use crate::lanes::{Dw, Kernel, decide, dw_add, dw_add_f64, dw_mul, two_prod, two_sum};

/// `exp` as a lane kernel.
pub(crate) struct Exp;

impl Kernel for Exp {
    fn scalar(x: f64) -> f64 {
        exp(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let (y, scale, scalar_lanes) = fast(k, &x);
        // decide_scaled: y_hi > 0 here, so |y_hi| is y_hi.
        let decided = k.mask_bits(decide(k, y, EPS)) & !scalar_lanes;
        let mut out = k.store(k.mul(y.0, scale));
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if decided >> i & 1 == 0 {
                *o = exp(x.as_ref()[i]);
            }
        }
        out
    }
}

/// `exp`'s fast value on every lane: `Y` as `fast_at` computes it after
/// `Reduced::of`, the scale `2^k`, and the lanes (bit `i` set) that `exp`
/// screens out or doesn't try the fast path on.
#[inline(always)]
pub(super) fn fast<K: Simd>(k: K, x: &K::Array) -> (Dw<K>, K::F, u64) {
    let xv = k.load(*x);
    // Reduced::of, steps 1 and 2: n = RN_int(x·INV_L).
    let n = k.sub(
        k.add(k.mul(xv, k.splat(INV_L)), k.splat(SHIFTER)),
        k.splat(SHIFTER),
    );
    let n_lanes = k.store(n);
    // Per lane: exp's screen, the table index j and the scale 2^k.
    let (mut t_hi, mut t_lo, mut scale) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    let mut scalar_lanes = 0_u64;
    for i in 0..K::LANES {
        let xi = x.as_ref()[i];
        let special =
            xi.is_nan() || xi >= X_OVERFLOW || xi <= X_ZERO || (ONE_LOW..ONE_HIGH).contains(&xi);
        // |n| < 2^18 past the screen (§3, step 2), so the conversion is
        // exact; a screened lane takes n = 0 and is discarded.
        #[allow(clippy::cast_possible_truncation)]
        let n_int = if special {
            0
        } else {
            n_lanes.as_ref()[i] as i32
        };
        #[allow(clippy::cast_sign_loss)] // rem_euclid is in [0, 128)
        let j = n_int.rem_euclid(128) as usize;
        let k_i = n_int.div_euclid(128);
        // `exp` tries the fast path for k ≥ −1021 (docs/exp.md §4, decision 3);
        // k = 1024 scales in two steps there (§5), so it is left to `exp`.
        if special || !(-1021..=1023).contains(&k_i) {
            scalar_lanes |= 1 << i;
        }
        let (hi, lo) = T_BITS[j];
        t_hi.as_mut()[i] = f64::from_bits(hi);
        t_lo.as_mut()[i] = f64::from_bits(lo);
        // pow2(k), as `scale` computes it; any normal power for a
        // discarded lane.
        #[allow(clippy::cast_sign_loss)] // clamped to [1, 2046]
        let biased = (k_i.clamp(-1022, 1023) + 1023) as u64;
        scale.as_mut()[i] = f64::from_bits(biased << 52);
    }
    // Reduced::of, steps 3 and 4.
    let r1 = k.sub(xv, k.mul(n, k.splat(L1)));
    let (p2, e2) = two_prod(k, n, k.splat(L2));
    let (s, t) = two_sum(k, r1, k.neg(p2));
    let rr = k.sub(k.sub(t, e2), k.mul(n, k.splat(L3)));
    let r = two_sum(k, s, rr);
    // fast_at.
    let r_hi = r.0;
    let [c3, c4, c5, c6] = POLY;
    let t5 = k.add(k.splat(c5), k.mul(r_hi, k.splat(c6)));
    let t4 = k.add(k.splat(c4), k.mul(r_hi, t5));
    let t3 = k.add(k.splat(c3), k.mul(r_hi, t4));
    let h = k.add(k.splat(0.5), k.mul(r_hi, t3));
    let q = k.mul(k.mul(r_hi, r_hi), h);
    let p = dw_add_f64(k, r, q);
    let e = dw_add(k, (k.splat(1.0), k.splat(0.0)), p);
    let t_j = two_sum(k, k.load(t_hi), k.load(t_lo));
    (dw_mul(k, t_j, e), k.load(scale), scalar_lanes)
}

#[cfg(test)]
mod tests;
