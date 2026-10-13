//! `expm1`'s small polynomial and exponential stages, operation for operation.

use morphiq_numerics_arch::Simd;

use super::stages::{E_A, E_B, SUBTRACTION_ERROR};
use super::{EPS, SMALL, TINY, expm1};
use crate::exp::lanes::{reduce, stage_a, stage_b};
use crate::lanes::{
    Dw, Kernel, add_dw, add_f64, decide, decide_relative, lanes_mask, mask_from, two_prod, two_sum,
};

pub(crate) struct Expm1;

impl Kernel for Expm1 {
    fn scalar(x: f64) -> f64 {
        expm1(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let xv = k.load(x);
        let magnitude = k.abs(xv);
        let tiny = k.mask_bits(k.lt(magnitude, k.splat(TINY)));
        let small = k.and_m(
            k.le(k.splat(TINY), magnitude),
            k.lt(magnitude, k.splat(SMALL)),
        );
        let general = k.and_m(
            k.and_m(
                k.le(k.splat(SMALL), magnitude),
                k.lt(magnitude, k.splat(704.0)),
            ),
            k.lt(k.splat(-37.0), xv),
        );
        let mut value = xv;
        let mut decided = tiny;
        if k.mask_bits(small) != 0 {
            // Inactive lanes use an in-domain placeholder before two_prod.
            let y = small_fast(k, k.select(small, xv, k.splat(1.0 / 64.0)));
            let accepted = small_decide(k, y) & k.mask_bits(small);
            value = k.select(mask_from(k, accepted), y.0, value);
            decided |= accepted;
        }
        let open = k.mask_bits(general);
        if open != 0 {
            let input = k.store(k.select(general, xv, k.splat(1.0)));
            let r = reduce(k, &input);
            let inverse = inverse_scale(k, r.table.scale);
            let (mut low, a) = subtract(k, stage_a(k, &r), inverse, E_A);
            let mut accepted = a & open;
            if open & !accepted != 0 {
                let (b, b_ok) = subtract(k, stage_b(k, &r), inverse, E_B);
                let take = open & !accepted & b_ok;
                low = k.select(mask_from(k, take), b, low);
                accepted |= take;
            }
            value = k.select(mask_from(k, accepted), k.mul(low, r.table.scale), value);
            decided |= accepted;
        }
        let mut out = k.store(value);
        if decided != lanes_mask::<K>() {
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = expm1(x.as_ref()[i]);
                }
            }
        }
        out
    }
}

/// For normal 2^e and 2^-e, subtracting biased exponents gives 2^-e exactly.
#[inline(always)]
fn inverse_scale<K: Simd>(k: K, scale: K::F) -> K::F {
    k.to_float(k.sub_u(k.splat_bits(2046 << 52), k.to_bits(scale)))
}

#[inline(always)]
fn parts<K: Simd>(k: K, y: Dw<K>, inverse: K::F, base: f64) -> (K::F, K::F, K::F) {
    let (s, e) = two_sum(k, y.0, k.neg(inverse));
    let lo = k.add(e, y.1);
    let eps = k.add(
        k.splat(base),
        k.mul(k.add(k.abs(e), k.abs(y.1)), k.splat(SUBTRACTION_ERROR)),
    );
    (s, lo, eps)
}

#[inline(always)]
fn subtract<K: Simd>(k: K, y: Dw<K>, inverse: K::F, base: f64) -> (K::F, u64) {
    let (s, lo, eps) = parts(k, y, inverse, base);
    decide(k, (s, lo), eps)
}

#[inline(always)]
fn small_fast<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let [c3, c4, c5, c6, c7, c8, c9] = super::tables::POLY;
    let w8 = k.add(k.splat(c8), k.mul(x, k.splat(c9)));
    let w7 = k.add(k.splat(c7), k.mul(x, w8));
    let w6 = k.add(k.splat(c6), k.mul(x, w7));
    let w5 = k.add(k.splat(c5), k.mul(x, w6));
    let w4 = k.add(k.splat(c4), k.mul(x, w5));
    let w = k.add(k.splat(c3), k.mul(x, w4));
    // 2^-54 <= |x| < 2^-5: x*x >= 2^-108, inside two_prod's proved domain.
    let (sh, sl) = two_prod(k, x, x);
    let t = k.mul(k.mul(x, sh), w);
    let half = two_sum(k, k.mul(k.splat(0.5), sh), k.mul(k.splat(0.5), sl));
    // DoubleWord::from_f64(x).add(half).add_f64(t), in exactly that order.
    add_f64(k, add_dw(k, (x, k.splat(0.0)), half), t)
}

#[inline(always)]
fn small_decide<K: Simd>(k: K, y: Dw<K>) -> u64 {
    decide_relative(k, y, EPS)
}

#[cfg(test)]
mod tests;
