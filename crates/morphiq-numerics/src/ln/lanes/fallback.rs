//! Shared double-word logarithm fallback, in scalar operation order.
use morphiq_numerics_arch::Simd;

use super::reduce;
use crate::lanes::{Dw, add_dw, add_f64, two_prod, two_sum};
use crate::ln::tables::{LN2_HI, LN2_LO, NEG_LN_R_BITS, POLY, R_BITS};

/// `ln_1p_double_word`: zero or `2^-64 <= |z.hi| <= 0.0078126`, and a
/// normalized low word. Squaring is inside `two_prod`'s proved domain.
#[inline(always)]
pub(super) fn polynomial<K: Simd>(k: K, z: Dw<K>) -> Dw<K> {
    let [c3, c4, c5, c6, c7, c8, c9] = POLY;
    let w8 = k.add(k.splat(c8), k.mul(z.0, k.splat(c9)));
    let w7 = k.add(k.splat(c7), k.mul(z.0, w8));
    let w6 = k.add(k.splat(c6), k.mul(z.0, w7));
    let w5 = k.add(k.splat(c5), k.mul(z.0, w6));
    let w4 = k.add(k.splat(c4), k.mul(z.0, w5));
    let w = k.add(k.splat(c3), k.mul(z.0, w4));
    let (sh, sl) = two_prod(k, z.0, z.0);
    let t = k.mul(k.mul(z.0, sh), w);
    let b = two_sum(k, k.mul(k.splat(-0.5), sh), k.mul(k.splat(-0.5), sl));
    let v = k.sub(t, k.mul(z.0, z.1));
    add_f64(k, add_dw(k, z, b), v)
}

/// The shared reduced `ln y` and full `ln x` fast values.
#[inline(always)]
fn reduced<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let (y, e) = reduce(k, x, 0);
    let words = k.store(y);
    let (mut r, mut nh, mut nl) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for (lane, value) in words.as_ref().iter().enumerate() {
        #[allow(clippy::cast_possible_truncation)] // seven fraction bits
        let i = ((value.to_bits() >> 45) & 127) as usize;
        r.as_mut()[lane] = f64::from_bits(R_BITS[i]);
        let (h, l) = NEG_LN_R_BITS[i];
        nh.as_mut()[lane] = f64::from_bits(h);
        nl.as_mut()[lane] = f64::from_bits(l);
    }
    let (p, q) = two_prod(k, y, k.load(r));
    let z = two_sum(k, k.sub(p, k.splat(1.0)), q);
    let p = polynomial(k, z);
    let n = two_sum(k, k.load(nh), k.load(nl));
    let ly = add_dw(k, n, p);
    let el = two_sum(k, k.mul(e, k.splat(LN2_HI)), k.mul(e, k.splat(LN2_LO)));
    add_dw(k, el, ly)
}

/// Every lane is a positive finite input other than one.
#[inline(always)]
pub(super) fn ln<K: Simd>(k: K, x: K::F) -> Dw<K> {
    reduced(k, x)
}

/// Every lane is finite, greater than -1, and has magnitude at least 2^-54.
#[inline(always)]
pub(super) fn ln_1p<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let small = k.lt(k.abs(x), k.splat(super::super::TWO_M7));
    let mut value = (k.splat(0.0), k.splat(0.0));
    if k.mask_bits(small) != 0 {
        value = polynomial(k, (k.select(small, x, k.splat(1.0 / 256.0)), k.splat(0.0)));
    }
    if k.mask_bits(small) != crate::lanes::lanes_mask::<K>() {
        let x = k.select(small, k.splat(1.0), x);
        let modest = k.lt(x, k.splat(super::super::TWO_53));
        let (h, l) = two_sum(k, k.splat(1.0), k.select(modest, x, k.splat(1.0)));
        let h = k.select(modest, h, x);
        let l = k.select(modest, l, k.splat(1.0));
        let general = add_f64(k, reduced(k, h), k.div(l, h));
        value = (
            k.select(small, value.0, general.0),
            k.select(small, value.1, general.1),
        );
    }
    value
}
