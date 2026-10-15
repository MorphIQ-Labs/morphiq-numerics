//! Stage B's value, retaining both words for composed kernels.
use morphiq_numerics_arch::Simd;

use crate::lanes::{Dw, two_prod};
use crate::ln::stage_tables::{B, L0, L1, OFF, R, T};

#[inline(always)]
fn horner<K: Simd>(k: K, z: K::F) -> K::F {
    let mut p = k.splat(B[5]);
    for &c in B[..5].iter().rev() {
        p = k.add(k.mul(z, p), k.splat(c));
    }
    p
}

/// `stages::stage_b_parts`'s first two words for inputs passing its screen.
/// Inactive regions are masked before their error-free products.
#[inline(always)]
pub(crate) fn value<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let small = k.lt(k.abs(x), k.splat(f64::from_bits(0x3f60_0000_0000_0000)));
    let all = (1 << K::LANES) - 1;
    let small_bits = k.mask_bits(small);
    let mut result = (k.splat(0.0), k.splat(0.0));
    if small_bits != 0 {
        let z = k.select(small, x, k.splat(0.001));
        let (p, pl) = two_prod(k, z, z);
        let m = k.mul(k.splat(-0.5), p);
        let s = k.add(z, m);
        let e1 = k.sub(m, k.sub(s, z));
        let tail = k.mul(k.mul(z, p), horner(k, z));
        result = (s, k.add(e1, k.add(k.mul(k.splat(-0.5), pl), tail)));
    }
    if small_bits == all {
        return result;
    }
    let x = k.select(small, k.splat(0.25), x);
    let big = k.le(k.splat(super::TWO_53), x);
    let s0 = k.add(k.splat(1.0), x);
    let l0 = k.sub(x, k.sub(s0, k.splat(1.0)));
    let h = k.select(big, x, s0);
    let l = k.select(big, k.splat(1.0), l0);
    let hb = k.to_bits(h);
    let u = k.sub_u(hb, k.splat_bits(OFF));
    let words = k.store(k.to_float(u));
    let (mut ef, mut r, mut th, mut tl) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for (lane, word) in words.as_ref().iter().enumerate() {
        let u = word.to_bits();
        #[allow(clippy::cast_possible_truncation)] // nine bits
        let i = ((u >> 43) & 511) as usize;
        #[allow(clippy::cast_possible_wrap, clippy::cast_precision_loss)] // signed 12-bit exponent
        {
            ef.as_mut()[lane] = ((u as i64) >> 52) as f64;
        }
        r.as_mut()[lane] = f64::from_bits(R[i]);
        (th.as_mut()[lane], tl.as_mut()[lane]) = T[i];
    }
    let rs = k.to_float(k.sub_u(
        k.to_bits(k.load(r)),
        k.and_u(u, k.splat_bits(!super::FRACTION)),
    ));
    let hh = k.to_float(k.and_u(hb, k.splat_bits(!0x3ff)));
    let hl = k.sub(h, hh);
    let z = k.add(k.sub(k.mul(hh, rs), k.splat(1.0)), k.mul(hl, rs));
    let lr = k.mul(l, rs);
    let ln1 = k.add(k.mul(k.load(ef), k.splat(L1)), k.load(th));
    let ln0 = k.add(k.mul(k.load(ef), k.splat(L0)), k.load(tl));
    let (p, pl) = two_prod(k, z, z);
    let s1 = k.add(ln1, z);
    let e1 = k.sub(z, k.sub(s1, ln1));
    let m = k.mul(k.splat(-0.5), p);
    let s = k.add(s1, m);
    let e2 = k.sub(m, k.sub(s, s1));
    let zp = k.mul(z, p);
    let tail = k.mul(zp, horner(k, z));
    let lrt = k.mul(lr, k.sub(k.add(k.sub(k.splat(1.0), z), p), zp));
    let lo = k.add(
        k.add(e1, e2),
        k.add(k.add(ln0, lrt), k.add(k.mul(k.splat(-0.5), pl), tail)),
    );
    (k.select(small, result.0, s), k.select(small, result.1, lo))
}
