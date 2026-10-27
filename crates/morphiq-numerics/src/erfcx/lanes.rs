//! Scalar operation sequences on SIMD lanes. Inactive regions receive benign
//! inputs before division, table indexing or any error-free product.
use super::{
    CS, DEG, EPS_N, EPS_T, EPS_Y, PA, Region, T, X_SUB, erfcx, f, pow2, region, special, t_reduce,
};
use crate::lanes::{Dw, Kernel, decide_relative, fast_two_sum, mask_from, two_prod, two_sum};
use morphiq_numerics_arch::Simd;

pub(crate) struct Erfcx;

#[inline(always)]
fn mul<K: Simd>(k: K, a: Dw<K>, b: Dw<K>) -> Dw<K> {
    let (p, e) = two_prod(k, a.0, b.0);
    fast_two_sum(k, p, k.add(e, k.add(k.mul(a.0, b.1), k.mul(a.1, b.0))))
}

#[inline(always)]
pub(crate) fn table<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let words = k.store(x);
    let mut coefficients = [K::Array::default(); 13];
    let mut h = K::Array::default();
    let mut shift = K::Array::default();
    for (i, &x) in words.as_ref().iter().enumerate() {
        let (idx, _, residual, e) = t_reduce(x);
        h.as_mut()[i] = residual;
        shift.as_mut()[i] = f((((1023 + 29 + e) as u64) << 52) | (1 << 51));
        for (a, &bits) in coefficients.iter_mut().zip(&T[idx]) {
            a.as_mut()[i] = f(bits);
        }
    }
    let h = k.load(h);
    let shift = k.load(shift);
    let hh = k.sub(k.add(h, shift), shift);
    let l = k.sub(h, hh);
    // Load only the coefficient being consumed; avoid materializing a second
    // array of vectors through the generic array-map machinery.
    let a = |j: usize| k.load(coefficients[j]);
    let a1 = k.to_float(k.and_u(k.to_bits(a(2)), k.splat_bits(!((1 << 18) - 1))));
    let b1 = k.add(k.sub(a(2), a1), a(3));
    let a2 = k.to_float(k.and_u(k.to_bits(a(4)), k.splat_bits(!((1 << 36) - 1))));
    let b2 = k.add(k.sub(a(4), a2), a(5));
    let p1 = k.mul(a1, hh);
    let sq = k.mul(hh, hh);
    let p2 = k.mul(a2, sq);
    let mut q = a(6 + DEG - 3);
    for j in (6..6 + DEG - 3).rev() {
        q = k.add(a(j), k.mul(h, q));
    }
    let lh = k.mul(l, k.add(h, hh));
    let h2 = k.add(sq, lh);
    let t3 = k.mul(k.mul(h2, h), q);
    let rest = k.add(
        k.add(
            k.add(a(1), k.add(k.mul(a1, l), k.mul(b1, h))),
            k.add(k.mul(a(4), lh), k.mul(b2, sq)),
        ),
        t3,
    );
    let (s, e1) = fast_two_sum(k, a(0), p1);
    let (s2, e2) = fast_two_sum(k, s, p2);
    fast_two_sum(k, s2, k.add(k.add(e1, e2), rest))
}

#[inline(always)]
pub(crate) fn asymptotic<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let yh = k.div(k.splat(1.0), x);
    let (p, pe) = two_prod(k, x, yh);
    let yl = k.mul(k.sub(k.sub(k.splat(1.0), p), pe), yh);
    let (th, tl0) = two_prod(k, yh, yh);
    let tl = k.add(tl0, k.mul(k.mul(k.splat(2.0), yh), yl));
    let mut pp = k.splat(f(PA[PA.len() - 1]));
    for j in (0..PA.len() - 1).rev() {
        pp = k.add(k.splat(f(PA[j])), k.mul(th, pp));
    }
    let (w, ew) = fast_two_sum(k, k.splat(1.0), k.mul(k.splat(-0.5), th));
    let v = k.mul(k.mul(th, k.add(th, k.mul(k.splat(2.0), tl))), pp);
    let (w, e3) = fast_two_sum(k, w, v);
    let wl = k.add(e3, k.sub(ew, k.mul(k.splat(0.5), tl)));
    let z = mul(k, (k.splat(f(CS.0)), k.splat(f(CS.1))), (yh, yl));
    mul(k, z, (w, wl))
}

#[inline(always)]
fn reciprocal<K: Simd>(k: K, x: K::F) -> (Dw<K>, K::F) {
    let large = k.lt(k.splat(1e270), x);
    let scale = k.select(large, k.splat(pow2(-600)), k.splat(1.0));
    let xs = k.mul(x, scale);
    let ch = k.splat(f(CS.0));
    let q = k.div(ch, xs);
    let (p, pe) = two_prod(k, q, xs);
    let r = k.add(k.sub(k.sub(ch, p), pe), k.splat(f(CS.1)));
    let ql = k.div(r, xs);
    let y = k.div(k.splat(1.0), k.select(large, k.splat(512.0), x));
    let t = k.mul(y, y);
    let u = k.mul(
        t,
        k.add(
            k.splat(-0.5),
            k.mul(t, k.sub(k.splat(0.75), k.mul(k.splat(1.875), t))),
        ),
    );
    let tail = k.select(large, ql, k.add(ql, k.mul(q, u)));
    (fast_two_sum(k, q, tail), scale)
}

#[inline(always)]
fn reflected<K: Simd>(k: K, x: K::F) -> (Dw<K>, K::Array) {
    let (s, se) = two_prod(k, x, x);
    let (y, n) = crate::exp::lanes::stage_b_double_word(k, s, se);
    let mut scales = K::Array::default();
    let mut exponents = K::Array::default();
    let mut reflect = 0;
    for (i, &n) in k.store(n).as_ref().iter().enumerate() {
        let exponent = (n as i32).div_euclid(512);
        exponents.as_mut()[i] = f64::from(exponent + 1);
        scales.as_mut()[i] = pow2(-(exponent + 1));
        if exponent <= 104 {
            reflect |= 1 << i;
        }
    }
    if reflect == 0 {
        return (y, exponents);
    }
    let positive = k.select(mask_from(k, reflect), k.neg(x), k.splat(1.0));
    // Only k <= 104 lanes reflect, so their positive arguments are < 9.
    let g = table(k, positive);
    let sc = k.load(scales);
    let (dh, dl) = two_sum(k, y.0, k.neg(k.mul(g.0, sc)));
    let v = fast_two_sum(k, dh, k.add(dl, k.sub(y.1, k.mul(g.1, sc))));
    let mask = mask_from(k, reflect);
    (
        (k.select(mask, v.0, y.0), k.select(mask, v.1, y.1)),
        exponents,
    )
}

/// The common homogeneous chunk returns directly; only undecided lanes
/// leave the vector path.
#[inline(always)]
fn finish<K: Simd>(k: K, input: &K::Array, y: Dw<K>, scale: K::F, eps: f64) -> K::Array {
    let decided = decide_relative(k, y, eps);
    let mut out = k.store(k.mul(y.0, scale));
    if decided != (1 << K::LANES) - 1 {
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if decided >> i & 1 == 0 {
                *o = super::accurate::accurate(input.as_ref()[i]).to_f64();
            }
        }
    }
    out
}

#[inline(always)]
fn finish_reciprocal<K: Simd>(k: K, input: &K::Array) -> K::Array {
    let x = k.load(*input);
    let (y, scale) = reciprocal(k, x);
    let mut candidate = k.mul(y.0, scale);
    let subnormal = k.mask_bits(k.le(k.splat(X_SUB), x));
    if subnormal == 0 {
        return finish(k, input, y, scale, EPS_Y);
    }
    let normal_decided = decide_relative(k, y, EPS_Y) & !subnormal;
    let residual = k.add(k.sub(y.0, k.mul(candidate, k.splat(pow2(600)))), y.1);
    let active = mask_from(k, subnormal);
    let above = k.and_m(active, k.lt(k.splat(pow2(-475)), residual));
    let below = k.and_m(active, k.lt(residual, k.splat(-pow2(-475))));
    candidate = k.select(
        above,
        k.to_float(k.sub_u(k.to_bits(candidate), k.splat_bits(u64::MAX))),
        candidate,
    );
    candidate = k.select(
        below,
        k.to_float(k.sub_u(k.to_bits(candidate), k.splat_bits(1))),
        candidate,
    );
    let distance = k.abs(k.add(k.sub(y.0, k.mul(candidate, k.splat(pow2(600)))), y.1));
    let tiny_decided = k.mask_bits(k.lt(
        k.add(distance, k.mul(k.splat(EPS_Y), y.0)),
        k.splat(pow2(-475)),
    )) & subnormal;
    let decided = normal_decided | tiny_decided;
    let mut out = k.store(candidate);
    if decided != (1 << K::LANES) - 1 {
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if decided >> i & 1 == 0 {
                *o = super::accurate::accurate(input.as_ref()[i]).to_f64();
            }
        }
    }
    out
}

impl Kernel for Erfcx {
    fn scalar(x: f64) -> f64 {
        erfcx(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let xv = k.load(x);
        let all = (1 << K::LANES) - 1;
        let table_mask = k.and_m(k.le(k.splat(-0.5), xv), k.lt(xv, k.splat(16.0)));
        let ones = k.and_m(
            k.le(k.splat(super::ONE_NEG), xv),
            k.le(xv, k.splat(super::ONE_POS)),
        );
        if k.mask_bits(table_mask) == all && k.mask_bits(ones) == 0 {
            return finish(k, &x, table(k, xv), k.splat(1.0), EPS_T);
        }
        if k.mask_bits(k.and_m(k.le(k.splat(16.0), xv), k.lt(xv, k.splat(512.0)))) == all {
            return finish(k, &x, asymptotic(k, xv), k.splat(1.0), EPS_Y);
        }
        if k.mask_bits(k.and_m(k.le(k.splat(512.0), xv), k.le(xv, k.splat(f64::MAX)))) == all {
            return finish_reciprocal(k, &x);
        }
        if k.mask_bits(k.and_m(k.lt(k.splat(super::X_OVF), xv), k.lt(xv, k.splat(-0.5)))) == all {
            let (y, exponents) = reflected(k, xv);
            let decided = decide_relative(k, y, EPS_N);
            let mut out = k.store(y.0);
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = super::accurate::accurate(x.as_ref()[i]).to_f64();
                } else {
                    let exponent = exponents.as_ref()[i] as i32;
                    *o = if exponent > 1023 {
                        *o * pow2(exponent - 1023) * pow2(1023)
                    } else {
                        *o * pow2(exponent)
                    };
                }
            }
            return out;
        }
        // A mixed two-lane chunk has no region with two active lanes.
        if K::LANES == 2 {
            let mut out = x;
            for o in out.as_mut() {
                *o = erfcx(*o);
            }
            return out;
        }
        let mut out = K::Array::default();
        let mut masks = [0u64; 4];
        for (i, &v) in x.as_ref().iter().enumerate() {
            if let Some(y) = special(v) {
                out.as_mut()[i] = y;
            } else {
                masks[match region(v) {
                    Region::T => 0,
                    Region::YA => 1,
                    Region::YB => 2,
                    Region::N => 3,
                }] |= 1 << i;
            }
        }
        let input = k.load(x);
        for (r, &mask) in masks.iter().enumerate() {
            if mask == 0 {
                continue;
            }
            if mask.count_ones() == 1 {
                let i = mask.trailing_zeros() as usize;
                out.as_mut()[i] = erfcx(x.as_ref()[i]);
                continue;
            }
            let x = k.select(
                mask_from(k, mask),
                input,
                k.splat([1.0, 16.0, 512.0, -1.0][r]),
            );
            if r == 2 {
                let values = finish_reciprocal(k, &k.store(x));
                for (i, o) in out.as_mut().iter_mut().enumerate() {
                    if mask >> i & 1 != 0 {
                        *o = values.as_ref()[i];
                    }
                }
                continue;
            }
            let (value, scale, exponents, eps) = match r {
                0 => (table(k, x), k.splat(1.0), K::Array::default(), EPS_T),
                1 => (asymptotic(k, x), k.splat(1.0), K::Array::default(), EPS_Y),
                2 => {
                    let (y, s) = reciprocal(k, x);
                    (y, s, K::Array::default(), EPS_Y)
                }
                _ => {
                    let (y, e) = reflected(k, x);
                    (y, k.splat(1.0), e, EPS_N)
                }
            };
            let decided = decide_relative(k, value, eps) & mask;
            let values = k.store(k.mul(value.0, scale));
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if mask >> i & 1 == 0 {
                    continue;
                }
                *o = if decided >> i & 1 == 0 {
                    super::accurate::accurate(k.store(input).as_ref()[i]).to_f64()
                } else if r == 3 {
                    let exponent = exponents.as_ref()[i] as i32;
                    let y = values.as_ref()[i];
                    if exponent > 1023 {
                        y * pow2(exponent - 1023) * pow2(1023)
                    } else {
                        y * pow2(exponent)
                    }
                } else {
                    values.as_ref()[i]
                };
            }
        }
        out
    }
}
