//! Scalar operation order in lanes, with shared exact integer reduction.
use morphiq_numerics_arch::{Simd, WithSimd};

use super::{
    COS_SMALL, EPS, EPS_TAN, Function, POLY_C, POLY_S, Reduced, SHIFTER, SIN_IS_X, TABLE, TAN_IS_X,
};
use crate::double_word::kernel::DoubleWord;
use crate::lanes::{
    Dw, Kernel, add_dw, add_f64, decide_relative, fast_two_sum, mask_from, mul_dw, two_prod,
    two_sum,
};

pub(crate) const SIN: u8 = 0;
pub(crate) const COS: u8 = 1;
pub(crate) const TAN: u8 = 2;
const PAIR: u8 = 3;

pub(crate) struct Trig<const KIND: u8>;

impl<const KIND: u8> Kernel for Trig<KIND> {
    fn scalar(x: f64) -> f64 {
        match KIND {
            SIN => super::sin(x),
            COS => super::cos(x),
            _ => super::tan(x),
        }
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let reduced = prepare::<K, KIND>(x);
        let (s, c) = fast_pair(k, &reduced);
        let (value, active) = if KIND == TAN {
            tangent(k, s, c, &reduced)
        } else {
            (select(k, s, c, &reduced, KIND == COS), reduced.active)
        };
        let accepted = decision(k, value, if KIND == TAN { EPS_TAN } else { EPS }) & active;
        let mut out = k.store(value.0);
        for (lane, value) in out.as_mut().iter_mut().enumerate() {
            if accepted >> lane & 1 == 0 {
                *value = Self::scalar(x.as_ref()[lane]);
            }
        }
        out
    }
}

struct Reduction<K: Simd> {
    hi: K::Array,
    lo: K::Array,
    odd: u64,
    sin_negative: u64,
    cos_negative: u64,
    tan_negative: u64,
    active: u64,
}

/// Screen before Q256 reduction; inactive lanes evaluate the ordinary 0.5.
#[inline(always)]
fn prepare<K: Simd, const KIND: u8>(input: K::Array) -> Reduction<K> {
    let mut r: Reduction<K> = Reduction {
        hi: K::Array::default(),
        lo: K::Array::default(),
        odd: 0,
        sin_negative: 0,
        cos_negative: 0,
        tan_negative: 0,
        active: 0,
    };
    for (lane, &x) in input.as_ref().iter().enumerate() {
        let active = x.is_finite()
            && match KIND {
                SIN => x.abs() > SIN_IS_X,
                COS => x.abs() >= COS_SMALL,
                TAN => x.abs() > TAN_IS_X,
                _ => x.abs() > SIN_IS_X && x.abs() >= COS_SMALL,
            };
        let reduced = Reduced::of(if active { x } else { 0.5 });
        let hi = reduced.r.to_f64();
        r.hi.as_mut()[lane] = hi;
        r.lo.as_mut()[lane] = reduced.r.add(crate::q256::Q256::from_f64(-hi)).to_f64();
        let (odd, sin_negative) = reduced.select(Function::Sin);
        let (_, cos_negative) = reduced.select(Function::Cos);
        r.active |= u64::from(active) << lane;
        r.odd |= u64::from(odd) << lane;
        r.sin_negative |= u64::from(sin_negative) << lane;
        r.cos_negative |= u64::from(cos_negative) << lane;
        r.tan_negative |= u64::from(odd != reduced.negative) << lane;
    }
    r
}

#[inline(always)]
fn neg<K: Simd>(k: K, x: Dw<K>) -> Dw<K> {
    (k.neg(x.0), k.neg(x.1))
}

#[inline(always)]
fn choose<K: Simd>(k: K, mask: K::M, a: Dw<K>, b: Dw<K>) -> Dw<K> {
    (k.select(mask, a.0, b.0), k.select(mask, a.1, b.1))
}

/// `trig::fast`, including both normalization steps and every rounded sum.
#[inline(always)]
fn fast_pair<K: Simd>(k: K, r: &Reduction<K>) -> (Dw<K>, Dw<K>) {
    let hi = k.load(r.hi);
    let lo = k.load(r.lo);
    let negative = k.lt(hi, k.splat(0.0));
    let hi = k.select(negative, k.neg(hi), hi);
    let lo = k.select(negative, k.neg(lo), lo);
    let i = k.sub(
        k.add(k.mul(hi, k.splat(64.0)), k.splat(SHIFTER)),
        k.splat(SHIFTER),
    );
    let t = two_sum(k, k.sub(hi, k.mul(i, k.splat(0.015_625))), lo);
    let u = two_prod(k, t.0, t.0);
    let ps = k.add(
        k.splat(POLY_S[0]),
        k.mul(
            u.0,
            k.add(k.splat(POLY_S[1]), k.mul(u.0, k.splat(POLY_S[2]))),
        ),
    );
    let pc = k.add(
        k.splat(POLY_C[0]),
        k.mul(
            u.0,
            k.add(k.splat(POLY_C[1]), k.mul(u.0, k.splat(POLY_C[2]))),
        ),
    );
    let sin_t = add_f64(k, t, k.mul(k.mul(t.0, u.0), ps));
    let cos_t_m1 = add_f64(
        k,
        two_sum(k, k.mul(k.splat(-0.5), u.0), k.mul(k.splat(-0.5), u.1)),
        k.sub(k.mul(k.mul(u.0, u.0), pc), k.mul(t.0, t.1)),
    );
    let mut sh = K::Array::default();
    let mut sl = K::Array::default();
    let mut ch = K::Array::default();
    let mut cl = K::Array::default();
    for (lane, &index) in k.store(i).as_ref().iter().enumerate() {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        // reduction proves integer 0 <= index <= 50
        let [(a, b), (c, d)] = TABLE[index as usize];
        sh.as_mut()[lane] = f64::from_bits(a);
        sl.as_mut()[lane] = f64::from_bits(b);
        ch.as_mut()[lane] = f64::from_bits(c);
        cl.as_mut()[lane] = f64::from_bits(d);
    }
    let s = two_sum(k, k.load(sh), k.load(sl));
    let c = two_sum(k, k.load(ch), k.load(cl));
    let sin = add_dw(k, s, add_dw(k, mul_dw(k, s, cos_t_m1), mul_dw(k, c, sin_t)));
    let cos = add_dw(
        k,
        c,
        add_dw(k, mul_dw(k, c, cos_t_m1), neg(k, mul_dw(k, s, sin_t))),
    );
    (choose(k, negative, neg(k, sin), sin), cos)
}

#[inline(always)]
fn select<K: Simd>(k: K, s: Dw<K>, c: Dw<K>, r: &Reduction<K>, cosine: bool) -> Dw<K> {
    let swap = mask_from(k, if cosine { !r.odd } else { r.odd });
    let value = choose(k, swap, c, s);
    let negative = mask_from(
        k,
        if cosine {
            r.cos_negative
        } else {
            r.sin_negative
        },
    );
    choose(k, negative, neg(k, value), value)
}

/// The checked DWDivDW2 arithmetic; rejected lanes divide 1 by 1.
#[inline(always)]
fn tangent<K: Simd>(k: K, s: Dw<K>, c: Dw<K>, r: &Reduction<K>) -> (Dw<K>, u64) {
    let odd = mask_from(k, r.odd);
    let n = choose(k, odd, c, s);
    let d = choose(k, odd, s, c);
    let (nh, nl, dh, dl) = (k.store(n.0), k.store(n.1), k.store(d.0), k.store(d.1));
    let mut active = r.active;
    for lane in 0..K::LANES {
        if !DoubleWord::division_lane_inputs(
            nh.as_ref()[lane],
            nl.as_ref()[lane],
            dh.as_ref()[lane],
            dl.as_ref()[lane],
        ) {
            active &= !(1 << lane);
        }
    }
    let mask = mask_from(k, active);
    let one = (k.splat(1.0), k.splat(0.0));
    let n = choose(k, mask, n, one);
    let d = choose(k, mask, d, one);
    let t_hi = k.div(n.0, d.0);
    // DoubleWord::mul_f64, including its two Fast2Sum normalizations.
    let (p, e) = two_prod(k, d.0, t_hi);
    let (rh, rl) = fast_two_sum(k, p, k.mul(d.1, t_hi));
    let product = fast_two_sum(k, rh, k.add(rl, e));
    let delta = k.add(k.sub(n.0, product.0), k.sub(n.1, product.1));
    let q = fast_two_sum(k, t_hi, k.div(delta, d.0));
    let (qh, ql) = (k.store(q.0), k.store(q.1));
    for lane in 0..K::LANES {
        // Same exact-zero admission as checked_div; no normalization is assumed.
        if nh.as_ref()[lane] == 0.0 && (qh.as_ref()[lane] != 0.0 || ql.as_ref()[lane] != 0.0) {
            active &= !(1 << lane);
        }
    }
    (
        choose(k, mask_from(k, r.tan_negative), neg(k, q), q),
        active,
    )
}

/// An accepted scalar decision has |hi| >= 2^-900 (RoundingDecisionDomain).
/// Screen first so the lane ulp construction only handles normal half-ulps.
#[inline(always)]
fn decision<K: Simd>(k: K, value: Dw<K>, eps: f64) -> u64 {
    let magnitude = k.abs(value.0);
    let domain = k.and_m(
        k.not_m(k.lt(magnitude, k.splat(f64::from_bits(123 << 52)))),
        k.lt(magnitude, k.splat(f64::INFINITY)),
    );
    let screened = choose(k, domain, value, (k.splat(1.0), k.splat(0.0)));
    decide_relative(k, screened, eps) & k.mask_bits(domain)
}

/// One reduction and reconstruction for both outputs in each whole packet.
#[inline(always)]
fn pair<K: Simd>(k: K, x: K::Array) -> (K::Array, K::Array) {
    let r = prepare::<K, PAIR>(x);
    let (raw_s, raw_c) = fast_pair(k, &r);
    let s = select(k, raw_s, raw_c, &r, false);
    let c = select(k, raw_s, raw_c, &r, true);
    let accepted = decision(k, s, EPS) & decision(k, c, EPS) & r.active;
    let (mut sine, mut cosine) = (k.store(s.0), k.store(c.0));
    for lane in 0..K::LANES {
        if accepted >> lane & 1 == 0 {
            let (s, c) = super::sincos(x.as_ref()[lane]);
            sine.as_mut()[lane] = s;
            cosine.as_mut()[lane] = c;
        }
    }
    (sine, cosine)
}

struct Pairs<'a> {
    x: &'a [f64],
    sine: &'a mut [f64],
    cosine: &'a mut [f64],
}

impl WithSimd for Pairs<'_> {
    type Output = usize;
    #[inline(always)]
    fn with<K: Simd>(self, k: K) -> usize {
        if K::LANES == 1 {
            return 0;
        }
        let covered = self.x.len() / K::LANES * K::LANES;
        for ((x, sine), cosine) in self
            .x
            .chunks_exact(K::LANES)
            .zip(self.sine.chunks_exact_mut(K::LANES))
            .zip(self.cosine.chunks_exact_mut(K::LANES))
        {
            let mut input = K::Array::default();
            input.as_mut().copy_from_slice(x);
            let (s, c) = pair(k, input);
            sine.copy_from_slice(s.as_ref());
            cosine.copy_from_slice(c.as_ref());
        }
        covered
    }
}

/// The existing widest-first cascade, with paired output slices.
pub(crate) fn sincos(x: &[f64], sine: &mut [f64], cosine: &mut [f64]) {
    let done = 0;
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    let done = {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        let mut done = done;
        if x.len() - done >= Avx512::LANES
            && let Some(k) = Avx512::try_new()
        {
            done += k.vectorize(Pairs {
                x: &x[done..],
                sine: &mut sine[done..],
                cosine: &mut cosine[done..],
            });
        }
        if x.len() - done >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            done += k.vectorize(Pairs {
                x: &x[done..],
                sine: &mut sine[done..],
                cosine: &mut cosine[done..],
            });
        }
        if x.len() - done >= Sse2::LANES {
            done += Sse2::new().vectorize(Pairs {
                x: &x[done..],
                sine: &mut sine[done..],
                cosine: &mut cosine[done..],
            });
        }
        done
    };
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    let done = done
        + morphiq_numerics_arch::Neon::new().vectorize(Pairs {
            x,
            sine: &mut *sine,
            cosine: &mut *cosine,
        });
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    )))]
    let done = done
        + morphiq_numerics_arch::Scalar::new().vectorize(Pairs {
            x,
            sine: &mut *sine,
            cosine: &mut *cosine,
        });
    for ((&x, s), c) in x[done..]
        .iter()
        .zip(&mut sine[done..])
        .zip(&mut cosine[done..])
    {
        (*s, *c) = super::sincos(x);
    }
}

#[cfg(test)]
mod tests;
