//! Candidate normal CDF: Cody's erf/erfcx rationals with an exact exponent.
//!
//! Timing candidate for the fold design; the coefficients are Cody's published
//! values until a numerics generator regenerates them.
#![allow(clippy::excessive_precision, clippy::unreadable_literal)]

use crate::normal_distribution::INV_SQRT2_HIGH;
#[cfg(feature = "simd")]
use morphiq_numerics_arch::Simd;

const A: [f64; 5] = [
    3.161_123_743_870_565_5,
    1.138_641_541_510_501_6e2,
    3.774_852_376_853_020_4e2,
    3.209_377_589_138_469_3e3,
    1.857_777_061_846_031_5e-1,
];
const B: [f64; 4] = [
    2.360_129_095_234_412e1,
    2.440_246_379_344_441_6e2,
    1.282_616_526_077_372_3e3,
    2.844_236_833_439_170_5e3,
];
/// Mid-domain numerator and denominator in ascending powers of `y`.
const N: [f64; 9] = [
    1.230_339_354_797_997_3e3,
    2.051_078_377_826_071_5e3,
    1.712_047_612_634_070_7e3,
    8.819_522_212_417_69e2,
    2.986_351_381_974_001_5e2,
    6.611_919_063_714_163e1,
    8.883_149_794_388_376,
    5.641_884_969_886_701e-1,
    2.153_115_354_744_038_3e-8,
];
const D: [f64; 9] = [
    1.230_339_354_803_749_5e3,
    3.439_367_674_143_722e3,
    4.362_619_090_143_247e3,
    3.290_799_235_733_46e3,
    1.621_389_574_566_690_1e3,
    5.371_811_018_620_099e2,
    1.176_939_508_913_125e2,
    1.574_492_611_070_983_5e1,
    1.0,
];
const P: [f64; 6] = [
    3.053_266_349_612_323_3e-1,
    3.603_448_999_498_044e-1,
    1.257_817_261_112_292_5e-1,
    1.608_378_514_874_227_7e-2,
    6.587_491_615_298_378e-4,
    1.631_538_713_730_209_7e-2,
];
const Q: [f64; 5] = [
    2.568_520_192_289_822_6,
    1.872_952_849_923_460_4,
    5.279_051_029_514_284e-1,
    6.051_834_131_244_132e-2,
    2.335_204_976_268_691_8e-3,
];
const SQRPI: f64 = 0.564_189_583_547_756_3;
/// `y = RN(|x|/sqrt 2)` at or below this takes the erf rational.
pub(super) const BODY: f64 = 0.468_75;
const MID: f64 = 4.0;

#[inline(always)]
fn erf_body(y: f64) -> f64 {
    let s = y * y;
    let mut n = A[4] * s;
    let mut d = s;
    for i in 0..3 {
        n = (n + A[i]) * s;
        d = (d + B[i]) * s;
    }
    y * (n + A[3]) / (d + B[3])
}

#[inline(always)]
fn estrin9(y: f64, y2: f64, y4: f64, y8: f64, c: &[f64; 9]) -> f64 {
    let a0 = c[0] + y * c[1];
    let a1 = c[2] + y * c[3];
    let a2 = c[4] + y * c[5];
    let a3 = c[6] + y * c[7];
    (a0 + y2 * a1) + y4 * (a2 + y2 * a3) + y8 * c[8]
}

#[inline(always)]
fn erfcx_mid(y: f64) -> f64 {
    let y2 = y * y;
    let y4 = y2 * y2;
    let y8 = y4 * y4;
    estrin9(y, y2, y4, y8, &N) / estrin9(y, y2, y4, y8, &D)
}

#[inline(always)]
fn erfcx_tail(y: f64) -> f64 {
    let s = 1.0 / (y * y);
    let s2 = s * s;
    let s4 = s2 * s2;
    let n = (P[4] + s * P[3]) + s2 * (P[2] + s * P[1]) + s4 * (P[0] + s * P[5]);
    let d = (Q[4] + s * Q[3]) + s2 * (Q[2] + s * Q[1]) + s4 * (Q[0] + s);
    (SQRPI - s * n / d) / y
}

/// `Phi(x)` for `2^-33 <= |x| <= 8`.
#[inline(always)]
pub(super) fn in_domain(x: f64) -> f64 {
    let a = x.abs();
    let y = a * INV_SQRT2_HIGH;
    if y <= BODY {
        return 0.5 + 0.5 * erf_body((x * INV_SQRT2_HIGH).copysign(x));
    }
    // exp(-a²/2) = exp(p)(1 + e) to first order; the correction joins the
    // rational, off the exponential's dependency chain.
    let (p, e) = crate::eft::two_prod_d(-0.5 * a, a);
    let exponential = crate::exp::bounded::in_domain(p);
    let r = if y <= MID {
        erfcx_mid(y)
    } else {
        erfcx_tail(y)
    };
    let lower = (0.5 * exponential) * (r + r * e);
    if x < 0.0 { lower } else { 1.0 - lower }
}

#[cfg(feature = "simd")]
#[inline(always)]
fn erf_body_lanes<K: Simd>(k: K, y: K::F) -> K::F {
    let s = k.mul(y, y);
    let mut n = k.mul(k.splat(A[4]), s);
    let mut d = s;
    for i in 0..3 {
        n = k.mul(k.add(n, k.splat(A[i])), s);
        d = k.mul(k.add(d, k.splat(B[i])), s);
    }
    k.div(k.mul(y, k.add(n, k.splat(A[3]))), k.add(d, k.splat(B[3])))
}

#[cfg(feature = "simd")]
#[inline(always)]
fn estrin9_lanes<K: Simd>(k: K, y: K::F, y2: K::F, y4: K::F, y8: K::F, c: &[f64; 9]) -> K::F {
    let t = |i: usize| k.add(k.splat(c[i]), k.mul(y, k.splat(c[i + 1])));
    let (a0, a1, a2, a3) = (t(0), t(2), t(4), t(6));
    k.add(
        k.add(
            k.add(a0, k.mul(y2, a1)),
            k.mul(y4, k.add(a2, k.mul(y2, a3))),
        ),
        k.mul(y8, k.splat(c[8])),
    )
}

#[cfg(feature = "simd")]
#[inline(always)]
fn erfcx_mid_lanes<K: Simd>(k: K, y: K::F) -> K::F {
    let y2 = k.mul(y, y);
    let y4 = k.mul(y2, y2);
    let y8 = k.mul(y4, y4);
    k.div(
        estrin9_lanes(k, y, y2, y4, y8, &N),
        estrin9_lanes(k, y, y2, y4, y8, &D),
    )
}

#[cfg(feature = "simd")]
#[inline(always)]
fn erfcx_tail_lanes<K: Simd>(k: K, y: K::F) -> K::F {
    let s = k.div(k.splat(1.0), k.mul(y, y));
    let s2 = k.mul(s, s);
    let s4 = k.mul(s2, s2);
    let pair = |a: f64, b: f64| k.add(k.splat(a), k.mul(s, k.splat(b)));
    let n = k.add(
        k.add(pair(P[4], P[3]), k.mul(s2, pair(P[2], P[1]))),
        k.mul(s4, pair(P[0], P[5])),
    );
    let d = k.add(
        k.add(pair(Q[4], Q[3]), k.mul(s2, pair(Q[2], Q[1]))),
        k.mul(s4, k.add(k.splat(Q[0]), s)),
    );
    k.div(k.sub(k.splat(SQRPI), k.div(k.mul(s, n), d)), y)
}

/// [`in_domain`] on lanes; `active` marks the lanes inside its domain, and the
/// others evaluate harmless substitutes whose results the caller replaces.
#[cfg(feature = "simd")]
#[inline(always)]
pub(super) fn lanes<K: Simd>(k: K, x: K::F, active: K::M) -> K::F {
    let a = k.abs(x);
    let y = k.mul(a, k.splat(INV_SQRT2_HIGH));
    let body = k.and_m(active, k.le(y, k.splat(BODY)));
    let outer = k.and_m(active, k.not_m(body));
    let mut out = k.splat(0.0);
    if k.mask_bits(body) != 0 {
        let yb = k.select(body, y, k.splat(0.25));
        let signed = k.select(k.lt(x, k.splat(0.0)), k.neg(yb), yb);
        out = k.select(
            body,
            k.add(k.splat(0.5), k.mul(k.splat(0.5), erf_body_lanes(k, signed))),
            out,
        );
    }
    if k.mask_bits(outer) != 0 {
        let safe = k.select(outer, a, k.splat(1.0));
        let ys = k.select(outer, y, k.splat(1.0));
        let (p, e) = crate::lanes::two_prod(k, k.mul(k.splat(-0.5), safe), safe);
        let exponential = crate::exp::bounded::in_domain_lanes(k, p);
        let in_mid = k.le(ys, k.splat(MID));
        let mid = k.and_m(outer, in_mid);
        let tail = k.and_m(outer, k.not_m(in_mid));
        let mut r = k.splat(0.0);
        if k.mask_bits(mid) != 0 {
            r = k.select(mid, erfcx_mid_lanes(k, k.select(mid, ys, k.splat(1.0))), r);
        }
        if k.mask_bits(tail) != 0 {
            r = k.select(
                tail,
                erfcx_tail_lanes(k, k.select(tail, ys, k.splat(5.0))),
                r,
            );
        }
        let lower = k.mul(k.mul(k.splat(0.5), exponential), k.add(r, k.mul(r, e)));
        let value = k.select(k.lt(x, k.splat(0.0)), lower, k.sub(k.splat(1.0), lower));
        out = k.select(outer, value, out);
    }
    out
}
