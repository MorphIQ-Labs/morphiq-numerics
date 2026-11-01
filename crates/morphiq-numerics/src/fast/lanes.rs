//! Scalar operation sequences through the library's existing SIMD dispatch.
use crate::lanes::{Kernel, lanes_mask};
use morphiq_numerics_arch::Simd;

pub(super) struct Cdf;

impl Kernel for Cdf {
    fn scalar(x: f64) -> f64 {
        super::normal::norm_cdf(x)
    }
    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let x = k.load(input);
        let a = k.abs(x);
        let active = k.and_m(
            k.le(k.splat(super::normal::MIN_MAGNITUDE), a),
            k.le(a, k.splat(8.0)),
        );
        let central = k.and_m(active, k.le(a, k.splat(1.0)));
        let tail = k.and_m(active, k.not_m(central));
        let mut y = k.splat(0.0);
        if k.mask_bits(central) != 0 {
            y = center(k, k.select(central, x, k.splat(0.0)));
        }
        if k.mask_bits(tail) != 0 {
            // Active magnitudes are at most 8; other lanes use 1. Thus every
            // rounded exponent is in [-32, 0] (fast_normal_exponent_ok).
            let safe = k.select(tail, a, k.splat(1.0));
            let lower = lower(k, safe);
            let value = k.select(k.lt(x, k.splat(0.0)), lower, k.sub(k.splat(1.0), lower));
            y = k.select(tail, value, y);
        }
        let mut out = k.store(y);
        let active_bits = k.mask_bits(active);
        if active_bits != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::norm_cdf(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

/// The scalar `normal::lower` operation sequence on lanes whose magnitudes
/// are in `[2^-33, 8]`.
#[inline(always)]
fn lower<K: Simd>(k: K, a: K::F) -> K::F {
    let exponential = crate::exp::bounded::in_domain_lanes(k, k.mul(k.mul(k.splat(-0.5), a), a));
    let scaled = k.mul(a, k.splat(crate::normal_distribution::INV_SQRT2_HIGH));
    k.mul(
        k.mul(k.splat(0.5), exponential),
        crate::erfcx::bounded::lanes(k, scaled),
    )
}

pub(super) struct LogCdf;

impl Kernel for LogCdf {
    fn scalar(x: f64) -> f64 {
        super::normal::log_norm_cdf(x)
    }
    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        use crate::normal_distribution::{INV_SQRT2_HIGH, LN2_HIGH};
        let x = k.load(input);
        let a = k.abs(x);
        let negative = k.lt(x, k.splat(0.0));
        // Negative lanes accelerate up to NEG_LIMIT, positive ones up to 8;
        // a NaN lane fails every comparison and keeps its strong result.
        let in_negative = k.and_m(negative, k.le(a, k.splat(super::normal::NEG_LIMIT)));
        let in_positive = k.and_m(k.not_m(negative), k.le(a, k.splat(8.0)));
        let active = k.and_m(
            k.le(k.splat(super::normal::MIN_MAGNITUDE), a),
            k.or_m(in_negative, in_positive),
        );
        let active_bits = k.mask_bits(active);
        let mut out = K::Array::default();
        if active_bits != 0 {
            // Inactive lanes evaluate at magnitude 1, inside every kernel domain.
            let safe = k.select(active, a, k.splat(1.0));
            let t = k.mul(k.mul(k.splat(-0.5), safe), safe);
            let scaled = k.mul(safe, k.splat(INV_SQRT2_HIGH));
            let f = crate::erfcx::bounded::lanes(k, scaled);
            // Positive lanes: q = (0.5 exp(t)) f, with exp entered only at
            // magnitudes at most 8 (fast_normal_exponent_ok). Negative lanes
            // substitute magnitude 1 for the exponential's argument.
            let positive = k.and_m(active, k.not_m(negative));
            let exp_arg = k.select(positive, t, k.splat(-0.5));
            let q = k.mul(
                k.mul(
                    k.splat(0.5),
                    crate::exp::bounded::in_domain_lanes(k, exp_arg),
                ),
                f,
            );
            let w = k.sub(k.splat(1.0), q);
            // One logarithm serves both branches: ln f on negative lanes,
            // ln w on positive ones.
            let g = crate::ln::lanes::bounded_positive(k, k.select(negative, f, w));
            let neg_value = k.sub(k.add(t, g), k.splat(LN2_HIGH));
            let pos_value = k.mul(g, k.div(q, k.sub(k.splat(1.0), w)));
            out = k.store(k.select(negative, neg_value, pos_value));
        }
        if active_bits != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::log_norm_cdf(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

#[inline(always)]
fn center<K: Simd>(k: K, x: K::F) -> K::F {
    use crate::normal_distribution::{CENTER_HIGH as A, DENSITY_HIGH};
    let z = k.mul(x, x);
    let zz = k.mul(z, z);
    let pair = |j: usize| k.add(k.splat(A[j]), k.mul(z, k.splat(A[j + 1])));
    let p0 = pair(0);
    let p1 = pair(2);
    let p2 = pair(4);
    let p3 = pair(6);
    let p4 = pair(8);
    let p5 = pair(10);
    let mut p = k.add(p5, k.mul(zz, k.splat(A[12])));
    for q in [p4, p3, p2, p1, p0] {
        p = k.add(q, k.mul(zz, p));
    }
    k.add(k.splat(0.5), k.mul(k.mul(x, k.splat(DENSITY_HIGH)), p))
}
