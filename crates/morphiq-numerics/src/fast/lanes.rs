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
        let y = super::cdf::lanes(k, x, active);
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
