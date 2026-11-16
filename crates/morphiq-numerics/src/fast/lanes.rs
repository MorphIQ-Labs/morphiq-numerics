//! Scalar operation sequences through the library's existing SIMD dispatch.
use crate::lanes::{Cold, Kernel, cold, cold_arrays, lanes_mask};
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
            k.le(a, k.splat(super::cdf::RATIONAL_LIMIT)),
        );
        let active_bits = k.mask_bits(active);
        let y = if active_bits != 0 {
            super::cdf::lanes(k, x, active)
        } else {
            k.splat(0.0)
        };
        let mut out = k.store(y);
        if active_bits != lanes_mask::<K>() {
            let far = far_mask(k, x);
            if k.mask_bits(far) != 0 {
                // Runtime AVX-512 cannot inline vector conversions into a
                // baseline-ISA trampoline. Static backends keep the vector
                // boundary, which preserves their common-path register lifetimes.
                if cfg!(all(target_arch = "x86_64", not(target_feature = "avx512f")))
                    && K::LANES == 8
                {
                    return finish_cdf(k, active_bits, k.store(x), k.store(y));
                }
                return k.store(cold(k, FinishCdf { near: active_bits }, x, y));
            }
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::norm_cdf(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

#[inline(always)]
fn far_mask<K: Simd>(k: K, x: K::F) -> K::M {
    k.and_m(
        k.le(k.splat(-super::cdf::FAR_LIMIT), x),
        k.lt(x, k.splat(-super::cdf::RATIONAL_LIMIT)),
    )
}

// Own snapshots at this boundary so the caller's original arrays do not escape.
// All lane operations remain in the backend wrapper entered by cold_arrays.
#[inline(never)]
fn finish_cdf<K: Simd>(k: K, near: u64, input: K::Array, out: K::Array) -> K::Array {
    cold_arrays(k, FinishCdf { near }, &input, &out)
}

/// Complete far-tail and screened lanes outside the common near-domain frame,
/// while retaining the backend token and vector arithmetic.
struct FinishCdf {
    near: u64,
}

impl Cold for FinishCdf {
    #[inline(always)]
    fn run<K: Simd>(self, k: K, input: K::Array, out: K::Array) -> K::Array {
        let x = k.load(input);
        let far = far_mask(k, x);
        let y = super::cdf::far_lanes(k, x, far);
        let mut out = k.store(k.select(far, y, k.load(out)));
        let active = self.near | k.mask_bits(far);
        if active != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active >> i & 1 == 0 {
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
