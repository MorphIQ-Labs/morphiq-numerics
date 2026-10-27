//! Scalar operation sequences through the library's existing SIMD dispatch.
use crate::lanes::{Kernel, lanes_mask};
use morphiq_numerics_arch::Simd;

pub(super) struct Exp;
pub(super) struct Erfcx;
pub(super) struct Cdf;

impl Kernel for Exp {
    fn scalar(x: f64) -> f64 {
        super::elementary::exp(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let reduced = crate::exp::lanes::reduce(k, &input);
        let (h, l) = crate::exp::lanes::stage_a(k, &reduced);
        let mut out = k.store(k.mul(k.add(h, l), reduced.table.scale));
        for (i, value) in out.as_mut().iter_mut().enumerate() {
            if reduced.screened >> i & 1 != 0 {
                *value = Self::scalar(input.as_ref()[i]);
            }
        }
        out
    }
}

impl Kernel for Erfcx {
    fn scalar(x: f64) -> f64 {
        super::normal::erfcx(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let x = k.load(input);
        let active = k.and_m(
            k.and_m(k.le(k.splat(-0.5), x), k.lt(x, k.splat(16.0))),
            k.le(k.splat(super::normal::MIN_MAGNITUDE), k.abs(x)),
        );
        let active_bits = k.mask_bits(active);
        // Every inactive argument becomes a valid table input before reduction.
        let safe = k.select(active, x, k.splat(1.0));
        let (hi, lo) = crate::erfcx::lanes::table(k, safe);
        let mut out = k.store(k.add(hi, lo));
        if active_bits != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::erfcx(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

impl Kernel for Cdf {
    fn scalar(x: f64) -> f64 {
        super::normal::norm_cdf(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let x = k.load(input);
        let magnitude = k.abs(x);
        let active = k.and_m(
            k.le(k.splat(super::normal::MIN_MAGNITUDE), magnitude),
            k.le(magnitude, k.splat(8.0)),
        );
        let active_bits = k.mask_bits(active);
        let a = k.select(active, magnitude, k.splat(1.0));
        // Preserve the scalar multiply order, including rounding of -a²/2.
        let exponent = k.mul(k.mul(k.splat(-0.5), a), a);
        let reduced = crate::exp::lanes::reduce(k, &k.store(exponent));
        let (exp_hi, exp_lo) = crate::exp::lanes::stage_a(k, &reduced);
        let exponential = k.mul(k.add(exp_hi, exp_lo), reduced.table.scale);
        let scaled = k.mul(a, k.splat(crate::normal_distribution::INV_SQRT2_HIGH));
        let (hi, lo) = crate::erfcx::lanes::table(k, scaled);
        let lower = k.mul(k.mul(k.splat(0.5), exponential), k.add(hi, lo));
        let cdf = k.select(k.lt(x, k.splat(0.0)), lower, k.sub(k.splat(1.0), lower));
        let mut out = k.store(cdf);
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
