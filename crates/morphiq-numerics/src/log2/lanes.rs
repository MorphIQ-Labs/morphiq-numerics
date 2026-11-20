//! Radix logarithms in scalar operation order, sharing ln's lane reduction.
use morphiq_numerics_arch::Simd;

use super::tables::{INV_LN2_HI, INV_LN2_LO, INV_LN10_HI, INV_LN10_LO};
use crate::lanes::{Dw, Kernel, add_dw, decide_relative, mul_dw, two_sum};

pub(crate) struct Radix<const BASE10: bool>;

impl<const BASE10: bool> Kernel for Radix<BASE10> {
    fn scalar(x: f64) -> f64 {
        if BASE10 {
            super::log10(x)
        } else {
            super::log2(x)
        }
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let (value, active) = fast_value::<K, BASE10>(k, x);
        let accepted = decide_relative(k, value, crate::ln::EPS) & active;
        let mut out = k.store(value.0);
        for (lane, value) in out.as_mut().iter_mut().enumerate() {
            if accepted >> lane & 1 == 0 {
                *value = Self::scalar(x.as_ref()[lane]);
            }
        }
        out
    }
}

/// Screen before reduction, so every evaluated lane satisfies the scalar
/// hypotheses. Discarded lanes use 2, whose radix logarithms are nonzero.
#[inline(always)]
fn fast_value<K: Simd, const BASE10: bool>(k: K, input: K::Array) -> (Dw<K>, u64) {
    let x = k.load(input);
    let ordinary = k.and_m(k.lt(k.splat(0.0), x), k.lt(x, k.splat(f64::INFINITY)));
    let one = k.eq_u(k.to_bits(x), k.splat_bits(1.0_f64.to_bits()));
    let active = k.and_m(ordinary, k.not_m(one));
    let x = k.select(active, x, k.splat(2.0));
    let value = if BASE10 {
        let logarithm = crate::ln::lanes::fallback::ln(k, x);
        let reciprocal = two_sum(k, k.splat(INV_LN10_HI), k.splat(INV_LN10_LO));
        mul_dw(k, logarithm, reciprocal)
    } else {
        let (logarithm, exponent) = crate::ln::lanes::fallback::ln_y(k, x);
        let reciprocal = two_sum(k, k.splat(INV_LN2_HI), k.splat(INV_LN2_LO));
        let w = mul_dw(k, logarithm, reciprocal);
        let reconstructed = add_dw(k, (exponent, k.splat(0.0)), w);
        let zero_exponent = k.eq_u(k.to_bits(exponent), k.splat_bits(0));
        (
            k.select(zero_exponent, w.0, reconstructed.0),
            k.select(zero_exponent, w.1, reconstructed.1),
        )
    };
    (value, k.mask_bits(active))
}

#[cfg(test)]
mod tests;
