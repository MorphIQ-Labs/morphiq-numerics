//! One lane of plain `f64` arithmetic: available on every target.

use crate::{Simd, WithSimd, sealed::Sealed};

/// The one-lane backend: plain `f64` arithmetic, on every target. It has no
/// fused multiply-add.
#[derive(Clone, Copy, Debug)]
pub struct Scalar(());

impl Scalar {
    /// The scalar backend, which every target has.
    #[must_use]
    pub const fn new() -> Self {
        Self(())
    }
}

impl Default for Scalar {
    fn default() -> Self {
        Self::new()
    }
}

impl Sealed for Scalar {}

impl Simd for Scalar {
    const LANES: usize = 1;
    const NAME: &'static str = "scalar";
    const FMA: bool = false;
    type F = f64;
    type U = u64;
    type M = bool;
    type Array = [f64; 1];
    type Words = [u64; 1];

    #[inline(always)]
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output {
        op.with(self)
    }

    #[inline(always)]
    fn splat(self, x: f64) -> f64 {
        x
    }
    #[inline(always)]
    fn splat_bits(self, x: u64) -> u64 {
        x
    }
    #[inline(always)]
    fn load(self, a: [f64; 1]) -> f64 {
        a[0]
    }
    #[inline(always)]
    fn load_bits(self, a: [u64; 1]) -> u64 {
        a[0]
    }
    #[inline(always)]
    fn store(self, v: f64) -> [f64; 1] {
        [v]
    }

    #[inline(always)]
    fn add(self, a: f64, b: f64) -> f64 {
        a + b
    }
    #[inline(always)]
    fn sub(self, a: f64, b: f64) -> f64 {
        a - b
    }
    #[inline(always)]
    fn mul(self, a: f64, b: f64) -> f64 {
        a * b
    }
    #[inline(always)]
    fn div(self, a: f64, b: f64) -> f64 {
        a / b
    }
    #[inline(always)]
    fn mul_add(self, _: f64, _: f64, _: f64) -> Option<f64> {
        // Plain f64 arithmetic has no fused multiply-add without a libm call
        // or a software emulation, and this backend uses neither.
        None
    }
    #[inline(always)]
    fn abs(self, a: f64) -> f64 {
        a.abs()
    }
    #[inline(always)]
    fn neg(self, a: f64) -> f64 {
        -a
    }

    #[inline(always)]
    fn lt(self, a: f64, b: f64) -> bool {
        a < b
    }
    #[inline(always)]
    fn le(self, a: f64, b: f64) -> bool {
        a <= b
    }
    #[inline(always)]
    fn and_m(self, a: bool, b: bool) -> bool {
        a & b
    }
    #[inline(always)]
    fn or_m(self, a: bool, b: bool) -> bool {
        a | b
    }
    #[inline(always)]
    fn not_m(self, a: bool) -> bool {
        !a
    }
    #[inline(always)]
    fn mask_bits(self, m: bool) -> u64 {
        u64::from(m)
    }
    #[inline(always)]
    fn select(self, m: bool, a: f64, b: f64) -> f64 {
        if m { a } else { b }
    }

    #[inline(always)]
    fn to_bits(self, a: f64) -> u64 {
        a.to_bits()
    }
    #[inline(always)]
    fn to_float(self, a: u64) -> f64 {
        f64::from_bits(a)
    }
    #[inline(always)]
    fn and_u(self, a: u64, b: u64) -> u64 {
        a & b
    }
    #[inline(always)]
    fn or_u(self, a: u64, b: u64) -> u64 {
        a | b
    }
    #[inline(always)]
    fn sub_u(self, a: u64, b: u64) -> u64 {
        a.wrapping_sub(b)
    }
    #[inline(always)]
    fn eq_u(self, a: u64, b: u64) -> bool {
        a == b
    }
}
