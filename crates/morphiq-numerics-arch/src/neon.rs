//! Two lanes on aarch64 NEON (Advanced SIMD), with its fused multiply-add.
//!
//! This module is compiled only when the target enables `neon`, which every
//! aarch64 target with a floating-point unit does, so no detection is needed:
//! the target specification itself is the proof. The instructions live in
//! `#[target_feature(enable = "neon")]` helpers, which are `unsafe` to call
//! from a function without that attribute even when the target enables NEON;
//! each backend method calls exactly one, with the token as its proof.

use core::arch::aarch64::{float64x2_t, uint64x2_t};

use crate::{Simd, WithSimd, sealed::Sealed};

/// Two NEON lanes. Every aarch64 target with a floating-point unit enables
/// NEON, so the token is always available where the type exists.
#[derive(Clone, Copy, Debug)]
pub struct Neon(());

impl Neon {
    /// The NEON backend: the target enables NEON, so it is always present.
    #[must_use]
    pub const fn new() -> Self {
        Self(())
    }

    /// The NEON backend; always `Some`, for symmetry with the other backends.
    #[must_use]
    pub const fn try_new() -> Option<Self> {
        Some(Self::new())
    }
}

/// Two lane booleans, each lane all ones (true) or all zeros (false). Only
/// the backend's comparisons and mask operations construct one.
#[derive(Clone, Copy, Debug)]
pub struct NeonMask(uint64x2_t);

impl Default for Neon {
    fn default() -> Self {
        Self::new()
    }
}

impl Sealed for Neon {}

impl Simd for Neon {
    const LANES: usize = 2;
    const NAME: &'static str = "neon";
    const FMA: bool = true;
    type F = float64x2_t;
    type U = uint64x2_t;
    type M = NeonMask;
    type Array = [f64; 2];
    type Words = [u64; 2];

    #[inline(always)]
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output {
        // NEON is enabled for the whole target, so every function already
        // compiles with it: no feature-enabled wrapper is needed.
        op.with(self)
    }

    #[inline(always)]
    fn mul_add(self, a: float64x2_t, b: float64x2_t, c: float64x2_t) -> Option<float64x2_t> {
        // SAFETY: the helper's only precondition is that the CPU has the
        // features it is compiled with, and `self` is a token that exists
        // only when it does.
        Some(unsafe { helpers::mul_add(a, b, c) })
    }

    forward! { helpers;
        fn splat(x: f64) -> float64x2_t;
        fn splat_bits(x: u64) -> uint64x2_t;
        fn load(a: [f64; 2]) -> float64x2_t;
        fn load_bits(a: [u64; 2]) -> uint64x2_t;
        fn store(v: float64x2_t) -> [f64; 2];
        fn add(a: float64x2_t, b: float64x2_t) -> float64x2_t;
        fn sub(a: float64x2_t, b: float64x2_t) -> float64x2_t;
        fn mul(a: float64x2_t, b: float64x2_t) -> float64x2_t;
        fn div(a: float64x2_t, b: float64x2_t) -> float64x2_t;
        fn abs(a: float64x2_t) -> float64x2_t;
        fn neg(a: float64x2_t) -> float64x2_t;
        fn lt(a: float64x2_t, b: float64x2_t) -> NeonMask;
        fn le(a: float64x2_t, b: float64x2_t) -> NeonMask;
        fn and_m(a: NeonMask, b: NeonMask) -> NeonMask;
        fn or_m(a: NeonMask, b: NeonMask) -> NeonMask;
        fn not_m(a: NeonMask) -> NeonMask;
        fn mask_bits(m: NeonMask) -> u64;
        fn select(m: NeonMask, a: float64x2_t, b: float64x2_t) -> float64x2_t;
        fn to_bits(a: float64x2_t) -> uint64x2_t;
        fn to_float(a: uint64x2_t) -> float64x2_t;
        fn and_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t;
        fn or_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t;
        fn sub_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t;
        fn shr_u(a: uint64x2_t, n: u32) -> uint64x2_t;
        fn eq_u(a: uint64x2_t, b: uint64x2_t) -> NeonMask;
    }
}

/// The NEON instructions, one helper per backend method, each compiled with
/// `neon` so the intrinsics inside are safe to call.
mod helpers {
    use core::arch::aarch64::{
        float64x2_t, uint64x2_t, vabsq_f64, vaddq_f64, vandq_u64, vbslq_f64, vceqq_u64, vcleq_f64,
        vcltq_f64, vdivq_f64, vdupq_n_f64, vdupq_n_s64, vdupq_n_u64, vfmaq_f64, vgetq_lane_u64,
        vld1q_f64, vld1q_u64, vmulq_f64, vmvnq_u32, vnegq_f64, vorrq_u64, vreinterpretq_f64_u64,
        vreinterpretq_u32_u64, vreinterpretq_u64_f64, vreinterpretq_u64_u32, vshlq_u64, vst1q_f64,
        vsubq_f64, vsubq_u64,
    };

    use super::NeonMask;

    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn splat(x: f64) -> float64x2_t {
        vdupq_n_f64(x)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn splat_bits(x: u64) -> uint64x2_t {
        vdupq_n_u64(x)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn load(a: [f64; 2]) -> float64x2_t {
        // SAFETY: `a` is two initialized f64, the 16 bytes vld1q_f64 reads; it
        // has no alignment requirement beyond f64's.
        unsafe { vld1q_f64(a.as_ptr()) }
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn load_bits(a: [u64; 2]) -> uint64x2_t {
        // SAFETY: `a` is two initialized u64, the 16 bytes vld1q_u64 reads.
        unsafe { vld1q_u64(a.as_ptr()) }
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn store(v: float64x2_t) -> [f64; 2] {
        let mut out = [0.0; 2];
        // SAFETY: `out` is two f64, the 16 bytes vst1q_f64 writes.
        unsafe { vst1q_f64(out.as_mut_ptr(), v) };
        out
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn add(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        vaddq_f64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn sub(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        vsubq_f64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn mul(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        vmulq_f64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn div(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        vdivq_f64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn abs(a: float64x2_t) -> float64x2_t {
        vabsq_f64(a)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn neg(a: float64x2_t) -> float64x2_t {
        vnegq_f64(a)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn lt(a: float64x2_t, b: float64x2_t) -> NeonMask {
        NeonMask(vcltq_f64(a, b))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn le(a: float64x2_t, b: float64x2_t) -> NeonMask {
        NeonMask(vcleq_f64(a, b))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn and_m(a: NeonMask, b: NeonMask) -> NeonMask {
        NeonMask(vandq_u64(a.0, b.0))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn or_m(a: NeonMask, b: NeonMask) -> NeonMask {
        NeonMask(vorrq_u64(a.0, b.0))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn not_m(a: NeonMask) -> NeonMask {
        NeonMask(vreinterpretq_u64_u32(vmvnq_u32(vreinterpretq_u32_u64(a.0))))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn mask_bits(m: NeonMask) -> u64 {
        (vgetq_lane_u64::<0>(m.0) & 1) | (vgetq_lane_u64::<1>(m.0) & 2)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn select(m: NeonMask, a: float64x2_t, b: float64x2_t) -> float64x2_t {
        vbslq_f64(m.0, a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn to_bits(a: float64x2_t) -> uint64x2_t {
        vreinterpretq_u64_f64(a)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn to_float(a: uint64x2_t) -> float64x2_t {
        vreinterpretq_f64_u64(a)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn and_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        vandq_u64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn or_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        vorrq_u64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn sub_u(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        vsubq_u64(a, b)
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn shr_u(a: uint64x2_t, n: u32) -> uint64x2_t {
        // USHL by a negative count shifts right; by −64 or less it gives 0.
        vshlq_u64(a, vdupq_n_s64(-i64::from(n)))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn eq_u(a: uint64x2_t, b: uint64x2_t) -> NeonMask {
        NeonMask(vceqq_u64(a, b))
    }
    #[target_feature(enable = "neon")]
    #[inline]
    pub(super) fn mul_add(a: float64x2_t, b: float64x2_t, c: float64x2_t) -> float64x2_t {
        // FMLA: c + a·b, rounded once.
        vfmaq_f64(c, a, b)
    }
}
