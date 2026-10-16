//! x86-64: two SSE2 lanes (no fused multiply-add), four AVX2 lanes with FMA,
//! and eight AVX-512F lanes.
//!
//! This module is compiled only when the target enables SSE2, which every
//! hosted x86-64 target does, so the SSE2 backend needs no detection and its
//! intrinsics (those without a pointer) are safe to call. AVX2, FMA and
//! AVX-512F are detected (`Avx2::try_new`, `Avx512::try_new`). Their
//! instructions live in `#[target_feature]` helper functions below, which are
//! `unsafe` to call from code compiled without those features; each backend
//! method calls exactly one helper, in an `unsafe` block whose proof is the
//! token it receives.

use core::arch::x86_64::{__m128d, __m128i, __m256d, __m256i, __m512d, __m512i, __mmask8};

use crate::{Simd, WithSimd, sealed::Sealed};
use helpers::{avx2, avx512, sse2};

// ---------------------------------------------------------------------------
// SSE2: two lanes, no fused multiply-add.

/// Two SSE2 lanes. Every hosted x86-64 target enables SSE2, so the token is
/// always available where the type exists. SSE2 has no fused multiply-add.
#[derive(Clone, Copy, Debug)]
pub struct Sse2(());

impl Sse2 {
    /// The SSE2 backend: the target enables SSE2, so it is always present.
    #[must_use]
    pub const fn new() -> Self {
        Self(())
    }

    /// The SSE2 backend; always `Some`, for symmetry with the other backends.
    #[must_use]
    pub const fn try_new() -> Option<Self> {
        Some(Self::new())
    }
}

/// Two lane booleans, each lane all ones (true) or all zeros (false). Only
/// the backend's comparisons and mask operations construct one.
#[derive(Clone, Copy, Debug)]
pub struct Sse2Mask(__m128d);

impl Default for Sse2 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sealed for Sse2 {}

impl Simd for Sse2 {
    const LANES: usize = 2;
    const NAME: &'static str = "sse2";
    const FMA: bool = false;
    type F = __m128d;
    type U = __m128i;
    type M = Sse2Mask;
    type Array = [f64; 2];
    type Words = [u64; 2];

    #[inline(always)]
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output {
        // SSE2 is enabled for the whole target: no feature-enabled wrapper is
        // needed.
        op.with(self)
    }

    #[inline(always)]
    fn mul_add(self, _: __m128d, _: __m128d, _: __m128d) -> Option<__m128d> {
        // SSE2 has no fused multiply-add.
        None
    }

    forward! { sse2;
        fn splat(x: f64) -> __m128d;
        fn splat_bits(x: u64) -> __m128i;
        fn load(a: [f64; 2]) -> __m128d;
        fn load_bits(a: [u64; 2]) -> __m128i;
        fn store(v: __m128d) -> [f64; 2];
        fn add(a: __m128d, b: __m128d) -> __m128d;
        fn sub(a: __m128d, b: __m128d) -> __m128d;
        fn mul(a: __m128d, b: __m128d) -> __m128d;
        fn div(a: __m128d, b: __m128d) -> __m128d;
        fn abs(a: __m128d) -> __m128d;
        fn neg(a: __m128d) -> __m128d;
        fn lt(a: __m128d, b: __m128d) -> Sse2Mask;
        fn le(a: __m128d, b: __m128d) -> Sse2Mask;
        fn and_m(a: Sse2Mask, b: Sse2Mask) -> Sse2Mask;
        fn or_m(a: Sse2Mask, b: Sse2Mask) -> Sse2Mask;
        fn not_m(a: Sse2Mask) -> Sse2Mask;
        fn mask_bits(m: Sse2Mask) -> u64;
        fn select(m: Sse2Mask, a: __m128d, b: __m128d) -> __m128d;
        fn to_bits(a: __m128d) -> __m128i;
        fn to_float(a: __m128i) -> __m128d;
        fn and_u(a: __m128i, b: __m128i) -> __m128i;
        fn or_u(a: __m128i, b: __m128i) -> __m128i;
        fn sub_u(a: __m128i, b: __m128i) -> __m128i;
        fn shr_u(a: __m128i, n: u32) -> __m128i;
        fn eq_u(a: __m128i, b: __m128i) -> Sse2Mask;
    }
}

// ---------------------------------------------------------------------------
// AVX2 with FMA: four lanes.

/// Four AVX2 lanes, with FMA's fused multiply-add. Obtained only from
/// [`Avx2::try_new`], which checks that the CPU has both AVX2 and FMA.
#[derive(Clone, Copy, Debug)]
pub struct Avx2(());

impl Avx2 {
    /// The AVX2 backend, if this CPU has AVX2 and FMA: detected at run time
    /// with the `std` feature, else enabled at compile time.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        #[cfg(feature = "std")]
        let present = std::arch::is_x86_feature_detected!("avx2")
            && std::arch::is_x86_feature_detected!("fma");
        #[cfg(not(feature = "std"))]
        let present = cfg!(all(target_feature = "avx2", target_feature = "fma"));
        present.then_some(Self(()))
    }
}

/// Four lane booleans, each lane all ones (true) or all zeros (false). Only
/// the backend's comparisons and mask operations construct one.
#[derive(Clone, Copy, Debug)]
pub struct Avx2Mask(__m256d);

impl Sealed for Avx2 {}

#[target_feature(enable = "avx2,fma")]
#[inline]
fn avx2_run<W: WithSimd>(simd: Avx2, op: W) -> W::Output {
    op.with(simd)
}

impl Simd for Avx2 {
    const LANES: usize = 4;
    const NAME: &'static str = "avx2";
    const FMA: bool = true;
    type F = __m256d;
    type U = __m256i;
    type M = Avx2Mask;
    type Array = [f64; 4];
    type Words = [u64; 4];

    #[inline(always)]
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output {
        // SAFETY: avx2_run only requires AVX2 and FMA, which `self` proves.
        unsafe { avx2_run(self, op) }
    }

    #[inline(always)]
    fn mul_add(self, a: __m256d, b: __m256d, c: __m256d) -> Option<__m256d> {
        // SAFETY: the helper's only precondition is that the CPU has the
        // features it is compiled with, and `self` is a token that exists
        // only when it does.
        Some(unsafe { avx2::mul_add(a, b, c) })
    }

    forward! { avx2;
        fn splat(x: f64) -> __m256d;
        fn splat_bits(x: u64) -> __m256i;
        fn load(a: [f64; 4]) -> __m256d;
        fn load_bits(a: [u64; 4]) -> __m256i;
        fn store(v: __m256d) -> [f64; 4];
        fn add(a: __m256d, b: __m256d) -> __m256d;
        fn sub(a: __m256d, b: __m256d) -> __m256d;
        fn mul(a: __m256d, b: __m256d) -> __m256d;
        fn div(a: __m256d, b: __m256d) -> __m256d;
        fn abs(a: __m256d) -> __m256d;
        fn neg(a: __m256d) -> __m256d;
        fn lt(a: __m256d, b: __m256d) -> Avx2Mask;
        fn le(a: __m256d, b: __m256d) -> Avx2Mask;
        fn and_m(a: Avx2Mask, b: Avx2Mask) -> Avx2Mask;
        fn or_m(a: Avx2Mask, b: Avx2Mask) -> Avx2Mask;
        fn not_m(a: Avx2Mask) -> Avx2Mask;
        fn mask_bits(m: Avx2Mask) -> u64;
        fn select(m: Avx2Mask, a: __m256d, b: __m256d) -> __m256d;
        fn to_bits(a: __m256d) -> __m256i;
        fn to_float(a: __m256i) -> __m256d;
        fn and_u(a: __m256i, b: __m256i) -> __m256i;
        fn or_u(a: __m256i, b: __m256i) -> __m256i;
        fn sub_u(a: __m256i, b: __m256i) -> __m256i;
        fn shr_u(a: __m256i, n: u32) -> __m256i;
        fn eq_u(a: __m256i, b: __m256i) -> Avx2Mask;
    }
}

// ---------------------------------------------------------------------------
// AVX-512F: eight lanes.

/// Eight AVX-512F lanes, with its fused multiply-add. Obtained only from
/// [`Avx512::try_new`], which checks that the CPU (and, with `std`, the
/// operating system) supports AVX-512F.
#[derive(Clone, Copy, Debug)]
pub struct Avx512(());

impl Avx512 {
    /// The AVX-512F backend, if this CPU has AVX-512F: detected at run time
    /// with the `std` feature, else enabled at compile time.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        #[cfg(feature = "std")]
        let present = std::arch::is_x86_feature_detected!("avx512f");
        #[cfg(not(feature = "std"))]
        let present = cfg!(target_feature = "avx512f");
        present.then_some(Self(()))
    }
}

/// Eight lane booleans, one bit each: an AVX-512 mask register.
#[derive(Clone, Copy, Debug)]
pub struct Avx512Mask(__mmask8);

impl Sealed for Avx512 {}

#[target_feature(enable = "avx512f")]
#[inline]
fn avx512_run<W: WithSimd>(simd: Avx512, op: W) -> W::Output {
    op.with(simd)
}

impl Simd for Avx512 {
    const LANES: usize = 8;
    const NAME: &'static str = "avx512";
    const FMA: bool = true;
    type F = __m512d;
    type U = __m512i;
    type M = Avx512Mask;
    type Array = [f64; 8];
    type Words = [u64; 8];

    #[inline(always)]
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output {
        // SAFETY: avx512_run only requires AVX-512F, which `self` proves.
        unsafe { avx512_run(self, op) }
    }

    #[inline(always)]
    fn mul_add(self, a: __m512d, b: __m512d, c: __m512d) -> Option<__m512d> {
        // SAFETY: the helper's only precondition is that the CPU has the
        // features it is compiled with, and `self` is a token that exists
        // only when it does.
        Some(unsafe { avx512::mul_add(a, b, c) })
    }

    forward! { avx512;
        fn splat(x: f64) -> __m512d;
        fn splat_bits(x: u64) -> __m512i;
        fn load(a: [f64; 8]) -> __m512d;
        fn load_bits(a: [u64; 8]) -> __m512i;
        fn store(v: __m512d) -> [f64; 8];
        fn add(a: __m512d, b: __m512d) -> __m512d;
        fn sub(a: __m512d, b: __m512d) -> __m512d;
        fn mul(a: __m512d, b: __m512d) -> __m512d;
        fn div(a: __m512d, b: __m512d) -> __m512d;
        fn abs(a: __m512d) -> __m512d;
        fn neg(a: __m512d) -> __m512d;
        fn lt(a: __m512d, b: __m512d) -> Avx512Mask;
        fn le(a: __m512d, b: __m512d) -> Avx512Mask;
        fn select(m: Avx512Mask, a: __m512d, b: __m512d) -> __m512d;
        fn to_bits(a: __m512d) -> __m512i;
        fn to_float(a: __m512i) -> __m512d;
        fn and_u(a: __m512i, b: __m512i) -> __m512i;
        fn or_u(a: __m512i, b: __m512i) -> __m512i;
        fn sub_u(a: __m512i, b: __m512i) -> __m512i;
        fn shr_u(a: __m512i, n: u32) -> __m512i;
        fn eq_u(a: __m512i, b: __m512i) -> Avx512Mask;
    }

    // Mask registers are plain bytes: no instruction set is involved.
    #[inline(always)]
    fn and_m(self, a: Avx512Mask, b: Avx512Mask) -> Avx512Mask {
        Avx512Mask(a.0 & b.0)
    }
    #[inline(always)]
    fn or_m(self, a: Avx512Mask, b: Avx512Mask) -> Avx512Mask {
        Avx512Mask(a.0 | b.0)
    }
    #[inline(always)]
    fn not_m(self, a: Avx512Mask) -> Avx512Mask {
        Avx512Mask(!a.0)
    }
    #[inline(always)]
    fn mask_bits(self, m: Avx512Mask) -> u64 {
        u64::from(m.0)
    }
    #[inline(always)]
    fn mask_from_bits(self, bits: u64) -> Avx512Mask {
        #[allow(clippy::cast_possible_truncation)] // exactly eight mask lanes
        Avx512Mask(bits as u8)
    }
}

/// The AVX2 and AVX-512F instructions, one helper per backend method. Each
/// is compiled with its backend's features, so the intrinsics inside are safe
/// to call; calling a helper is `unsafe` from code without those features.
mod helpers {
    pub(super) mod sse2 {
        use core::arch::x86_64::{
            __m128d, __m128i, _mm_add_pd, _mm_and_pd, _mm_and_si128, _mm_andnot_pd,
            _mm_castpd_si128, _mm_castsi128_pd, _mm_cmpeq_epi32, _mm_cmple_pd, _mm_cmplt_pd,
            _mm_cvtsi64_si128, _mm_div_pd, _mm_loadu_pd, _mm_loadu_si128, _mm_movemask_pd,
            _mm_mul_pd, _mm_or_pd, _mm_or_si128, _mm_set1_epi64x, _mm_set1_pd, _mm_shuffle_epi32,
            _mm_srl_epi64, _mm_storeu_pd, _mm_sub_epi64, _mm_sub_pd, _mm_xor_pd,
        };

        use super::super::Sse2Mask;

        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn splat(x: f64) -> __m128d {
            _mm_set1_pd(x)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn splat_bits(x: u64) -> __m128i {
            _mm_set1_epi64x(x.cast_signed())
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn load(a: [f64; 2]) -> __m128d {
            // SAFETY: `a` is the two f64 _mm_loadu_pd reads; it needs no alignment.
            unsafe { _mm_loadu_pd(a.as_ptr()) }
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn load_bits(a: [u64; 2]) -> __m128i {
            // SAFETY: `a` is the 16 bytes _mm_loadu_si128 reads, unaligned.
            unsafe { _mm_loadu_si128(a.as_ptr().cast()) }
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn store(v: __m128d) -> [f64; 2] {
            let mut out = [0.0; 2];
            // SAFETY: `out` is the two f64 _mm_storeu_pd writes, unaligned.
            unsafe { _mm_storeu_pd(out.as_mut_ptr(), v) };
            out
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn add(a: __m128d, b: __m128d) -> __m128d {
            _mm_add_pd(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn sub(a: __m128d, b: __m128d) -> __m128d {
            _mm_sub_pd(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn mul(a: __m128d, b: __m128d) -> __m128d {
            _mm_mul_pd(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn div(a: __m128d, b: __m128d) -> __m128d {
            _mm_div_pd(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn abs(a: __m128d) -> __m128d {
            _mm_andnot_pd(_mm_set1_pd(-0.0), a)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn neg(a: __m128d) -> __m128d {
            _mm_xor_pd(a, _mm_set1_pd(-0.0))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn lt(a: __m128d, b: __m128d) -> Sse2Mask {
            Sse2Mask(_mm_cmplt_pd(a, b))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn le(a: __m128d, b: __m128d) -> Sse2Mask {
            Sse2Mask(_mm_cmple_pd(a, b))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn and_m(a: Sse2Mask, b: Sse2Mask) -> Sse2Mask {
            Sse2Mask(_mm_and_pd(a.0, b.0))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn or_m(a: Sse2Mask, b: Sse2Mask) -> Sse2Mask {
            Sse2Mask(_mm_or_pd(a.0, b.0))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn not_m(a: Sse2Mask) -> Sse2Mask {
            Sse2Mask(_mm_xor_pd(a.0, _mm_castsi128_pd(_mm_set1_epi64x(-1))))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn mask_bits(m: Sse2Mask) -> u64 {
            // MOVMSKPD: bit i is lane i's sign bit, so bits 0 and 1 only.
            u64::from(_mm_movemask_pd(m.0).cast_unsigned())
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn select(m: Sse2Mask, a: __m128d, b: __m128d) -> __m128d {
            // SSE2 has no blend: (m ∧ a) ∨ (¬m ∧ b), each mask lane all ones or zeros.
            _mm_or_pd(_mm_and_pd(m.0, a), _mm_andnot_pd(m.0, b))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn to_bits(a: __m128d) -> __m128i {
            _mm_castpd_si128(a)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn to_float(a: __m128i) -> __m128d {
            _mm_castsi128_pd(a)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn and_u(a: __m128i, b: __m128i) -> __m128i {
            _mm_and_si128(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn or_u(a: __m128i, b: __m128i) -> __m128i {
            _mm_or_si128(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn sub_u(a: __m128i, b: __m128i) -> __m128i {
            _mm_sub_epi64(a, b)
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn shr_u(a: __m128i, n: u32) -> __m128i {
            // PSRLQ by the count in the low 64 bits; 64 or more gives 0.
            _mm_srl_epi64(a, _mm_cvtsi64_si128(i64::from(n)))
        }
        #[target_feature(enable = "sse2")]
        #[inline]
        pub(in super::super) fn eq_u(a: __m128i, b: __m128i) -> Sse2Mask {
            // SSE2 compares 32-bit halves only: a 64-bit lane is equal when both
            // halves are, so AND each half's result with its partner's.
            let halves = _mm_cmpeq_epi32(a, b);
            let partners = _mm_shuffle_epi32::<0b10_11_00_01>(halves);
            Sse2Mask(_mm_castsi128_pd(_mm_and_si128(halves, partners)))
        }
    }

    pub(super) mod avx2 {
        use core::arch::x86_64::{
            __m256d, __m256i, _CMP_LE_OQ, _CMP_LT_OQ, _mm_cvtsi64_si128, _mm256_add_pd,
            _mm256_and_pd, _mm256_and_si256, _mm256_andnot_pd, _mm256_blendv_pd,
            _mm256_castpd_si256, _mm256_castsi256_pd, _mm256_cmp_pd, _mm256_cmpeq_epi64,
            _mm256_div_pd, _mm256_fmadd_pd, _mm256_loadu_pd, _mm256_loadu_si256,
            _mm256_movemask_pd, _mm256_mul_pd, _mm256_or_pd, _mm256_or_si256, _mm256_set1_epi64x,
            _mm256_set1_pd, _mm256_srl_epi64, _mm256_storeu_pd, _mm256_sub_epi64, _mm256_sub_pd,
            _mm256_xor_pd,
        };

        use super::super::Avx2Mask;

        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn splat(x: f64) -> __m256d {
            _mm256_set1_pd(x)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn splat_bits(x: u64) -> __m256i {
            _mm256_set1_epi64x(x.cast_signed())
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn load(a: [f64; 4]) -> __m256d {
            // SAFETY: `a` is the four f64 _mm256_loadu_pd reads, unaligned.
            unsafe { _mm256_loadu_pd(a.as_ptr()) }
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn load_bits(a: [u64; 4]) -> __m256i {
            // SAFETY: `a` is the 32 bytes _mm256_loadu_si256 reads, unaligned.
            unsafe { _mm256_loadu_si256(a.as_ptr().cast()) }
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn store(v: __m256d) -> [f64; 4] {
            let mut out = [0.0; 4];
            // SAFETY: `out` is the four f64 _mm256_storeu_pd writes, unaligned.
            unsafe { _mm256_storeu_pd(out.as_mut_ptr(), v) };
            out
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn add(a: __m256d, b: __m256d) -> __m256d {
            _mm256_add_pd(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn sub(a: __m256d, b: __m256d) -> __m256d {
            _mm256_sub_pd(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn mul(a: __m256d, b: __m256d) -> __m256d {
            _mm256_mul_pd(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn div(a: __m256d, b: __m256d) -> __m256d {
            _mm256_div_pd(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn mul_add(a: __m256d, b: __m256d, c: __m256d) -> __m256d {
            // VFMADD: a·b + c, rounded once.
            _mm256_fmadd_pd(a, b, c)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn abs(a: __m256d) -> __m256d {
            _mm256_andnot_pd(_mm256_set1_pd(-0.0), a)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn neg(a: __m256d) -> __m256d {
            _mm256_xor_pd(a, _mm256_set1_pd(-0.0))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn lt(a: __m256d, b: __m256d) -> Avx2Mask {
            Avx2Mask(_mm256_cmp_pd::<_CMP_LT_OQ>(a, b))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn le(a: __m256d, b: __m256d) -> Avx2Mask {
            Avx2Mask(_mm256_cmp_pd::<_CMP_LE_OQ>(a, b))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn and_m(a: Avx2Mask, b: Avx2Mask) -> Avx2Mask {
            Avx2Mask(_mm256_and_pd(a.0, b.0))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn or_m(a: Avx2Mask, b: Avx2Mask) -> Avx2Mask {
            Avx2Mask(_mm256_or_pd(a.0, b.0))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn not_m(a: Avx2Mask) -> Avx2Mask {
            Avx2Mask(_mm256_xor_pd(
                a.0,
                _mm256_castsi256_pd(_mm256_set1_epi64x(-1)),
            ))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn mask_bits(m: Avx2Mask) -> u64 {
            // VMOVMSKPD: bit i is lane i's sign bit, so bits 0 to 3 only.
            u64::from(_mm256_movemask_pd(m.0).cast_unsigned())
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn select(m: Avx2Mask, a: __m256d, b: __m256d) -> __m256d {
            // VBLENDVPD takes the second operand where the mask's sign bit is
            // set; each mask lane is all ones or all zeros.
            _mm256_blendv_pd(b, a, m.0)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn to_bits(a: __m256d) -> __m256i {
            _mm256_castpd_si256(a)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn to_float(a: __m256i) -> __m256d {
            _mm256_castsi256_pd(a)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn and_u(a: __m256i, b: __m256i) -> __m256i {
            _mm256_and_si256(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn or_u(a: __m256i, b: __m256i) -> __m256i {
            _mm256_or_si256(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn sub_u(a: __m256i, b: __m256i) -> __m256i {
            _mm256_sub_epi64(a, b)
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn shr_u(a: __m256i, n: u32) -> __m256i {
            // VPSRLQ by the count in the low 64 bits; 64 or more gives 0.
            _mm256_srl_epi64(a, _mm_cvtsi64_si128(i64::from(n)))
        }
        #[target_feature(enable = "avx2,fma")]
        #[inline]
        pub(in super::super) fn eq_u(a: __m256i, b: __m256i) -> Avx2Mask {
            Avx2Mask(_mm256_castsi256_pd(_mm256_cmpeq_epi64(a, b)))
        }
    }

    pub(super) mod avx512 {
        use core::arch::x86_64::{
            __m512d, __m512i, _CMP_LE_OQ, _CMP_LT_OQ, _mm_cvtsi64_si128, _mm512_abs_pd,
            _mm512_add_pd, _mm512_and_si512, _mm512_castpd_si512, _mm512_castsi512_pd,
            _mm512_cmp_pd_mask, _mm512_cmpeq_epi64_mask, _mm512_div_pd, _mm512_fmadd_pd,
            _mm512_loadu_pd, _mm512_loadu_si512, _mm512_mask_blend_pd, _mm512_mul_pd,
            _mm512_or_si512, _mm512_set1_epi64, _mm512_set1_pd, _mm512_srl_epi64, _mm512_storeu_pd,
            _mm512_sub_epi64, _mm512_sub_pd, _mm512_xor_si512,
        };

        use super::super::Avx512Mask;

        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn splat(x: f64) -> __m512d {
            _mm512_set1_pd(x)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn splat_bits(x: u64) -> __m512i {
            _mm512_set1_epi64(x.cast_signed())
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn load(a: [f64; 8]) -> __m512d {
            // SAFETY: `a` is the eight f64 _mm512_loadu_pd reads, unaligned.
            unsafe { _mm512_loadu_pd(a.as_ptr()) }
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn load_bits(a: [u64; 8]) -> __m512i {
            // SAFETY: `a` is the 64 bytes _mm512_loadu_si512 reads, unaligned.
            unsafe { _mm512_loadu_si512(a.as_ptr().cast()) }
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn store(v: __m512d) -> [f64; 8] {
            let mut out = [0.0; 8];
            // SAFETY: `out` is the eight f64 _mm512_storeu_pd writes, unaligned.
            unsafe { _mm512_storeu_pd(out.as_mut_ptr(), v) };
            out
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn add(a: __m512d, b: __m512d) -> __m512d {
            _mm512_add_pd(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn sub(a: __m512d, b: __m512d) -> __m512d {
            _mm512_sub_pd(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn mul(a: __m512d, b: __m512d) -> __m512d {
            _mm512_mul_pd(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn div(a: __m512d, b: __m512d) -> __m512d {
            _mm512_div_pd(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn mul_add(a: __m512d, b: __m512d, c: __m512d) -> __m512d {
            // VFMADD: a·b + c, rounded once.
            _mm512_fmadd_pd(a, b, c)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn abs(a: __m512d) -> __m512d {
            _mm512_abs_pd(a)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn neg(a: __m512d) -> __m512d {
            // AVX-512F has no floating-point XOR (that is AVX-512DQ): flip the
            // sign bit in the integer domain.
            _mm512_castsi512_pd(_mm512_xor_si512(
                _mm512_castpd_si512(a),
                _mm512_set1_epi64(i64::MIN),
            ))
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn lt(a: __m512d, b: __m512d) -> Avx512Mask {
            Avx512Mask(_mm512_cmp_pd_mask::<_CMP_LT_OQ>(a, b))
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn le(a: __m512d, b: __m512d) -> Avx512Mask {
            Avx512Mask(_mm512_cmp_pd_mask::<_CMP_LE_OQ>(a, b))
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn select(m: Avx512Mask, a: __m512d, b: __m512d) -> __m512d {
            // VBLENDMPD takes its second operand where the mask bit is set.
            _mm512_mask_blend_pd(m.0, b, a)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn to_bits(a: __m512d) -> __m512i {
            _mm512_castpd_si512(a)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn to_float(a: __m512i) -> __m512d {
            _mm512_castsi512_pd(a)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn and_u(a: __m512i, b: __m512i) -> __m512i {
            _mm512_and_si512(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn or_u(a: __m512i, b: __m512i) -> __m512i {
            _mm512_or_si512(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn sub_u(a: __m512i, b: __m512i) -> __m512i {
            _mm512_sub_epi64(a, b)
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn shr_u(a: __m512i, n: u32) -> __m512i {
            // VPSRLQ by the count in the low 64 bits; 64 or more gives 0.
            _mm512_srl_epi64(a, _mm_cvtsi64_si128(i64::from(n)))
        }
        #[target_feature(enable = "avx512f")]
        #[inline]
        pub(in super::super) fn eq_u(a: __m512i, b: __m512i) -> Avx512Mask {
            Avx512Mask(_mm512_cmpeq_epi64_mask(a, b))
        }
    }
}
