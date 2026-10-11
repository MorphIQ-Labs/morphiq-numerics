//! Safe binary64 SIMD lanes for `morphiq-numerics`.
//!
//! A *backend* is a zero-sized token type implementing [`Simd`]: [`Scalar`]
//! (one lane, everywhere), `Neon` (two lanes, aarch64), `Sse2` (two lanes,
//! x86-64), `Avx2` (four lanes, AVX2 and FMA) and `Avx512` (eight lanes,
//! AVX-512F). A token can only be obtained from its constructor, which checks
//! that the CPU has the backend's features, so holding one proves they are
//! present; every operation takes the token, so no operation can run on a CPU
//! without its instructions. [`dispatch`] picks the widest available backend.
//!
//! Every operation is an IEEE 754 binary64 operation on each lane,
//! round-to-nearest-even, exactly as the scalar `f64` operation computes it:
//! the backends differ in width, never in a lane's result.
//! [`Simd::mul_add`] is fused (one rounding) and returns `None` on backends
//! without a hardware fused multiply-add ([`Simd::FMA`]); it is never emulated.
//!
//! This is the workspace's only crate with `unsafe` code. The safety argument
//! and the API are in
//! [`docs/arch.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/arch.md).
//!
//! The crate is `no_std` and has no dependencies. The `std` feature turns on
//! runtime detection; without it a backend is available only when the target
//! enables its features at compile time.

#![no_std]

#[cfg(any(feature = "std", test))]
extern crate std;

/// Implements each listed `Simd` method by one call to the backend's
/// `#[target_feature]` helper of the same name.
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "sse2")
))]
macro_rules! forward {
    ($module:ident; $( fn $name:ident($($arg:ident: $ty:ty),*) -> $ret:ty; )*) => {
        $(
            #[inline(always)]
            fn $name(self, $($arg: $ty),*) -> $ret {
                // SAFETY: the helper's only precondition is that the CPU has
                // the features it is compiled with, and `self` is a token
                // that exists only when it does: constructed after detection,
                // or where the target itself enables them.
                unsafe { $module::$name($($arg),*) }
            }
        )*
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod neon;
mod scalar;
#[cfg(test)]
mod tests;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
mod x86_64;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub use neon::{Neon, NeonMask};
pub use scalar::Scalar;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
pub use x86_64::{Avx2, Avx2Mask, Avx512, Avx512Mask, Sse2, Sse2Mask};

mod sealed {
    /// Only this crate's backends implement [`Simd`](super::Simd).
    pub trait Sealed {}
}

/// An operation generic over the backend, run by [`Simd::vectorize`] or
/// [`dispatch`].
///
/// Mark the implementation of [`with`](WithSimd::with), and every generic
/// function it calls, `#[inline(always)]`: the operation is then compiled
/// inside a function with the backend's target features enabled, and each
/// lane operation becomes one instruction.
pub trait WithSimd {
    /// The operation's result.
    type Output;
    /// Runs the operation on `simd`'s lanes.
    fn with<S: Simd>(self, simd: S) -> Self::Output;
}

/// A backend's lanes and their operations.
///
/// `F` holds [`LANES`](Simd::LANES) binary64 numbers, `U` as many 64-bit words
/// and `M` as many booleans. Each operation acts on every lane independently,
/// as the scalar operation it names: `add` is `a + b` rounded to nearest, ties
/// to even, and so on, with IEEE 754 special values. Comparisons are ordered:
/// false when either operand is NaN.
pub trait Simd: Copy + Send + Sync + core::fmt::Debug + sealed::Sealed + 'static {
    /// The number of lanes.
    const LANES: usize;
    /// The backend's name, for reports.
    const NAME: &'static str;
    /// Whether the backend has a hardware fused multiply-add.
    const FMA: bool;
    /// `LANES` binary64 numbers.
    type F: Copy;
    /// `LANES` 64-bit words.
    type U: Copy;
    /// `LANES` booleans.
    type M: Copy;
    /// `[f64; LANES]`.
    type Array: Copy + Default + AsRef<[f64]> + AsMut<[f64]>;
    /// `[u64; LANES]`.
    type Words: Copy + Default + AsRef<[u64]> + AsMut<[u64]>;

    /// Runs `op` inside a function compiled with this backend's target
    /// features enabled, so that its lane operations inline as single
    /// instructions.
    fn vectorize<W: WithSimd>(self, op: W) -> W::Output;

    /// Every lane `x`.
    fn splat(self, x: f64) -> Self::F;
    /// Every lane `x`.
    fn splat_bits(self, x: u64) -> Self::U;
    /// The lanes of `a`, in order.
    fn load(self, a: Self::Array) -> Self::F;
    /// The lanes of `a`, in order.
    fn load_bits(self, a: Self::Words) -> Self::U;
    /// The lanes of `v`, in order.
    fn store(self, v: Self::F) -> Self::Array;

    /// `a + b`.
    fn add(self, a: Self::F, b: Self::F) -> Self::F;
    /// `a − b`.
    fn sub(self, a: Self::F, b: Self::F) -> Self::F;
    /// `a · b`.
    fn mul(self, a: Self::F, b: Self::F) -> Self::F;
    /// `a / b`.
    fn div(self, a: Self::F, b: Self::F) -> Self::F;
    /// `a·b + c` rounded once, on a backend with a hardware fused
    /// multiply-add ([`FMA`](Simd::FMA)); `None` on one without, which never
    /// emulates it.
    fn mul_add(self, a: Self::F, b: Self::F, c: Self::F) -> Option<Self::F>;
    /// `|a|`: the sign bit cleared.
    fn abs(self, a: Self::F) -> Self::F;
    /// `−a`: the sign bit flipped.
    fn neg(self, a: Self::F) -> Self::F;

    /// `a < b`.
    fn lt(self, a: Self::F, b: Self::F) -> Self::M;
    /// `a ≤ b`.
    fn le(self, a: Self::F, b: Self::F) -> Self::M;
    /// `a ∧ b`.
    fn and_m(self, a: Self::M, b: Self::M) -> Self::M;
    /// `a ∨ b`.
    fn or_m(self, a: Self::M, b: Self::M) -> Self::M;
    /// `¬a`.
    fn not_m(self, a: Self::M) -> Self::M;
    /// Bit `i` set when lane `i` is true; the bits above `LANES` are clear.
    fn mask_bits(self, m: Self::M) -> u64;
    /// `a` where `m` is true, else `b`.
    fn select(self, m: Self::M, a: Self::F, b: Self::F) -> Self::F;

    /// The encoding of `a` (`f64::to_bits`).
    fn to_bits(self, a: Self::F) -> Self::U;
    /// The binary64 number encoded by `a` (`f64::from_bits`).
    fn to_float(self, a: Self::U) -> Self::F;
    /// `a & b`.
    fn and_u(self, a: Self::U, b: Self::U) -> Self::U;
    /// `a | b`.
    fn or_u(self, a: Self::U, b: Self::U) -> Self::U;
    /// `a − b`, wrapping.
    fn sub_u(self, a: Self::U, b: Self::U) -> Self::U;
    /// `a >> n`, logical; zero for `n ≥ 64`.
    fn shr_u(self, a: Self::U, n: u32) -> Self::U;
    /// `a = b`.
    fn eq_u(self, a: Self::U, b: Self::U) -> Self::M;
}

/// Runs `op` on the widest backend this CPU has: AVX-512F, then AVX2 with
/// FMA, then SSE2 on x86-64; NEON on aarch64; otherwise [`Scalar`].
pub fn dispatch<W: WithSimd>(op: W) -> W::Output {
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        if let Some(simd) = Avx512::try_new() {
            return simd.vectorize(op);
        }
        if let Some(simd) = Avx2::try_new() {
            return simd.vectorize(op);
        }
        if let Some(simd) = Sse2::try_new() {
            return simd.vectorize(op);
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        Neon::new().vectorize(op)
    }
    #[cfg(not(all(target_arch = "aarch64", target_feature = "neon")))]
    {
        Scalar::new().vectorize(op)
    }
}
