//! Correctly rounded, target-independent binary64 numerics.
//!
//! It provides:
//!
//! - [`eft`]: error-free transforms, the rounded sum or product of two
//!   numbers with its exact rounding error;
//! - [`double_word`]: double-word (`f64 + f64`) arithmetic with proved
//!   relative error bounds;
//! - [`elementary`]: correctly rounded `exp`, `expm1`, `exp2`, `ln`, `ln_1p`,
//!   `log2`, `log10`, `sin`, `cos`, `sincos`, `tan` and `sqrt`, each with its
//!   stated domain of correct rounding, and `exp_slice`, `exp2_slice`, `expm1_slice`, `ln_slice` and
//!   `ln_1p_slice`, which return the same bits for a whole slice, in SIMD
//!   lanes with the `simd` feature;
//! - [`log_space`]: `log_sum_exp` and `log_diff_exp`, logarithms of sums and
//!   differences of exponentials, within proved error bounds, with `−∞` as
//!   exact zero mass; `log_sum_exp_pairs`, which returns `log_sum_exp`'s
//!   bits for several pairs at once, in SIMD lanes with the `simd` feature;
//!   and `log_sum_exp_and_normalize`, a pair's log-sum with the pair divided
//!   by its own sum, sharing one exponential;
//! - [`normal`]: `norm_pdf`, `norm_cdf`, `norm_ccdf`, `norm_cdf_centered` and
//!   `log_norm_cdf`, with matching SIMD slice functions and proved error bounds;
//!   `log_norm_pdf`, the logarithm of the standard normal
//!   density, correctly rounded wherever its rounding test decides; and
//!   `erfcx`, the scaled complementary error function, with `erfcx_slice`
//!   for scalar-equivalent SIMD evaluation (see its assurance limits);
//! - [`random`]: seeded SplitMix64 and xoshiro256++ streams, with exact
//!   unit uniforms and Box–Muller normal pairs;
//! - [`reduce`]: sums, dot products and sums of squares in a specified order,
//!   with compensated variants as accurate as twice the working precision;
//! - [`interval`]: finite conservative outward enclosures with typed domain and
//!   range failures; these are not tight directed-rounding operations;
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, forbids `unsafe` and never calls a platform math
//! library, so its results are the same on every target. Its one dependency,
//! optional behind the `simd` feature, is the first-party
//! `morphiq-numerics-arch`, which holds the lane intrinsics.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(any(test, feature = "std"))]
extern crate std;

mod asin;
mod asinh;
mod atan2;
pub mod double_word;
pub mod eft;
pub mod elementary;
mod erfcx;
mod exact;
mod exp;
mod exp2;
mod expm1;
#[cfg(test)]
mod internal_crosscheck;
pub mod interval;
#[cfg(feature = "simd")]
mod lanes;
mod ln;
mod log2;
mod log_norm_pdf;
pub mod log_space;
pub mod normal;
mod normal_distribution;
mod q128;
mod q256;
pub mod random;
pub mod reduce;
mod sqrt;
#[cfg(test)]
mod test_exact;
mod trig;
pub mod ulp;
