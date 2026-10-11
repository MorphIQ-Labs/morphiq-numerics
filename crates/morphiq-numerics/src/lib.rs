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
//!   stated domain of correct rounding, and `exp_slice`, `ln_slice` and
//!   `ln_1p_slice`, which return the same bits for a whole slice, in SIMD
//!   lanes with the `simd` feature;
//! - [`log_space`]: `log_sum_exp` and `log_diff_exp`, logarithms of sums and
//!   differences of exponentials, within proved error bounds, with `−∞` as
//!   exact zero mass, and `log_sum_exp_pairs`, which returns `log_sum_exp`'s
//!   bits for several pairs at once, in SIMD lanes with the `simd` feature;
//! - [`normal`]: `log_norm_pdf`, the logarithm of the standard normal
//!   density, correctly rounded wherever its rounding test decides;
//! - [`random`]: seeded SplitMix64 and xoshiro256++ streams, with exact
//!   unit uniforms and Box–Muller normal pairs;
//! - [`reduce`]: sums, dot products and sums of squares in a specified order,
//!   with compensated variants as accurate as twice the working precision;
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, forbids `unsafe` and never calls a platform math
//! library, so its results are the same on every target. Its one dependency,
//! optional behind the `simd` feature, is the first-party
//! `morphiq-numerics-arch`, which holds the lane intrinsics.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(test)]
extern crate std;

pub mod double_word;
pub mod eft;
pub mod elementary;
mod exp;
mod exp2;
mod expm1;
#[cfg(test)]
mod internal_crosscheck;
#[cfg(feature = "simd")]
mod lanes;
mod ln;
mod log2;
mod log_norm_pdf;
pub mod log_space;
pub mod normal;
mod q128;
mod q256;
pub mod random;
pub mod reduce;
mod sqrt;
#[cfg(test)]
mod test_exact;
mod trig;
pub mod ulp;
