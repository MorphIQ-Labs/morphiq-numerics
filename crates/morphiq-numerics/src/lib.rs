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
//!   stated domain of correct rounding;
//! - [`log_space`]: `log_sum_exp` and `log_diff_exp`, logarithms of sums and
//!   differences of exponentials, within proved error bounds, with `−∞` as
//!   exact zero mass;
//! - [`random`]: seeded SplitMix64 and xoshiro256++ streams, with exact
//!   unit uniforms and Box–Muller normal pairs;
//! - [`reduce`]: sums, dot products and sums of squares in a specified order,
//!   with compensated variants as accurate as twice the working precision;
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, has no dependencies and never calls a platform
//! math library, so its results are the same on every target.

#![no_std]

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
mod ln;
mod log2;
pub mod log_space;
mod q128;
mod q256;
pub mod random;
pub mod reduce;
mod sqrt;
#[cfg(test)]
mod test_exact;
mod trig;
pub mod ulp;
