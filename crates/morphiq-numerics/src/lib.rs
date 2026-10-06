//! Correctly rounded, target-independent binary64 numerics.
//!
//! The crate is being built milestone by milestone under its [project plan].
//! It currently provides:
//!
//! - [`eft`]: error-free transforms, the rounded sum or product of two
//!   numbers with its exact rounding error;
//! - [`double_word`]: double-word (`f64 + f64`) arithmetic with proved
//!   relative error bounds;
//! - [`random`]: seeded SplitMix64 and xoshiro256++ streams, with exact
//!   unit uniforms;
//! - [`reduce`]: sums, dot products and sums of squares in a specified order,
//!   with compensated variants as accurate as twice the working precision;
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, has no dependencies and never calls a platform
//! math library, so its results are the same on every target.
//!
//! [project plan]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/PLAN.md

#![no_std]

#[cfg(test)]
extern crate std;

pub mod double_word;
pub mod eft;
pub mod elementary;
mod exp;
mod ln;
mod q128;
pub mod random;
pub mod reduce;
#[cfg(test)]
mod test_exact;
pub mod ulp;
