//! Correctly rounded, target-independent binary64 numerics.
//!
//! The crate is being built milestone by milestone under its [project plan].
//! It currently provides:
//!
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, has no dependencies and never calls a platform
//! math library, so its results are the same on every target.
//!
//! [project plan]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/PLAN.md

#![no_std]

pub mod ulp;
