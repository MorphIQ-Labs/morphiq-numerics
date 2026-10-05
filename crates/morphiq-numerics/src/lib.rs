//! Correctly rounded, target-independent binary64 numerics.
//!
//! This crate is at milestone M0 of its [project plan]: it has no public API
//! yet. Release 0.1 will provide correctly rounded elementary functions,
//! seeded random streams and the normal family, each derived from first
//! principles, with machine-checked error bounds.
//!
//! The crate is `no_std`, has no dependencies and never calls a platform
//! math library, so its results are the same on every target.
//!
//! [project plan]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/PLAN.md

#![no_std]
