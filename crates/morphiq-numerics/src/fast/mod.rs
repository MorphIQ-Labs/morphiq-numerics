//! Explicit bounded-approximation primitives alongside the strong APIs.
//!
//! Each function states its accelerated domain. Outside it, the corresponding
//! strong API supplies its existing result and special-value semantics.
//! The slice APIs preserve this namespace's scalar bits. They do not promise
//! the strong API's bits or correctly rounded results in the accelerated domain.
//! See `docs/fast.md` for the bounds and their derivation.

pub mod elementary;
#[cfg(feature = "simd")]
mod lanes;
pub mod normal;

#[cfg(test)]
mod tests;
