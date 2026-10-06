//! Elementary functions, correctly rounded: each returns the binary64 number
//! nearest to the exact result, ties to even, on every target.
//!
//! Each function's derivation, with its certificates, is in `docs/`:
//! [`exp`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md).

pub use crate::exp::exp;
