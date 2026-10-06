//! Elementary functions, correctly rounded: each returns the binary64 number
//! nearest to the exact result, ties to even, on every target.
//!
//! Each function's derivation, with its certificates, is in `docs/`:
//! [`exp`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md),
//! [`exp2`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp2.md),
//! [`expm1`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/expm1.md),
//! [`ln` and `ln_1p`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/ln.md),
//! [`log2` and `log10`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/log2.md),
//! [`sin`, `cos`, `sincos` and `tan`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sin_cos.md).

pub use crate::exp::exp;
pub use crate::exp2::exp2;
pub use crate::expm1::expm1;
pub use crate::ln::{ln, ln_1p};
pub use crate::log2::{log2, log10};
pub use crate::trig::{cos, sin, sincos, tan};
