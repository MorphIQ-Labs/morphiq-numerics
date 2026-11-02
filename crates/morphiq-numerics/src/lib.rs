//! Target-independent binary64 numerics with explicit numerical contracts.
//!
//! Correct rounding is claimed on established domains; other APIs carry their
//! stated error bounds. The [`fast`] namespace selects bounded approximations
//! explicitly, without changing the existing APIs' guarantees.
//!
//! It provides:
//!
//! - [`eft`]: error-free transforms, the rounded sum or product of two
//!   numbers with its exact rounding error;
//! - [`double_word`]: double-word (`f64 + f64`) arithmetic with proved
//!   relative error bounds, and `DoubleWord::exp_split`, a double-word
//!   exponential with its binary exponent kept apart;
//! - [`elementary`]: `exp`, `expm1`, `exp2`, `ln`, `ln_1p`, `log2`, `log10`,
//!   `sin`, `cos`, `sincos`, `tan`, `sqrt`, `asin`, `asinh` and `atan2`, each
//!   with its stated correct-rounding domain or error bound; slice functions
//!   for `exp`, `exp2`, `expm1`, `ln`, `ln_1p`, `asin`, `asinh` and `atan2`
//!   preserve scalar bits, using SIMD lanes with the `simd` feature;
//! - [`log_space`]: `log_sum_exp` and `log_diff_exp`, logarithms of sums and
//!   differences of exponentials, within proved error bounds, with `−∞` as
//!   exact zero mass; `log_sum_exp_pairs`, which returns `log_sum_exp`'s
//!   bits for several pairs at once, in SIMD lanes with the `simd` feature;
//!   and `log_sum_exp_and_normalize`, a pair's log-sum with the pair divided
//!   by its own sum, sharing one exponential; [`log_space::normalize_log_weights`]
//!   supplies checked slice normalization with a returned error bound;
//! - [`normal`]: `norm_pdf`, `norm_cdf`, `norm_ccdf`, `norm_cdf_centered` and
//!   `log_norm_cdf`, with matching SIMD slice functions and proved error bounds;
//!   `log_norm_pdf`, the logarithm of the standard normal
//!   density, correctly rounded wherever its rounding test decides; and
//!   `erfcx`, the scaled complementary error function, with `erfcx_slice`
//!   for scalar-equivalent SIMD evaluation (see its assurance limits);
//! - [`fast`]: explicit bounded-approximation `exp` and `exp_coarse`
//!   (relative `2^-51` and `2^-38` for `|x| < 704`), `ln`, `erfcx`, `norm_cdf`
//!   and `log_norm_cdf` entries with matching slices; each states its accelerated
//!   domain and delegates other inputs to the corresponding strong API;
//! - [`bivariate_normal`]: the bivariate normal distribution function with an
//!   absolute error bound, and a per-correlation evaluator that reuses its
//!   quadrature table;
//! - [`random`]: seeded SplitMix64 and xoshiro256++ streams, with exact
//!   unit uniforms and Box–Muller normal pairs;
//! - [`reduce`]: sums, dot products and sums of squares in a specified order,
//!   with compensated variants as accurate as twice the working precision;
//! - [`interval`]: finite conservative outward enclosures with typed domain and
//!   range failures; these are not tight directed-rounding operations;
//! - [`linalg::tridiagonal`]: reusable allocation-free Thomas factors for
//!   dominant, sign and general unpivoted matrices, with explicit certificates;
//! - [`ulp`]: units in the last place, and distances measured in them.
//!
//! The crate is `no_std`, forbids `unsafe`, allocates no heap memory and never
//! calls a platform math library. Specified operation sequences preserve its
//! results across targets under the documented floating-point environment.
//! Its one dependency,
//! optional behind the `simd` feature, is the first-party
//! `morphiq-numerics-arch`, which holds the lane intrinsics.

#![no_std]
#![forbid(unsafe_code)]

#[cfg(any(test, feature = "std"))]
extern crate std;

mod asin;
mod asinh;
mod atan2;
pub mod bivariate_normal;
pub mod double_word;
pub mod eft;
pub mod elementary;
mod erfcx;
mod exact;
mod exp;
mod exp2;
mod expm1;
pub mod fast;
#[cfg(test)]
mod internal_crosscheck;
pub mod interval;
#[cfg(feature = "simd")]
mod lanes;
pub mod linalg;
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
