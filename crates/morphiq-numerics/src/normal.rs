//! Standard-normal densities, probabilities and logarithms, and scaled erfc.
//!
//! Accepted rounding tests return correctly rounded results. The normal
//! distribution functions use Q256 fallbacks with proved error bounds; no
//! whole-domain correct-rounding claim is made. For a finite mathematical
//! result `f`, excluding log-CDF overflow, the result has the form
//! `f * (1 + d) + a`, with `|d| <= 2^-53 + 2^-111` and `|a| <= 2^-1075`.
//! The individual derivations and tighter bounds are in `docs/normal.md`,
//! `docs/log_norm_pdf.md` and `docs/erfcx.md`.
//!
//! Slice functions preserve scalar bits, including signed zeros and NaN
//! encodings, on NEON, SSE2, AVX2+FMA and AVX-512F with the `simd` feature.

pub use crate::log_norm_pdf::log_norm_pdf;

/// The scaled complementary error function.
pub use crate::erfcx::erfcx;

/// Apply [`erfcx`] to a slice, preserving the scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn erfcx_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "erfcx_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::erfcx::lanes::Erfcx>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = erfcx(x);
    }
}

/// The standard-normal density, `exp(-x²/2) / sqrt(2π)`.
///
/// Both infinities give positive zero. Both signed zeros give `1/sqrt(2π)`
/// rounded to binary64. NaN encodings are preserved.
/// See the [module assurance bounds](self).
#[inline]
pub fn norm_pdf(x: f64) -> f64 {
    crate::normal_distribution::evaluate(crate::normal_distribution::Operation::Pdf, x)
}

/// Apply [`norm_pdf`] to a slice, preserving scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn norm_pdf_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "norm_pdf_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::normal_distribution::lanes::Normal<0>>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = norm_pdf(x);
    }
}

/// The standard-normal cumulative distribution, `P(Z <= x)`.
///
/// Negative infinity gives positive zero; positive infinity gives one.
/// Both signed zeros give one half. NaN encodings are preserved.
/// For a small upper-tail probability, use [`norm_ccdf`] directly.
/// See the [module assurance bounds](self).
#[inline]
pub fn norm_cdf(x: f64) -> f64 {
    crate::normal_distribution::evaluate(crate::normal_distribution::Operation::Cdf, x)
}

/// Apply [`norm_cdf`] to a slice, preserving scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn norm_cdf_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "norm_cdf_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::normal_distribution::lanes::Normal<1>>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = norm_cdf(x);
    }
}

/// The standard-normal complementary distribution, `P(Z > x)`.
///
/// Evaluates the reflected CDF without subtracting a rounded CDF from one.
/// Negative infinity gives one; positive infinity gives positive zero.
/// Both signed zeros give one half. NaN encodings are preserved.
/// See the [module assurance bounds](self).
#[inline]
pub fn norm_ccdf(x: f64) -> f64 {
    if x.is_nan() { x } else { norm_cdf(-x) }
}

/// Apply [`norm_ccdf`] to a slice, preserving scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn norm_ccdf_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "norm_ccdf_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::normal_distribution::lanes::Normal<2>>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = norm_ccdf(x);
    }
}

/// The centered standard-normal CDF, `P(Z <= x) - 1/2`.
///
/// Evaluates the integral from zero directly near zero. Signed zeros are
/// preserved; infinities give one half with the input sign. NaN encodings
/// are preserved. See the [module assurance bounds](self).
#[inline]
pub fn norm_cdf_centered(x: f64) -> f64 {
    crate::normal_distribution::evaluate(crate::normal_distribution::Operation::Centered, x)
}

/// Apply [`norm_cdf_centered`] to a slice, preserving scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn norm_cdf_centered_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "norm_cdf_centered_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::normal_distribution::lanes::Normal<3>>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = norm_cdf_centered(x);
    }
}

/// The natural logarithm of the standard-normal CDF.
///
/// Evaluates the tails without forming an underflowed CDF or subtracting
/// a rounded probability from one. Negative infinity gives negative infinity;
/// positive infinity gives negative zero. Finite negative inputs whose exact
/// log-CDF overflows also give negative infinity. Both signed zeros give
/// `-ln(2)` rounded to binary64. NaN encodings are preserved.
/// See the [module assurance bounds](self).
#[inline]
pub fn log_norm_cdf(x: f64) -> f64 {
    crate::normal_distribution::evaluate(crate::normal_distribution::Operation::LogCdf, x)
}

/// Apply [`log_norm_cdf`] to a slice, preserving scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn log_norm_cdf_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "log_norm_cdf_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::normal_distribution::lanes::Normal<4>>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = log_norm_cdf(x);
    }
}
