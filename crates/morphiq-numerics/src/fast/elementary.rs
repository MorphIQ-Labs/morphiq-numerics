//! Bounded elementary functions with explicit identities.

/// Natural logarithm with absolute error at most
/// `2^-53 * |ln(x)| + 2^-65` for every positive finite binary64 input.
///
/// The bound is in natural-log units, includes final rounding, and refers to
/// the exact input. `ln(1) = +0` exactly. Subnormals are normalized exactly;
/// zero, negative inputs, infinities and NaNs retain [`crate::elementary::ln`]
/// semantics. Correct or faithful rounding is not promised.
#[must_use]
#[inline]
pub fn ln(x: f64) -> f64 {
    crate::ln::bounded::ln(x)
}

/// Apply [`ln`] to a slice, preserving its scalar bits.
///
/// # Panics
/// If the slice lengths differ.
#[inline]
pub fn ln_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(x.len(), out.len(), "ln_slice: slices of different lengths");
    #[cfg(feature = "simd")]
    crate::ln::bounded::slice(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = ln(x);
    }
}

/// Exponential with relative error at most `2^-51` for `|x| < 704`.
///
/// It uses the generated table high words and a bounded cubic polynomial,
/// with exact exponent-field scaling. Other inputs use [`crate::elementary::exp`],
/// including gradual underflow, overflow, infinities and NaN payloads.
#[must_use]
#[inline]
pub fn exp(x: f64) -> f64 {
    crate::exp::bounded::exp(x)
}

/// Apply [`exp`] to a slice, preserving its scalar bits.
///
/// # Panics
/// If the slice lengths differ.
#[inline]
pub fn exp_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(x.len(), out.len(), "exp_slice: slices of different lengths");
    #[cfg(all(feature = "simd", target_arch = "x86_64", target_feature = "avx512f"))]
    crate::exp::bounded::slice_static_avx512(x, out);
    #[cfg(all(
        feature = "simd",
        not(all(target_arch = "x86_64", target_feature = "avx512f"))
    ))]
    crate::exp::bounded::slice(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = exp(x);
    }
}
