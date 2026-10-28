//! Bounded elementary functions with explicit identities.

/// Exponential with relative error at most `2^-51` for `|x| < 704`.
///
/// It uses the generated table high words and a bounded quartic polynomial,
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
    #[cfg(feature = "simd")]
    crate::exp::bounded::slice(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = exp(x);
    }
}
