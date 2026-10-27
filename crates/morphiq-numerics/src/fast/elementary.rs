//! Bounded elementary functions with explicit identities.

/// Exponential with a draft target of relative error at most `2^-51`
/// for `|x| < 704`, pending formal entry and source-binding qualification.
///
/// The generated stage-A polynomial is shared with the strong exponential.
/// Its result is rounded once without a correct-rounding decision or a
/// higher-precision retry. Other inputs use [`crate::elementary::exp`],
/// including gradual underflow, overflow, infinities and NaN payloads.
#[must_use]
#[inline]
pub fn exp(x: f64) -> f64 {
    if x.abs() < 704.0 {
        let stage = crate::exp::Stages::of(x);
        let (h, l) = stage.a_value();
        let scale = f64::from_bits(((stage.exponent() + 1023) as u64) << 52);
        (h + l) * scale
    } else {
        crate::elementary::exp(x)
    }
}

/// Apply [`exp`] to a slice, preserving its scalar bits.
///
/// # Panics
/// If the slice lengths differ.
pub fn exp_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(x.len(), out.len(), "exp_slice: slices of different lengths");
    #[cfg(feature = "simd")]
    crate::lanes::map::<super::lanes::Exp>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = exp(x);
    }
}
