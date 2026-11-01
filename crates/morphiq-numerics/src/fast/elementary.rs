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
/// It uses the generated table high words, a split reduction and a bounded
/// cubic polynomial, with exact exponent-field scaling. Other inputs use
/// [`crate::elementary::exp`], including gradual underflow, overflow,
/// infinities and NaN payloads. [`exp_coarse`] trades accuracy for a shorter
/// dependency chain.
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
    slice::<crate::exp::bounded::Cubic>(x, out);
}

/// Exponential with relative error at most `2^-38` for `|x| < 704`.
///
/// The same table high words as [`exp`], with a one-word reduction and a
/// bounded quadratic whose two terms evaluate independently: a shorter
/// dependency chain for callers whose error budget admits `2^-38`. Other
/// inputs use [`crate::elementary::exp`], exactly as [`exp`] does.
#[must_use]
#[inline]
pub fn exp_coarse(x: f64) -> f64 {
    crate::exp::bounded::exp_coarse(x)
}

/// Apply [`exp_coarse`] to a slice, preserving its scalar bits.
///
/// # Panics
/// If the slice lengths differ.
#[inline]
pub fn exp_coarse_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "exp_coarse_slice: slices of different lengths"
    );
    slice::<crate::exp::bounded::Coarse>(x, out);
}

#[inline(always)]
fn slice<E: crate::exp::bounded::Kernel>(x: &[f64], out: &mut [f64]) {
    #[cfg(all(feature = "simd", target_arch = "x86_64", target_feature = "avx512f"))]
    crate::exp::bounded::slice_static_avx512::<E>(x, out);
    #[cfg(all(
        feature = "simd",
        not(all(target_arch = "x86_64", target_feature = "avx512f"))
    ))]
    crate::exp::bounded::slice::<E>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = crate::exp::bounded::entry::<E>(x);
    }
}
