//! Draft approximations assembled from Numerics' generated table kernels.
//!
//! The intended bounds below remain subject to the draft's proof, source-binding
//! and native qualification work. They are not whole-domain rounding claims.

/// Exact `2^-33`, the lower magnitude screen of these approximation domains.
pub(super) const MIN_MAGNITUDE: f64 = f64::from_bits((1023_u64 - 33) << 52);

/// Scaled complementary error function, `exp(x²) erfc(x)`.
///
/// The draft targets relative error at most `2^-51` on
/// `-0.5 <= x < 16`, excluding `|x| < 2^-33`. On that domain it sums the
/// two words of the existing generated table polynomial. All other inputs
/// use [`crate::normal::erfcx`], retaining its special-value semantics.
#[must_use]
#[inline]
pub fn erfcx(x: f64) -> f64 {
    if (-0.5..16.0).contains(&x) && x.abs() >= MIN_MAGNITUDE {
        let (hi, lo) = crate::erfcx::t_eval(x);
        hi + lo
    } else {
        crate::normal::erfcx(x)
    }
}

/// Standard-normal cumulative distribution, `P(Z <= x)`.
///
/// The draft targets absolute error at most `2^-49` on
/// `2^-33 <= |x| <= 8`. It uses the mathematical identity
/// `Phi(-a) = 0.5 * exp(-a²/2) * erfcx(a/sqrt(2))` for `a = |x|`,
/// with the generated high word of `1/sqrt(2)` and the table polynomial.
/// Other inputs use [`crate::normal::norm_cdf`], retaining its special values.
#[must_use]
#[inline]
pub fn norm_cdf(x: f64) -> f64 {
    let a = x.abs();
    if !(MIN_MAGNITUDE..=8.0).contains(&a) {
        return crate::normal::norm_cdf(x);
    }
    let exponential = super::elementary::exp((-0.5 * a) * a);
    let scaled = a * crate::normal_distribution::INV_SQRT2_HIGH;
    // The composition needs the table below erfcx's public magnitude screen.
    let (hi, lo) = crate::erfcx::t_eval(scaled);
    let lower = (0.5 * exponential) * (hi + lo);
    if x < 0.0 { lower } else { 1.0 - lower }
}

/// Apply [`erfcx`] to a slice, preserving its scalar result bits.
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
    crate::lanes::map::<super::lanes::Erfcx>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = erfcx(x);
    }
}

/// Apply [`norm_cdf`] to a slice, preserving its scalar result bits.
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
    crate::lanes::map::<super::lanes::Cdf>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = norm_cdf(x);
    }
}
