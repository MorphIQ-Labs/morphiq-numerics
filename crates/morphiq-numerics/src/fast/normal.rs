//! Draft approximations assembled from Numerics' generated table kernels.
//!
//! The intended bounds below remain subject to the draft's proof, source-binding
//! and native qualification work. They are not whole-domain rounding claims.

/// Exact `2^-33`, the lower magnitude screen of these approximation domains.
pub(super) const MIN_MAGNITUDE: f64 = f64::from_bits((1023_u64 - 33) << 52);

/// Scaled complementary error function, `exp(x²) erfc(x)`.
///
/// The draft targets relative error at most `2^-51` on
/// `-0.5 <= x < 16`, excluding `|x| < 2^-33`. On that domain it evaluates
/// the high words of the generated table polynomial in adjacent pairs. All other inputs
/// use [`crate::normal::erfcx`], retaining its special-value semantics.
#[must_use]
#[inline]
pub fn erfcx(x: f64) -> f64 {
    if (-0.5..16.0).contains(&x) && x.abs() >= MIN_MAGNITUDE {
        crate::erfcx::bounded::table(x)
    } else {
        crate::normal::erfcx(x)
    }
}

/// Standard-normal cumulative distribution, `P(Z <= x)`.
///
/// The draft targets absolute error at most `2^-49` on
/// `2^-33 <= |x| <= 8`. For `|x| <= 1` it evaluates the generated
/// integrated Gaussian polynomial. For larger arguments it uses the identity
/// `Phi(-a) = 0.5 * exp(-a²/2) * erfcx(a/sqrt(2))` for `a = |x|`,
/// with the generated high word of `1/sqrt(2)` and the table polynomial.
/// Other inputs use [`crate::normal::norm_cdf`], retaining its special values.
#[must_use]
#[inline]
pub fn norm_cdf(x: f64) -> f64 {
    let a = x.abs();
    if !(MIN_MAGNITUDE..=8.0).contains(&a) {
        return norm_cdf_fallback(x);
    }
    if a <= 1.0 {
        return central(x);
    }
    let exponential = super::elementary::exp((-0.5 * a) * a);
    let scaled = a * crate::normal_distribution::INV_SQRT2_HIGH;
    // The composition needs the table below erfcx's public magnitude screen.
    let lower = (0.5 * exponential) * crate::erfcx::bounded::table(scaled);
    if x < 0.0 { lower } else { 1.0 - lower }
}

// Keep the strong entry's register requirements out of the accelerated caller.
#[cold]
#[inline(never)]
fn norm_cdf_fallback(x: f64) -> f64 {
    crate::normal::norm_cdf(x)
}

/// Degree-25 integrated Gaussian Taylor polynomial on |x| <= 1.
#[inline]
pub(super) fn central(x: f64) -> f64 {
    use crate::normal_distribution::{CENTER_HIGH as A, DENSITY_HIGH};
    let z = x * x;
    let zz = z * z;
    let p0 = A[0] + z * A[1];
    let p1 = A[2] + z * A[3];
    let p2 = A[4] + z * A[5];
    let p3 = A[6] + z * A[7];
    let p4 = A[8] + z * A[9];
    let p5 = A[10] + z * A[11];
    let p = p0 + zz * (p1 + zz * (p2 + zz * (p3 + zz * (p4 + zz * (p5 + zz * A[12])))));
    0.5 + (x * DENSITY_HIGH) * p
}

/// Apply [`erfcx`] to a slice, preserving its scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
#[inline]
pub fn erfcx_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "erfcx_slice: slices of different lengths"
    );
    if x.len() <= 8 {
        if !x.is_empty() {
            out[0] = erfcx(x[0]);
        }
        if x.len() >= 2 {
            out[1] = erfcx(x[1]);
        }
        if x.len() >= 3 {
            out[2] = erfcx(x[2]);
        }
        if x.len() >= 4 {
            out[3] = erfcx(x[3]);
        }
        if x.len() >= 5 {
            out[4] = erfcx(x[4]);
        }
        if x.len() >= 6 {
            out[5] = erfcx(x[5]);
        }
        if x.len() >= 7 {
            out[6] = erfcx(x[6]);
        }
        if x.len() == 8 {
            out[7] = erfcx(x[7]);
        }
        return;
    }
    erfcx_slice_loop(x, out);
}

// Keep the long loop's saved registers out of the short-slice caller.
#[inline(never)]
fn erfcx_slice_loop(x: &[f64], out: &mut [f64]) {
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
