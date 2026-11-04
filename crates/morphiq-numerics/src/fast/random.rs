//! Bounded Box–Muller pairs with the strong pair's uniform mapping and octants.
//!
//! The derivation, generated angular polynomials and error composition are in
//! [`docs/fast_random.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/fast_random.md).

use super::random_tables::{COS, SIN};

/// Maximum absolute difference of each output from
/// [`crate::random::normal_pair`] for the same two words: `2^-38`.
pub const ABSOLUTE_ERROR_BOUND: f64 = f64::from_bits((1023 - 38) << 52);

#[inline(always)]
fn polynomial(z: f64, coefficients: &[f64; 6]) -> f64 {
    let mut p = coefficients[5];
    for &c in coefficients[..5].iter().rev() {
        p = c + z * p;
    }
    p
}

/// `(sin(phi), cos(phi))` on the folded angle's `[0, RN(pi/4)]` domain.
#[inline(always)]
pub(crate) fn angular(phi: f64) -> (f64, f64) {
    let z = phi * phi;
    (phi * polynomial(z, &SIN), polynomial(z, &COS))
}

/// Approximate Box–Muller pair from two words, with each output within
/// [`ABSOLUTE_ERROR_BOUND`] of [`crate::random::normal_pair`] on the same words.
///
/// Uses the same exact uniforms and octant fold as the strong pair. Every
/// input pair produces finite outputs; angular zeros retain their sign bits.
/// This function consumes no additional random words and performs no
/// rejection sampling or precision refinement. It uses the fast logarithm
/// and bounded angular polynomials; correctly rounded results are not promised.
#[must_use]
#[inline]
pub fn normal_pair(w1: u64, w2: u64) -> (f64, f64) {
    let (octant, phi) = crate::random::folded_angle(w2 >> 11);
    let (c, s) = components(crate::random::unit_open(w1), phi);
    crate::random::orient(octant, s, c)
}

/// The continuous-input sequence transcribed by `FastRandom.bm_pair64`.
#[inline(always)]
pub(crate) fn components(u: f64, phi: f64) -> (f64, f64) {
    let radius = crate::exact::sqrt(-2.0 * super::elementary::ln(u));
    let (s, c) = angular(phi);
    (radius * c, radius * s)
}

/// Apply [`normal_pair`] to the corresponding words, preserving scalar bits.
///
/// This implementation uses scalar calls on every backend.
///
/// # Panics
/// If the input and output lengths differ. All lengths are checked before
/// any output is written.
#[inline]
pub fn normal_pair_slice(w1: &[u64], w2: &[u64], out: &mut [(f64, f64)]) {
    assert_eq!(w1.len(), w2.len(), "normal_pair_slice: word lengths differ");
    assert_eq!(
        w1.len(),
        out.len(),
        "normal_pair_slice: output length differs"
    );
    for ((&a, &b), pair) in w1.iter().zip(w2).zip(out) {
        *pair = normal_pair(a, b);
    }
}
