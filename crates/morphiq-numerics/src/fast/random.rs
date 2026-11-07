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
/// rejection sampling or precision refinement. It uses a radius-specific logarithm
/// and bounded angular polynomials; correctly rounded results are not promised.
#[must_use]
#[inline(always)]
pub fn normal_pair(w1: u64, w2: u64) -> (f64, f64) {
    let (octant, phi) = crate::random::folded_angle(w2 >> 11);
    let (c, s) = components(crate::random::unit_open(w1), phi);
    crate::random::orient(octant, s, c)
}

/// The continuous-input sequence transcribed by `FastRandom.bm_pair64`.
/// Callers establish `2^-53 <= u <= 1 - 2^-53` with the exact open-uniform map.
#[inline(always)]
pub(crate) fn components(u: f64, phi: f64) -> (f64, f64) {
    // The exact uniform range permits the radius-specific logarithm bound.
    // The near-one cells retain the complete compensated sequence.
    let radius = crate::exact::sqrt(-2.0 * crate::ln::bounded::normal_pair_log(u));
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
    match w1.len() {
        0 => (),
        1 => out[0] = normal_pair(w1[0], w2[0]),
        _ => bulk_pairs(w1, w2, out),
    }
}

// Keep the bulk loop's hoisted constants and register saves off a tiny call.
#[inline(never)]
fn bulk_pairs(w1: &[u64], w2: &[u64], out: &mut [(f64, f64)]) {
    for ((&a, &b), pair) in w1.iter().zip(w2).zip(out) {
        *pair = normal_pair(a, b);
    }
}

#[cfg(test)]
mod tests {
    use crate::test_exact::{Exact, entries, field, word};
    use core::cmp::Ordering;

    #[test]
    fn private_radius_meets_the_independent_oracle_at_reduction_boundaries() {
        let fixture = include_str!("../../../reference/fixtures/fast_pair_radius.json");
        for row in entries(fixture, &["rows"]) {
            let input = u64::from_str_radix(field(row, "word"), 16).unwrap();
            let u = crate::random::unit_open(input);
            let logarithm = crate::ln::bounded::normal_pair_log(u);
            let radius = crate::exact::sqrt(-2.0 * logarithm);
            let near_one = u >= 511.0 / 512.0;
            if near_one {
                assert_eq!(
                    logarithm.to_bits(),
                    super::super::elementary::ln(u).to_bits()
                );
            }
            // Outside the cancellation region the radius has a separate
            // 2^-40 budget. Near one retains the existing composition bound.
            let bound = Exact::of_hex("1", if near_one { -38 } else { -40 });
            let error = Exact::of_f64(radius)
                .sub(&Exact::of_f64(word(row, "radius")))
                .abs();
            assert!(radius.is_finite() && radius > 0.0);
            assert_ne!(error.cmp(&bound), Ordering::Greater, "word {input:016x}");
        }
    }
}
