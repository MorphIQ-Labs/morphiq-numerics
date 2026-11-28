//! Sums, dot products and sums of squares over slices, in a specified order,
//! with compensated variants.
//!
//! The slice functions evaluate their terms left to right in one fixed order, so
//! the result is the same on every target. The compensated variants are
//! Ogita, Rump and Oishi's Sum2 and Dot2 ("Accurate sum and dot product",
//! *SIAM J. Sci. Comput.* 26(6), 2005), operation for operation; their results
//! are as accurate as if computed in twice the working precision and rounded
//! once. A NaN result is the first input NaN, unchanged, or the canonical quiet
//! NaN when no input is NaN. The contracts, error bounds and the conditions they
//! need are in
//! [`docs/reduce.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/reduce.md).
//!
//! Here `u = 2^-53`, `γ_k = k·u / (1 − k·u)`, `s` is the exact sum or dot
//! product, and `S` is the sum of the magnitudes of its terms.
//!
//! [`Moments2`] additionally provides checked, mergeable mean and variance
//! statistics with an explicit absolute error bound per readout. Its batch
//! partition and merge order are part of its separate numerical contract.

use crate::eft::{two_prod, two_sum};

mod moments;
pub use moments::{MomentEstimate, Moments2, MomentsError};

/// The quiet NaN returned when the arithmetic itself creates one.
const CANONICAL_NAN: u64 = 0x7ff8_0000_0000_0000;

/// `result`, with a NaN's bits taken from the contract: which operand's payload
/// survives an operation depends on the compiler's operand order, and the NaN
/// an invalid operation creates depends on the processor.
#[inline]
fn defined(result: f64, x: &[f64], y: &[f64]) -> f64 {
    if result.is_nan() {
        nan_result(x, y)
    } else {
        result
    }
}

/// The first NaN term in index order, `x` before `y`, or the canonical NaN.
#[cold]
fn nan_result(x: &[f64], y: &[f64]) -> f64 {
    for i in 0..x.len().max(y.len()) {
        for v in [x.get(i), y.get(i)].into_iter().flatten() {
            if v.is_nan() {
                return *v;
            }
        }
    }
    f64::from_bits(CANONICAL_NAN)
}

/// `x[0] + x[1] + … + x[n-1]`, rounded at each step, left to right:
/// `π_n` of Ogita, Rump and Oishi's Algorithm 4.1. Zero for an empty slice.
///
/// `|sum − s| ≤ γ_{n−1}·S` (their (2.4)), also with underflow, provided no
/// operation overflows.
#[must_use]
pub fn sum(x: &[f64]) -> f64 {
    let Some((&first, rest)) = x.split_first() else {
        return 0.0;
    };
    let mut pi = first;
    for &p in rest {
        pi += p;
    }
    defined(pi, x, &[])
}

/// The compensated sum: Ogita, Rump and Oishi's Algorithm 4.1 (Sum2), in
/// which each rounding error of the plain sum is recovered exactly by
/// [`two_sum`] and the errors are summed in working precision. Zero for an
/// empty slice.
///
/// `|sum2 − s| ≤ u·|s| + γ_{n−1}²·S` (their Proposition 4.5), also with
/// underflow, provided `n·u < 1` and no operation overflows.
#[must_use]
pub fn sum2(x: &[f64]) -> f64 {
    let Some((&first, rest)) = x.split_first() else {
        return 0.0;
    };
    // π_1 = p_1; σ_1 = 0.
    let mut pi = first;
    let mut sigma = 0.0;
    for &p in rest {
        // [π_i, q_i] = TwoSum(π_{i−1}, p_i); σ_i = fl(σ_{i−1} + q_i).
        let (next, q) = two_sum(pi, p);
        pi = next;
        sigma += q;
    }
    // res = fl(π_n + σ_n).
    defined(pi + sigma, x, &[])
}

/// `x[0]·y[0] + … + x[n-1]·y[n-1]`, each product rounded and the products
/// summed left to right: `p` of Ogita, Rump and Oishi's Algorithm 5.3. Zero
/// for empty slices.
///
/// `|dot − xᵀy| ≤ γ_n·|x|ᵀ|y|` when no product underflows (each `x[i]·y[i]` is
/// zero or at least `2^-1022` in magnitude) and no operation overflows.
///
/// # Panics
///
/// If `x` and `y` have different lengths.
#[must_use]
pub fn dot(x: &[f64], y: &[f64]) -> f64 {
    assert_eq!(x.len(), y.len(), "dot: slices of different lengths");
    let mut terms = x.iter().zip(y);
    let Some((&x1, &y1)) = terms.next() else {
        return 0.0;
    };
    let mut p = x1 * y1;
    for (&xi, &yi) in terms {
        p += xi * yi;
    }
    defined(p, x, y)
}

/// The compensated dot product: Ogita, Rump and Oishi's Algorithm 5.3
/// (Dot2), in which each product's rounding error is recovered exactly by
/// [`two_prod`] and each sum's by [`two_sum`]. Zero for empty slices.
///
/// `|dot2 − xᵀy| ≤ u·|xᵀy| + γ_n²·|x|ᵀ|y|` (their Proposition 5.5) when
/// `n·u < 1`, every product `x[i]·y[i]` is within [`two_prod`]'s domain (zero
/// or at least `2^-969` in magnitude), and no operation overflows.
///
/// # Panics
///
/// If `x` and `y` have different lengths.
#[must_use]
pub fn dot2(x: &[f64], y: &[f64]) -> f64 {
    assert_eq!(x.len(), y.len(), "dot2: slices of different lengths");
    let mut terms = x.iter().zip(y);
    let Some((&x1, &y1)) = terms.next() else {
        return 0.0;
    };
    // [p, s] = TwoProduct(x_1, y_1).
    let (mut p, mut s) = two_prod(x1, y1);
    for (&xi, &yi) in terms {
        // [h, r] = TwoProduct(x_i, y_i); [p, q] = TwoSum(p, h);
        // s = fl(s + (q + r)).
        let (h, r) = two_prod(xi, yi);
        let (next, q) = two_sum(p, h);
        p = next;
        s += q + r;
    }
    // res = fl(p + s).
    defined(p + s, x, y)
}

/// `x[0]² + … + x[n-1]²`: [`dot`]`(x, x)`, with its bound, in which
/// `|x|ᵀ|x|` is the exact sum of squares itself.
#[must_use]
pub fn sum_squares(x: &[f64]) -> f64 {
    dot(x, x)
}

/// The compensated sum of squares: [`dot2`]`(x, x)`, with its bound, in which
/// `|x|ᵀ|x|` is the exact sum of squares itself.
#[must_use]
pub fn sum_squares2(x: &[f64]) -> f64 {
    dot2(x, x)
}

/// The largest magnitude `|x[i]|`, exactly. Zero for an empty slice.
///
/// A NaN anywhere makes the result NaN: the first NaN in slice order is
/// returned unchanged, so the result doesn't depend on how a comparison
/// orders NaNs.
#[must_use]
pub fn max_abs(x: &[f64]) -> f64 {
    let mut largest = 0.0_f64;
    for &v in x {
        if v.is_nan() {
            return v;
        }
        let magnitude = v.abs();
        if magnitude > largest {
            largest = magnitude;
        }
    }
    largest
}
