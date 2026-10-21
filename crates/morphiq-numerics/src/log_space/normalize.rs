//! Checked log normalization; derivation and bounds in docs/log_normalize.md.

use super::normalize_constants::{MAX_FINITE, RELATIVE, SUBNORMAL_FACTOR};
use super::terms;
use crate::elementary::ln_1p;

/// Maximum number of finite entries covered by the compensated reduction's
/// error proof (docs/log_space.md §4). Structural zeros do not count.
pub const MAX_NORMALIZE_TERMS: usize = MAX_FINITE;

/// Why log weights cannot be normalized under this contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NormalizeError {
    /// Input and output lengths differ.
    LengthMismatch,
    /// Empty input or all entries are negative infinity.
    ZeroMass,
    /// A NaN or positive infinity, at this zero-based index.
    InvalidWeight(usize),
    /// More finite entries than [`MAX_NORMALIZE_TERMS`].
    TooManyFiniteTerms,
    /// A positive-mass component's rounded normalized log is not finite,
    /// at this zero-based index. It is never silently turned into zero mass.
    Unrepresentable(usize),
}

/// Metadata from one successful [`normalize_log_weights`] call.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LogNormalization {
    log_sum: f64,
    max_absolute_error: f64,
}

impl LogNormalization {
    /// Log total mass, bit-identical to [`super::log_sum_exp`] on the input.
    /// Its error contract is docs/log_space.md §4, separately from the bound
    /// on normalized components returned by [`Self::max_absolute_error`].
    #[must_use]
    pub fn log_sum(self) -> f64 {
        self.log_sum
    }

    /// Upper bound on every finite output's absolute log-probability error.
    /// Negative-infinity entries are exact structural zeros and have no error.
    /// This is a numerical bound, not statistical uncertainty.
    #[must_use]
    pub fn max_absolute_error(self) -> f64 {
        self.max_absolute_error
    }
}

/// Normalize relative log weights into `output`, without allocation.
///
/// For each finite `x[i]`, computes `x[i] - ln(sum(exp(x)))` via the shifted
/// form `(x[i] - max(x)) - ln(sum(exp(x - max(x))))`. It never subtracts the
/// rounded, unshifted log-sum from an input. Exact zero mass is negative
/// infinity; every finite input retains a finite, nonpositive output on success.
/// A single finite entry normalizes to positive zero exactly.
///
/// The documented error is bounded, not correctly rounded: with `u = 2^-53`,
/// `n` finite entries, and exact normalized log `p[i]`, the absolute error is
/// at most `(4 + 2^-7) u |p[i]| + 2n * 2^-1074`. The returned radius bounds
/// all finite components using their computed values, rounded outwards.
/// See `docs/log_normalize.md` for the exact-rational composition check.
///
/// Work is O(input length); auxiliary storage is O(1) (fixed lane scratch
/// with `simd`). All targets and feature combinations return identical bits.
/// Existing pair normalization has a different operation sequence and is
/// unchanged; this API makes no bit-parity promise with that pair output.
///
/// # Errors
///
/// [`NormalizeError`] for invalid shape, zero mass, NaN/positive infinity,
/// too many finite terms or an unrepresentable normalized component.
/// **The output is unchanged on every error.** In mixed-invalid inputs,
/// shape is checked first, then input classification in index order, then
/// output representability in index order.
pub fn normalize_log_weights(
    x: &[f64],
    output: &mut [f64],
) -> Result<LogNormalization, NormalizeError> {
    // A singleton is the exact closed form, including a signed-zero log total.
    if let ([value], [slot]) = (x, &mut *output)
        && value.is_finite()
    {
        *slot = 0.0;
        return Ok(LogNormalization {
            log_sum: *value,
            max_absolute_error: 0.0,
        });
    }
    if let ([a, b], [_, _]) = (x, &*output)
        && a.is_finite()
        && b.is_finite()
    {
        let (values, result) = finite_pair(*a, *b)?;
        output.copy_from_slice(&values);
        return Ok(result);
    }
    if x.len() != output.len() {
        return Err(NormalizeError::LengthMismatch);
    }
    let mut maximum = f64::NEG_INFINITY;
    let mut first_maximum = 0;
    let mut finite = 0usize;
    for (index, &value) in x.iter().enumerate() {
        if value == f64::NEG_INFINITY {
            continue;
        }
        if !value.is_finite() {
            return Err(NormalizeError::InvalidWeight(index));
        }
        finite += 1;
        if finite > MAX_NORMALIZE_TERMS {
            return Err(NormalizeError::TooManyFiniteTerms);
        }
        if value > maximum {
            maximum = value;
            first_maximum = index;
        }
    }
    if finite == 0 {
        return Err(NormalizeError::ZeroMass);
    }
    let tail = terms(x, maximum, first_maximum);
    let correction = ln_1p(tail);
    let log_sum = if tail == 0.0 {
        maximum
    } else {
        maximum + correction
    };

    // Validate every output before writing any, preserving caller storage on
    // failure. Subtract in the shifted domain even for huge common offsets.
    let mut largest_magnitude = 0.0_f64;
    for (index, &value) in x.iter().enumerate() {
        if value == f64::NEG_INFINITY {
            continue;
        }
        let normalized = (value - maximum) - correction;
        if !normalized.is_finite() {
            return Err(NormalizeError::Unrepresentable(index));
        }
        largest_magnitude = largest_magnitude.max(-normalized);
    }
    for (&value, slot) in x.iter().zip(output) {
        *slot = (value - maximum) - correction;
    }
    // 8u is the least power-of-two multiple of u dominating C/(1-Cu),
    // C = 4 + 2^-7. The 4n subnormal allowance dominates 2n/(1-Cu).
    // Both inequalities are checked in generators/log_space_bounds.py.
    let max_absolute_error = radius(finite, largest_magnitude);
    Ok(LogNormalization {
        log_sum,
        max_absolute_error,
    })
}

// Same arithmetic as the slice path, specialized to two finite inputs. Only
// the smaller normalized component can overflow; validate it before writing.
fn finite_pair(a: f64, b: f64) -> Result<([f64; 2], LogNormalization), NormalizeError> {
    let hi = usize::from(b > a);
    let (maximum, lower) = if hi == 0 { (a, b) } else { (b, a) };
    let (dh, dl) = crate::eft::two_sum(lower, -maximum);
    let mut sum = super::Sum2Stream::default();
    sum.add(crate::elementary::exp(dh), dl);
    let tail = sum.total();
    let correction = ln_1p(tail);
    let low = dh - correction;
    if !low.is_finite() {
        return Err(NormalizeError::Unrepresentable(1 - hi));
    }
    let mut values = [0.0; 2];
    values[hi] = 0.0 - correction;
    values[1 - hi] = low;
    Ok((
        values,
        LogNormalization {
            log_sum: if tail == 0.0 {
                maximum
            } else {
                maximum + correction
            },
            max_absolute_error: radius(2, -low),
        },
    ))
}

fn radius(finite: usize, largest_magnitude: f64) -> f64 {
    if finite == 1 {
        0.0
    } else {
        let relative = (RELATIVE * largest_magnitude).next_up();
        let absolute = f64::from_bits((SUBNORMAL_FACTOR * finite) as u64);
        (relative + absolute).next_up()
    }
}
