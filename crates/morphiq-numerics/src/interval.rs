//! Finite conservative binary64 enclosures; see `docs/interval.md`.
//!
//! Endpoint operations use round-to-nearest and then one outward neighbour.
//! These are enclosing intervals, not claims of tightest directed rounding.

use crate::elementary::{exp, ln};

/// A finite closed interval with ordered endpoints.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FiniteInterval {
    lower: f64,
    upper: f64,
}

/// An enclosure cannot be represented under the finite-interval contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntervalError {
    /// Nonfinite or reversed constructor endpoints.
    InvalidBounds,
    /// The interval includes an argument outside the operation's domain.
    Domain,
    /// An operation or outward neighbour has a nonfinite endpoint.
    Range,
}

impl FiniteInterval {
    /// Construct from finite endpoints with `lower <= upper`.
    ///
    /// # Errors
    /// [`IntervalError::InvalidBounds`] for reversed or nonfinite endpoints.
    pub fn new(lower: f64, upper: f64) -> Result<Self, IntervalError> {
        if !(lower.is_finite() && upper.is_finite() && lower <= upper) {
            return Err(IntervalError::InvalidBounds);
        }
        Ok(Self { lower, upper })
    }

    /// The exact singleton at a finite binary64 input.
    ///
    /// # Errors
    /// [`IntervalError::InvalidBounds`] for nonfinite input.
    pub fn point(value: f64) -> Result<Self, IntervalError> {
        Self::new(value, value)
    }

    /// Lower endpoint.
    #[must_use]
    pub const fn lower(self) -> f64 {
        self.lower
    }
    /// Upper endpoint.
    #[must_use]
    pub const fn upper(self) -> f64 {
        self.upper
    }

    /// Whether this interval contains `value`; NaN and infinities are outside.
    #[must_use]
    pub fn contains(self, value: f64) -> bool {
        self.lower <= value && value <= self.upper
    }

    /// Exact interval negation.
    #[must_use]
    pub fn negated(self) -> Self {
        Self {
            lower: -self.upper,
            upper: -self.lower,
        }
    }

    /// Exact range of absolute value on the interval.
    #[must_use]
    pub fn abs(self) -> Self {
        let lower = if self.lower >= 0.0 {
            self.lower.abs()
        } else if self.upper <= 0.0 {
            self.upper.abs()
        } else {
            0.0
        };
        Self {
            lower,
            upper: self.lower.abs().max(self.upper.abs()),
        }
    }

    /// Exact interval range of the pointwise maximum of two independent values.
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        Self {
            lower: max_canonical_zero(self.lower, other.lower),
            upper: max_canonical_zero(self.upper, other.upper),
        }
    }

    /// Enclose every pairwise sum.
    ///
    /// # Errors
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_add(self, other: Self) -> Result<Self, IntervalError> {
        outward(self.lower + other.lower, self.upper + other.upper)
    }

    /// Enclose every pairwise difference.
    ///
    /// # Errors
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_sub(self, other: Self) -> Result<Self, IntervalError> {
        outward(self.lower - other.upper, self.upper - other.lower)
    }

    /// Enclose every pairwise product, including intervals crossing zero.
    ///
    /// # Errors
    /// [`IntervalError::Range`] if any outward corner is nonfinite.
    pub fn checked_mul(self, other: Self) -> Result<Self, IntervalError> {
        let products = [
            self.lower * other.lower,
            self.lower * other.upper,
            self.upper * other.lower,
            self.upper * other.upper,
        ];
        let mut result = outward(products[0], products[0])?;
        for product in &products[1..] {
            let corner = outward(*product, *product)?;
            result.lower = result.lower.min(corner.lower);
            result.upper = result.upper.max(corner.upper);
        }
        Ok(result)
    }

    /// Enclose every pairwise quotient. The denominator must exclude zero.
    ///
    /// The reciprocal endpoints are widened first, followed by multiplication.
    /// A representable exact quotient can still return a range error if the
    /// intermediate reciprocal cannot be enclosed finitely.
    ///
    /// # Errors
    /// [`IntervalError::Domain`] if the denominator contains zero;
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_div(self, other: Self) -> Result<Self, IntervalError> {
        if other.contains(0.0) {
            return Err(IntervalError::Domain);
        }
        let reciprocal = outward(1.0 / other.upper, 1.0 / other.lower)?;
        self.checked_mul(reciprocal)
    }

    /// Enclose the square, retaining an exact zero lower bound when appropriate.
    ///
    /// # Errors
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_square(self) -> Result<Self, IntervalError> {
        let magnitude = self.abs();
        let result = outward(
            magnitude.lower * magnitude.lower,
            magnitude.upper * magnitude.upper,
        )?;
        Ok(Self {
            lower: result.lower.max(0.0),
            upper: result.upper,
        })
    }

    /// Enclose the natural logarithm on a strictly positive interval.
    ///
    /// # Errors
    /// [`IntervalError::Domain`] unless the lower endpoint is positive;
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_ln(self) -> Result<Self, IntervalError> {
        if self.lower <= 0.0 {
            return Err(IntervalError::Domain);
        }
        outward(ln(self.lower), ln(self.upper))
    }

    /// Enclose the exponential, including positive values below binary64 range.
    ///
    /// Underflow gives an interval with zero lower endpoint and positive upper
    /// endpoint; it never turns a positive exact value into an exact zero point.
    ///
    /// # Errors
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_exp(self) -> Result<Self, IntervalError> {
        let result = outward(exp(self.lower), exp(self.upper))?;
        Ok(Self {
            lower: result.lower.max(0.0),
            upper: result.upper,
        })
    }

    /// Enclose the square root of a nonnegative interval.
    ///
    /// # Errors
    /// [`IntervalError::Domain`] if the lower endpoint is negative;
    /// [`IntervalError::Range`] if a finite outward enclosure is unavailable.
    pub fn checked_sqrt(self) -> Result<Self, IntervalError> {
        if self.lower < 0.0 {
            return Err(IntervalError::Domain);
        }
        let result = outward(
            crate::exact::sqrt(self.lower),
            crate::exact::sqrt(self.upper),
        )?;
        Ok(Self {
            lower: result.lower.max(0.0),
            upper: result.upper,
        })
    }
}

// f64::max permits either zero sign on equal zeros. Fix it explicitly for
// the target-independent endpoint-bit contract.
fn max_canonical_zero(a: f64, b: f64) -> f64 {
    if a == 0.0 && b == 0.0 { 0.0 } else { a.max(b) }
}

/// Each finite nearest-rounded endpoint is within its adjacent floating-point
/// neighbours. Widen exact results too; overflow is never a finite sentinel.
fn outward(lower: f64, upper: f64) -> Result<FiniteInterval, IntervalError> {
    let lower = lower.next_down();
    let upper = upper.next_up();
    if !(lower.is_finite() && upper.is_finite()) {
        return Err(IntervalError::Range);
    }
    Ok(FiniteInterval { lower, upper })
}

#[cfg(test)]
mod tests;
