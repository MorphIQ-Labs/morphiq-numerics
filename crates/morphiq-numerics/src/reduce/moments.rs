//! Checked, compensated moments about a retained sample anchor.

use crate::double_word::{CheckError, DoubleWord};
use crate::elementary::sqrt;
use crate::interval::FiniteInterval;

/// A finite estimate with a conservative absolute error bound.
///
/// The exact statistic of the admitted binary64 samples is within
/// `absolute_error()` of `value()`. The bound accounts for arithmetic rounding,
/// not sampling uncertainty. See `docs/moments.md` for the contract.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MomentEstimate {
    value: f64,
    absolute_error: f64,
}

impl MomentEstimate {
    /// Estimated statistic, with a canonical positive zero.
    #[must_use]
    pub const fn value(self) -> f64 {
        self.value
    }

    /// Finite, nonnegative bound on absolute arithmetic error.
    #[must_use]
    pub const fn absolute_error(self) -> f64 {
        self.absolute_error
    }

    fn nonnegative(mut self) -> Self {
        // Projection cannot increase distance to a nonnegative exact statistic.
        if self.value < 0.0 {
            self.value = 0.0;
        }
        self
    }
}

/// A moment operation cannot establish its result under the stated contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MomentsError {
    /// The sample is a NaN or infinity.
    NonFiniteSample,
    /// The exact sample count would exceed `2^53`.
    CountOverflow,
    /// A mean was requested without any samples.
    Empty,
    /// Variance or standard error requires at least two samples.
    InsufficientSamples,
    /// An arithmetic operand is outside a checked double-word theorem's domain.
    Arithmetic(CheckError),
    /// A finite error bound or finite square-root enclosure is unavailable.
    Range,
}

impl From<CheckError> for MomentsError {
    fn from(error: CheckError) -> Self {
        Self::Arithmetic(error)
    }
}

/// Allocation-free, mergeable compensated mean and variance statistics.
///
/// Keeps the exact count, a sample anchor, and double-word sums of deviations
/// and squared deviations, each with an absolute error bound. Results are
/// reproducible for fixed samples, batch boundaries, and merge order, across
/// targets and thread counts. Changing the partition or merge order can change
/// rounding. This type performs no parallel scheduling.
///
/// Counts through `2^53` are exact. Nonfinite samples and arithmetic outside
/// the checked double-word domains are refused. Successful readouts return a
/// finite value and absolute arithmetic error bound; no uniform relative-error
/// or correct-rounding guarantee is implied. See `docs/moments.md`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Moments2 {
    count: u64,
    anchor: f64,
    sum: Bounded,
    squares: Bounded,
}

impl Default for Moments2 {
    fn default() -> Self {
        Self::new()
    }
}

impl Moments2 {
    /// Construct an empty accumulator without allocation.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            count: 0,
            anchor: 0.0,
            sum: Bounded::point(0.0),
            squares: Bounded::point(0.0),
        }
    }

    /// Exact number of admitted samples.
    #[must_use]
    pub const fn count(&self) -> u64 {
        self.count
    }

    /// Admit one exact binary64 sample. Failure leaves all state unchanged.
    ///
    /// # Errors
    /// [`MomentsError::NonFiniteSample`], [`MomentsError::CountOverflow`],
    /// [`MomentsError::Arithmetic`], or [`MomentsError::Range`].
    pub fn push(&mut self, sample: f64) -> Result<(), MomentsError> {
        if !sample.is_finite() {
            return Err(MomentsError::NonFiniteSample);
        }
        let count = next_count(self.count, 1)?;
        if self.count == 0 {
            self.anchor = sample;
            self.count = count;
            return Ok(());
        }
        let deviation = Bounded::difference(sample, self.anchor)?;
        let sum = self.sum.add(deviation)?;
        let squares = self.squares.add(deviation.mul(deviation)?)?;
        self.sum = sum;
        self.squares = squares;
        self.count = count;
        Ok(())
    }

    /// Append another accumulator's samples in this merge operation.
    ///
    /// An empty accumulator is an identity. The right operand is unchanged,
    /// and a failure leaves the receiver unchanged. Order and partition are
    /// part of the numerical contract; this operation is not bitwise associative.
    ///
    /// # Errors
    /// [`MomentsError::CountOverflow`], [`MomentsError::Arithmetic`], or
    /// [`MomentsError::Range`].
    pub fn merge(&mut self, other: &Self) -> Result<(), MomentsError> {
        let count = next_count(self.count, other.count)?;
        if other.count == 0 {
            return Ok(());
        }
        if self.count == 0 {
            *self = *other;
            return Ok(());
        }
        let shift = Bounded::difference(other.anchor, self.anchor)?;
        let n = Bounded::point(other.count as f64);
        let translated_sum = other.sum.add(shift.mul(n)?)?;
        let translated_squares = other
            .squares
            .add(shift.mul(other.sum)?.mul(Bounded::point(2.0))?)?
            .add(shift.mul(shift)?.mul(n)?)?;
        let sum = self.sum.add(translated_sum)?;
        let squares = self.squares.add(translated_squares)?;
        self.sum = sum;
        self.squares = squares;
        self.count = count;
        Ok(())
    }

    /// Arithmetic mean of the admitted samples, with an absolute error bound.
    ///
    /// # Errors
    /// [`MomentsError::Empty`], [`MomentsError::Arithmetic`], or
    /// [`MomentsError::Range`].
    pub fn mean(&self) -> Result<MomentEstimate, MomentsError> {
        if self.count == 0 {
            return Err(MomentsError::Empty);
        }
        self.sum
            .div(self.count as f64)?
            .add(Bounded::point(self.anchor))?
            .estimate()
    }

    /// Unbiased sample variance `sum((x-mean)^2)/(n-1)` and its error bound.
    ///
    /// # Errors
    /// [`MomentsError::InsufficientSamples`], [`MomentsError::Arithmetic`],
    /// or [`MomentsError::Range`].
    pub fn variance(&self) -> Result<MomentEstimate, MomentsError> {
        Ok(self.variance_words()?.estimate()?.nonnegative())
    }

    /// Estimated standard error of the mean, `sqrt(variance/n)`.
    ///
    /// Its absolute error bounds arithmetic error in that statistic, not the
    /// sampling error itself. Interpretation assumes the caller's observations
    /// are an appropriate independent sample (for antithetic Monte Carlo, pair
    /// means are the observations).
    ///
    /// # Errors
    /// [`MomentsError::InsufficientSamples`], [`MomentsError::Arithmetic`],
    /// or [`MomentsError::Range`].
    pub fn standard_error(&self) -> Result<MomentEstimate, MomentsError> {
        let squared = self
            .variance_words()?
            .div(self.count as f64)?
            .estimate()?
            .nonnegative();
        if squared.value == 0.0 && squared.absolute_error == 0.0 {
            return Ok(squared);
        }
        let lower = if squared.value <= squared.absolute_error {
            0.0
        } else {
            (squared.value - squared.absolute_error).next_down()
        };
        let upper = upper_sum(squared.value, squared.absolute_error)?;
        let enclosure = FiniteInterval::new(lower, upper)
            .and_then(FiniteInterval::checked_sqrt)
            .map_err(|_| MomentsError::Range)?;
        let value = sqrt(squared.value);
        let absolute_error = finite_up((value - enclosure.lower()).max(enclosure.upper() - value))?;
        Ok(MomentEstimate {
            value,
            absolute_error,
        })
    }

    fn variance_words(&self) -> Result<Bounded, MomentsError> {
        if self.count < 2 {
            return Err(MomentsError::InsufficientSamples);
        }
        self.squares
            .sub(self.sum.mul(self.sum.div(self.count as f64)?)?)?
            .div((self.count - 1) as f64)
    }
}

fn next_count(a: u64, b: u64) -> Result<u64, MomentsError> {
    a.checked_add(b)
        .filter(|&n| n <= (1_u64 << 53))
        .ok_or(MomentsError::CountOverflow)
}

// A double-word centre and a finite nonnegative absolute radius. This private
// helper propagates only the operations required by the moment recurrence.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Bounded {
    value: DoubleWord,
    error: f64,
}

impl Bounded {
    const fn point(value: f64) -> Self {
        Self {
            value: DoubleWord::from_f64(value),
            error: 0.0,
        }
    }

    fn exact_zero(self) -> bool {
        self.value.hi() == 0.0 && self.error == 0.0
    }

    fn difference(a: f64, b: f64) -> Result<Self, MomentsError> {
        if a == b {
            return Ok(Self::point(0.0));
        }
        Ok(Self {
            value: DoubleWord::checked_sum(a, -b)?,
            error: 0.0,
        })
    }

    fn magnitude(self) -> Result<f64, MomentsError> {
        upper_sum(self.value.hi().abs(), self.value.lo().abs())
    }

    fn add(self, other: Self) -> Result<Self, MomentsError> {
        if self.exact_zero() {
            return Ok(other);
        }
        if other.exact_zero() {
            return Ok(self);
        }
        let value = self.value.checked_add(other.value)?;
        Ok(Self {
            value,
            error: upper_sum(
                upper_sum(self.error, other.error)?,
                local_error(value, 2.0)?,
            )?,
        })
    }

    fn sub(self, other: Self) -> Result<Self, MomentsError> {
        self.add(Self {
            value: other.value.neg(),
            error: other.error,
        })
    }

    fn mul(self, other: Self) -> Result<Self, MomentsError> {
        if self.exact_zero() || other.exact_zero() {
            return Ok(Self::point(0.0));
        }
        let value = self.value.checked_mul(other.value)?;
        let propagated = upper_sum(
            upper_sum(
                upper_product(self.magnitude()?, other.error)?,
                upper_product(other.magnitude()?, self.error)?,
            )?,
            upper_product(self.error, other.error)?,
        )?;
        Ok(Self {
            value,
            error: upper_sum(propagated, local_error(value, 2.5)?)?,
        })
    }

    fn div(self, count: f64) -> Result<Self, MomentsError> {
        if self.exact_zero() {
            return Ok(self);
        }
        let value = self.value.checked_div_f64(count)?;
        let propagated = if self.error == 0.0 {
            0.0
        } else {
            finite_up(self.error / count)?
        };
        Ok(Self {
            value,
            error: upper_sum(propagated, local_error(value, 1.5)?)?,
        })
    }

    fn estimate(self) -> Result<MomentEstimate, MomentsError> {
        Ok(MomentEstimate {
            value: if self.value.hi() == 0.0 {
                0.0
            } else {
                self.value.hi()
            },
            absolute_error: upper_sum(self.error, self.value.lo().abs())?,
        })
    }
}

// If |rounded-exact| <= e|exact| and e <= 1/2, the local error is at most
// 2e|rounded|. The checked DW bounds are <4u² (add), <=5u² (mul), and
// <=3u² (div_f64). EPSILON=2u, hence these exact factors 2, 2.5, and 1.5.
fn local_error(value: DoubleWord, factor: f64) -> Result<f64, MomentsError> {
    upper_product(
        factor * f64::EPSILON * f64::EPSILON,
        upper_sum(value.hi().abs(), value.lo().abs())?,
    )
}

fn upper_sum(a: f64, b: f64) -> Result<f64, MomentsError> {
    if a == 0.0 {
        return Ok(b);
    }
    if b == 0.0 {
        return Ok(a);
    }
    finite_up(a + b)
}

fn upper_product(a: f64, b: f64) -> Result<f64, MomentsError> {
    if a == 0.0 || b == 0.0 {
        return Ok(0.0);
    }
    finite_up(a * b)
}

fn finite_up(value: f64) -> Result<f64, MomentsError> {
    let result = value.next_up();
    if result.is_finite() {
        Ok(result)
    } else {
        Err(MomentsError::Range)
    }
}

#[cfg(test)]
mod performance;
