//! Double-word numbers: an unevaluated sum `hi + lo` of two binary64 numbers
//! with `hi = RN(hi + lo)`, and their arithmetic.
//!
//! Each operation is the FMA-free algorithm of Joldes, Muller and Popescu
//! (2017), operation for operation, and carries the relative error bound
//! Muller and Rideau (2022) proved for it in Coq. Here `u = 2^-53`. The
//! sources, the bounds and the domain on which they hold are in
//! [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md).
//!
//! # Domain
//!
//! Each bound is for a nonzero exact result.
//!
//! - [`add_f64`](DoubleWord::add_f64), [`add`](DoubleWord::add) and
//!   [`sub`](DoubleWord::sub) keep their bounds for every input whose words
//!   are at most `2^1018` (`add_f64`) or `2^1016` (`add`, `sub`) in magnitude.
//!   Subnormal words and results are covered, and the limit excludes overflow.
//! - [`mul_f64`](DoubleWord::mul_f64) and [`mul`](DoubleWord::mul) are proved
//!   in binary64 when the leading words' product is zero or at least
//!   `2^-969` (within [`two_prod`](crate::eft::two_prod)'s domain), and every product of a leading
//!   and a trailing word is zero or at least `2^-1022`. Every nonzero word
//!   between `2^-484` and `2^484` in magnitude meets this; overflow is excluded
//!   for every word at most `2^508`.
//! - [`div_f64`](DoubleWord::div_f64) and [`div`](DoubleWord::div) are proved
//!   in binary64 when, for some `L, H ≥ 0` with `2L + 2H ≤ 917`, every nonzero
//!   word `w` of both operands has `2^-L ≤ |w| < 2^H`: for example, every
//!   nonzero word between `2^-229` and `2^229` in magnitude. That also excludes
//!   overflow.
//!
//! Each statement is a theorem about the algorithm in IEEE 754 binary64
//! arithmetic (`formal/binary64/IEEE64*.v`).
//!
//! # Checked operations
//!
//! Each operation, and the exact constructors [`sum`](DoubleWord::sum) and
//! [`product`](DoubleWord::product), has a `checked_` form that returns its
//! result only when the operands meet that theorem's hypotheses, decided
//! exactly, and says which failed otherwise ([`CheckError`]).
//!
//! # Non-finite results
//!
//! A NaN word of an unchecked result is the first NaN among the operands' words,
//! in argument order and high before low, unchanged; with no NaN operand it is
//! the canonical quiet NaN `7ff8000000000000`. Checked results are finite.

use crate::eft::defined_pair;

mod checked;
mod exp;
mod exp_tables;
pub(crate) mod kernel;
pub use checked::{CheckError, Hypothesis};

use kernel::DoubleWord as Kernel;

/// An unevaluated sum `hi + lo` of two binary64 numbers with
/// `hi = RN(hi + lo)`.
#[derive(Clone, Copy, PartialEq)]
pub struct DoubleWord(Kernel);

impl core::fmt::Debug for DoubleWord {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl DoubleWord {
    /// A kernel result with each NaN word's bits taken from the contract.
    #[inline(always)]
    const fn defined(z: Kernel, inputs: &[f64]) -> Self {
        // One test for both words; a NaN takes the rarely executed path.
        let (hi, lo) = (z.hi(), z.lo());
        if hi.is_nan() | lo.is_nan() {
            let (hi, lo) = defined_pair(hi, lo, inputs);
            return Self(Kernel::from_words(hi, lo));
        }
        Self(z)
    }

    /// `x` as a double-word number, `x + 0`.
    #[must_use]
    #[inline]
    pub const fn from_f64(x: f64) -> Self {
        Self(Kernel::from_f64(x))
    }

    /// The exact sum `a + b`, by [`two_sum`](crate::eft::two_sum).
    #[must_use]
    #[inline]
    pub const fn sum(a: f64, b: f64) -> Self {
        Self::defined(Kernel::sum(a, b), &[a, b])
    }

    /// The exact product `a · b`, by [`two_prod`](crate::eft::two_prod), within its domain.
    #[must_use]
    #[inline]
    pub const fn product(a: f64, b: f64) -> Self {
        Self::defined(Kernel::product(a, b), &[a, b])
    }

    /// `hi + lo` as a double-word number, or `None` unless `hi = RN(hi + lo)`.
    #[must_use]
    #[inline]
    pub fn from_parts(hi: f64, lo: f64) -> Option<Self> {
        Kernel::from_parts(hi, lo).map(Self)
    }

    /// The leading word, `RN(hi + lo)`: the value rounded to binary64.
    #[must_use]
    #[inline]
    pub const fn hi(self) -> f64 {
        self.0.hi()
    }

    /// The trailing word, `hi + lo - RN(hi + lo)`.
    #[must_use]
    #[inline]
    pub const fn lo(self) -> f64 {
        self.0.lo()
    }

    /// `-(hi + lo)`, exactly.
    #[must_use]
    #[inline]
    pub const fn neg(self) -> Self {
        Self(self.0.neg())
    }

    /// `(hi + lo) + y`, with relative error at most `2u²`.
    ///
    /// DWPlusFP: Joldes et al. 2017, Algorithm 4; bound proved in Muller and
    /// Rideau 2022, Table 1.
    #[must_use]
    #[inline]
    pub const fn add_f64(self, y: f64) -> Self {
        Self::defined(self.0.add_f64(y), &[self.hi(), self.lo(), y])
    }

    /// `(hi + lo) · y`, with relative error at most `1.5u² + 4u³`.
    ///
    /// DWTimesFP1: Joldes et al. 2017, Algorithm 7; bound proved in Muller
    /// and Rideau 2022, Table 1.
    #[must_use]
    #[inline]
    pub const fn mul_f64(self, y: f64) -> Self {
        Self::defined(self.0.mul_f64(y), &[self.hi(), self.lo(), y])
    }

    /// `(hi + lo) / y`, with relative error at most `3u²`, for `y ≠ 0`.
    ///
    /// DWDivFP3: Joldes et al. 2017, Algorithm 15; bound proved there
    /// (Theorem 6.2) and in Muller and Rideau 2022, Table 1. Lines 3 and 4 are
    /// exact by the paper's Property 6.1 and the Sterbenz lemma.
    #[must_use]
    #[inline]
    pub const fn div_f64(self, y: f64) -> Self {
        Self::defined(self.0.div_f64(y), &[self.hi(), self.lo(), y])
    }

    /// `(x_hi + x_lo) + (y_hi + y_lo)`, with relative error at most
    /// `3u² + 13u³`.
    ///
    /// AccurateDWPlusDW: Joldes et al. 2017, Algorithm 6; bound proved in
    /// Muller and Rideau 2022, Table 1, and shown asymptotically optimal
    /// there (Property 2.1).
    #[must_use]
    #[inline]
    pub const fn add(self, other: Self) -> Self {
        Self::defined(
            self.0.add(other.0),
            &[self.hi(), self.lo(), other.hi(), other.lo()],
        )
    }

    /// `(x_hi + x_lo) - (y_hi + y_lo)`: [`add`](Self::add) of the exact
    /// negation, with the same bound.
    #[must_use]
    #[inline]
    pub const fn sub(self, other: Self) -> Self {
        Self::defined(
            self.0.sub(other.0),
            &[self.hi(), self.lo(), other.hi(), other.lo()],
        )
    }

    /// `(x_hi + x_lo) · (y_hi + y_lo)`, with relative error at most
    /// `5u² / (1 + u)² < 5u²`.
    ///
    /// DWTimesDW1: Joldes et al. 2017, Algorithm 10. Muller and Rideau 2022,
    /// Theorem 2.6, proves this bound under round-to-nearest ties-to-even,
    /// which binary64 arithmetic uses, improving the 7u² of the 2017 paper.
    #[must_use]
    #[inline]
    pub const fn mul(self, other: Self) -> Self {
        Self::defined(
            self.0.mul(other.0),
            &[self.hi(), self.lo(), other.hi(), other.lo()],
        )
    }

    /// `(x_hi + x_lo) / (y_hi + y_lo)`, with relative error at most
    /// `15u² + 56u³`, for a nonzero divisor.
    ///
    /// DWDivDW2: Joldes et al. 2017, Algorithm 17, which returns exactly what
    /// their Algorithm 16 does with fewer operations; bound proved there
    /// (Theorem 7.1) and in Muller and Rideau 2022, Table 1. Line 3 is exact
    /// by the Sterbenz lemma.
    #[must_use]
    #[inline]
    pub const fn div(self, other: Self) -> Self {
        Self::defined(
            self.0.div(other.0),
            &[self.hi(), self.lo(), other.hi(), other.lo()],
        )
    }

    /// `exp(self)` as `(value, n)` with `exp(self) ≈ value · 2^n`, or `None`
    /// when `|self.hi()| >= 1455` or `self` is not finite.
    ///
    /// `value` is a double-word number in `[0.9996, 2.0008)`, with relative
    /// error as stated in [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md#exponential);
    /// `n` is in `[-2100, 2099]`. The scale is left to the caller, so
    /// `value · 2^n` may lie outside binary64's range: a caller multiplying it
    /// into a quantity of opposite scale keeps the product finite.
    ///
    /// Every exact product inside comes from a hardware fused multiply-add
    /// where the build or the processor has one, and from Dekker's product
    /// elsewhere; the result is the same on every target.
    #[must_use]
    #[inline]
    pub fn exp_split(self) -> Option<(Self, i32)> {
        let inputs = [self.hi(), self.lo()];
        self.0
            .exp_split()
            .map(|(value, n)| (Self::defined(value, &inputs), n))
    }

    /// [`sum`](Self::sum) when `|a|, |b| ≤ 2^1020`: then the result is the
    /// exact sum (`two_sum_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`] for a non-finite operand,
    /// [`Hypothesis::Magnitude`] beyond `2^1020`.
    pub fn checked_sum(a: f64, b: f64) -> Result<Self, CheckError> {
        Kernel::checked_sum(a, b).map(Self)
    }

    /// [`product`](Self::product) when `two_prod`'s domain holds: then the
    /// result is the exact product (`two_prod_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`] for a non-finite operand,
    /// [`Hypothesis::Magnitude`] or [`Hypothesis::ProductUnderflow`] outside
    /// the domain.
    pub fn checked_product(a: f64, b: f64) -> Result<Self, CheckError> {
        Kernel::checked_product(a, b).map(Self)
    }

    /// [`add_f64`](Self::add_f64) when every word is at most `2^1018`: then
    /// the result is finite and within `2u²` of the exact sum
    /// (`add_f64_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`], or [`CheckError::OutsideProvenDomain`]
    /// with [`Hypothesis::Magnitude`] or [`Hypothesis::ZeroResult`].
    pub fn checked_add_f64(self, y: f64) -> Result<Self, CheckError> {
        self.0.checked_add_f64(y).map(Self)
    }

    /// [`mul_f64`](Self::mul_f64) when every word is at most `2^508`,
    /// `x_hi·y` is in `two_prod`'s domain and `x_lo·y` is zero or at least
    /// `2^−1022`: then the result is finite and within `1.5u² + 4u³` of the
    /// exact product (`mul_f64_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`], or [`CheckError::OutsideProvenDomain`]
    /// with [`Hypothesis::Magnitude`], [`Hypothesis::ProductUnderflow`] or
    /// [`Hypothesis::ZeroResult`].
    pub fn checked_mul_f64(self, y: f64) -> Result<Self, CheckError> {
        self.0.checked_mul_f64(y).map(Self)
    }

    /// [`div_f64`](Self::div_f64) when `y ≠ 0` and some `L, H ≥ 0` with
    /// `2L + 2H ≤ 917` have every nonzero word in `[2^−L, 2^H)`: then the
    /// result is finite and within `3u²` of the exact quotient
    /// (`div_f64_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`], [`CheckError::DivisionByZero`], or
    /// [`CheckError::OutsideProvenDomain`] with [`Hypothesis::QuotientRange`]
    /// or [`Hypothesis::ZeroResult`].
    pub fn checked_div_f64(self, y: f64) -> Result<Self, CheckError> {
        self.0.checked_div_f64(y).map(Self)
    }

    /// [`add`](Self::add) when every word is at most `2^1016`: then the result
    /// is finite and within `3u²/(1 − 4u)` of the exact sum (`add_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_add_f64`](Self::checked_add_f64).
    pub fn checked_add(self, other: Self) -> Result<Self, CheckError> {
        self.0.checked_add(other.0).map(Self)
    }

    /// [`sub`](Self::sub) when every word is at most `2^1016`: then the result
    /// is finite and within `3u²/(1 − 4u)` of the exact difference
    /// (`sub_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_add_f64`](Self::checked_add_f64).
    pub fn checked_sub(self, other: Self) -> Result<Self, CheckError> {
        self.0.checked_sub(other.0).map(Self)
    }

    /// [`mul`](Self::mul) when every word is at most `2^508`, `x_hi·y_hi` is in
    /// `two_prod`'s domain and `x_hi·y_lo` and `x_lo·y_hi` are each zero or at
    /// least `2^−1022`: then the result is finite and within `5u²` of the exact
    /// product (`mul_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_mul_f64`](Self::checked_mul_f64).
    pub fn checked_mul(self, other: Self) -> Result<Self, CheckError> {
        self.0.checked_mul(other.0).map(Self)
    }

    /// [`div`](Self::div) when the divisor is nonzero and some `L, H ≥ 0` with
    /// `2L + 2H ≤ 917` have every nonzero word of both operands in
    /// `[2^−L, 2^H)`: then the result is finite and within `15u² + 56u³` of the
    /// exact quotient (`div_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_div_f64`](Self::checked_div_f64).
    pub fn checked_div(self, other: Self) -> Result<Self, CheckError> {
        self.0.checked_div(other.0).map(Self)
    }
}
