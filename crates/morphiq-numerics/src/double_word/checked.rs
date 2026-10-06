//! Checked double-word arithmetic: each operation returns its result only when
//! its operands satisfy the hypotheses of the machine-checked IEEE 754 theorem
//! for that operation, so the documented bound is proved for the call.
//!
//! The hypotheses are the theorems' own, decided exactly: magnitudes by
//! comparison with powers of two, and conditions on products in integer
//! arithmetic on the significands, never through a rounded product, which can
//! cross a boundary the exact product doesn't. The theorems and their domains
//! are in
//! [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md).
//!
//! The conditions are sufficient, not necessary. An operation outside them is
//! not shown to be inaccurate; its accuracy is just not proved, and the
//! unchecked operation still returns what the arithmetic produces.

use super::DoubleWord;
use crate::eft::{two_prod, two_sum};
use core::fmt;

/// Why a checked operation returned no result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CheckError {
    /// An operand is not a double-word number: a word is infinite or NaN, or
    /// `hi ≠ RN(hi + lo)`.
    InvalidOperand,
    /// The divisor is zero.
    DivisionByZero,
    /// The operands are valid, but a hypothesis of the operation's theorem
    /// fails, so its bound is not proved for them. Neither accuracy nor
    /// inaccuracy is claimed.
    OutsideProvenDomain(Hypothesis),
}

/// The theorem hypothesis an operation's operands failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Hypothesis {
    /// A word exceeds the operation's magnitude limit, which excludes
    /// overflow: `2^1020` for `sum`, `2^1018` for `add_f64`, `2^1016` for
    /// `add` and `sub`, `2^508` for the products; for `product`, no exponents
    /// `e_a, e_b ≤ 994` with `e_a + e_b ≤ 1020` bound the operands.
    Magnitude,
    /// A product of words is nonzero but below `2^−969` (leading words) or
    /// `2^−1022` (a leading and a trailing word).
    ProductUnderflow,
    /// No `L, H ≥ 0` with `2L + 2H ≤ 917` have every nonzero word of both
    /// operands in `[2^−L, 2^H)`.
    QuotientRange,
    /// The exact result is zero, where a relative bound says nothing, and the
    /// operation did not return zero.
    ZeroResult,
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOperand => f.write_str("an operand is not a finite double-word number"),
            Self::DivisionByZero => f.write_str("division by zero"),
            Self::OutsideProvenDomain(h) => {
                let which = match h {
                    Hypothesis::Magnitude => "a word exceeds the magnitude limit",
                    Hypothesis::ProductUnderflow => "a product of words is below the proved range",
                    Hypothesis::QuotientRange => "the words' exponents span too wide a range",
                    Hypothesis::ZeroResult => "the exact result is zero and the result is not",
                };
                write!(f, "outside the proven domain: {which}")
            }
        }
    }
}

impl core::error::Error for CheckError {}

use CheckError::{DivisionByZero, InvalidOperand, OutsideProvenDomain};
use Hypothesis::{Magnitude, ProductUnderflow, QuotientRange, ZeroResult};

/// The binary64 fraction field.
const FRACTION: u64 = (1 << 52) - 1;

/// `2^k` for `−1022 ≤ k ≤ 1023`.
const fn pow2(k: i32) -> f64 {
    #[allow(clippy::cast_sign_loss)] // k + 1023 >= 1
    f64::from_bits(((k + 1023) as u64) << 52)
}

/// `(m, e)` with `|x| = m·2^e` exactly, for finite `x`.
const fn decompose(x: f64) -> (u64, i32) {
    let bits = x.to_bits();
    #[allow(clippy::cast_possible_truncation)] // the 11-bit exponent field
    let biased = ((bits >> 52) & 0x7ff) as i32;
    if biased == 0 {
        (bits & FRACTION, -1074)
    } else {
        ((bits & FRACTION) | (1 << 52), biased - 1075)
    }
}

/// `⌊log2 |x|⌋`, exactly, for finite nonzero `x`.
const fn exponent(x: f64) -> i32 {
    let (m, e) = decompose(x);
    #[allow(clippy::cast_possible_wrap)] // at most 63
    let top = 63 - m.leading_zeros() as i32;
    e + top
}

/// The least `e` with `|x| ≤ 2^e`, for finite nonzero `x`.
const fn ceiling_exponent(x: f64) -> i32 {
    let (m, _) = decompose(x);
    if m.is_power_of_two() {
        exponent(x)
    } else {
        exponent(x) + 1
    }
}

/// `|a·b| ≥ 2^k`, decided exactly; false when either is zero.
const fn product_at_least(a: f64, b: f64, k: i32) -> bool {
    if a == 0.0 || b == 0.0 {
        return false;
    }
    let (ma, ea) = decompose(a);
    let (mb, eb) = decompose(b);
    // |a·b| = p·2^(ea + eb), with p < 2^106.
    let p = ma as u128 * mb as u128;
    let s = k - ea - eb;
    if s <= 0 {
        true
    } else if s >= 106 {
        false
    } else {
        p >= 1 << s
    }
}

/// `in_two_prod_domain`: `a·b = 0` or `|a·b| ≥ 2^−969`.
const fn in_two_prod_domain(a: f64, b: f64) -> bool {
    a == 0.0 || b == 0.0 || product_at_least(a, b, -969)
}

/// `normal_or_zero(a·b)`: `a·b = 0` or `|a·b| ≥ 2^−1022`.
const fn normal_or_zero(a: f64, b: f64) -> bool {
    a == 0.0 || b == 0.0 || product_at_least(a, b, -1022)
}

/// Every word at most `2^k` in magnitude.
fn within(words: &[f64], k: i32) -> bool {
    words.iter().all(|w| w.abs() <= pow2(k))
}

/// `two_prod_ieee`'s hypotheses: exponents `−537 ≤ e_a, e_b ≤ 994` with
/// `e_a + e_b ≤ 1020` and `|a| ≤ 2^e_a`, `|b| ≤ 2^e_b`, which exist exactly
/// when the least such exponents satisfy them; and `in_two_prod_domain`.
fn product_hypotheses(a: f64, b: f64) -> Result<(), CheckError> {
    let least = |x: f64| {
        if x == 0.0 {
            -537
        } else {
            ceiling_exponent(x).max(-537)
        }
    };
    let (ea, eb) = (least(a), least(b));
    if ea > 994 || eb > 994 || ea + eb > 1020 {
        return Err(OutsideProvenDomain(Magnitude));
    }
    if !in_two_prod_domain(a, b) {
        return Err(OutsideProvenDomain(ProductUnderflow));
    }
    Ok(())
}

/// `div_ieee`'s range hypothesis: some `L, H ≥ 0` with `2L + 2H ≤ 917` and
/// every nonzero word in `[2^−L, 2^H)`. Both conditions are monotone in `L`
/// and `H`, so the least `L` and `H` decide it.
fn quotient_range(words: &[f64]) -> Result<(), CheckError> {
    let (mut l, mut h) = (0, 0);
    for &w in words.iter().filter(|w| **w != 0.0) {
        l = l.max(-exponent(w));
        h = h.max(exponent(w) + 1);
    }
    if 2 * l + 2 * h <= 917 {
        Ok(())
    } else {
        Err(OutsideProvenDomain(QuotientRange))
    }
}

/// A finite double-word number: both words finite and `hi = RN(hi + lo)`.
fn valid(x: DoubleWord) -> Result<(), CheckError> {
    if x.hi.is_finite() && x.lo.is_finite() && x.hi + x.lo == x.hi {
        Ok(())
    } else {
        Err(InvalidOperand)
    }
}

fn valid_f64(y: f64) -> Result<(), CheckError> {
    if y.is_finite() {
        Ok(())
    } else {
        Err(InvalidOperand)
    }
}

/// The result, or, when the exact result is zero, the result only if it is
/// zero: the relative bounds say nothing there, so zero is checked directly.
fn admit(z: DoubleWord, exact_zero: bool) -> Result<DoubleWord, CheckError> {
    if exact_zero && (z.hi != 0.0 || z.lo != 0.0) {
        Err(OutsideProvenDomain(ZeroResult))
    } else {
        Ok(z)
    }
}

impl DoubleWord {
    /// [`sum`](Self::sum) when `|a|, |b| ≤ 2^1020`: then the result is the
    /// exact sum (`two_sum_ieee`).
    ///
    /// # Errors
    ///
    /// [`CheckError::InvalidOperand`] for a non-finite operand,
    /// [`Hypothesis::Magnitude`] beyond `2^1020`.
    pub fn checked_sum(a: f64, b: f64) -> Result<Self, CheckError> {
        valid_f64(a)?;
        valid_f64(b)?;
        if !within(&[a, b], 1020) {
            return Err(OutsideProvenDomain(Magnitude));
        }
        let (hi, lo) = two_sum(a, b);
        Ok(Self { hi, lo })
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
        valid_f64(a)?;
        valid_f64(b)?;
        product_hypotheses(a, b)?;
        let (hi, lo) = two_prod(a, b);
        Ok(Self { hi, lo })
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
        valid(self)?;
        valid_f64(y)?;
        if !within(&[self.hi, self.lo, y], 1018) {
            return Err(OutsideProvenDomain(Magnitude));
        }
        // hi + lo is a binary64 number only when lo = 0.
        admit(self.add_f64(y), self.lo == 0.0 && self.hi == -y)
    }

    /// [`add`](Self::add) when every word is at most `2^1016`: then the result
    /// is finite and within `3u²/(1 − 4u)` of the exact sum (`add_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_add_f64`](Self::checked_add_f64).
    pub fn checked_add(self, other: Self) -> Result<Self, CheckError> {
        valid(self)?;
        valid(other)?;
        if !within(&[self.hi, self.lo, other.hi, other.lo], 1016) {
            return Err(OutsideProvenDomain(Magnitude));
        }
        // A value has one double-word representation (hi = RN(value)), so
        // the sum is zero exactly when other = −self, word for word.
        admit(
            self.add(other),
            self.hi == -other.hi && self.lo == -other.lo,
        )
    }

    /// [`sub`](Self::sub) when every word is at most `2^1016`: then the result
    /// is finite and within `3u²/(1 − 4u)` of the exact difference
    /// (`sub_ieee`).
    ///
    /// # Errors
    ///
    /// As [`checked_add_f64`](Self::checked_add_f64).
    pub fn checked_sub(self, other: Self) -> Result<Self, CheckError> {
        self.checked_add(other.neg())
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
        valid(self)?;
        valid_f64(y)?;
        if !within(&[self.hi, self.lo, y], 508) {
            return Err(OutsideProvenDomain(Magnitude));
        }
        if !in_two_prod_domain(self.hi, y) || !normal_or_zero(self.lo, y) {
            return Err(OutsideProvenDomain(ProductUnderflow));
        }
        // hi = 0 forces lo = 0, so the product is zero exactly then.
        admit(self.mul_f64(y), self.hi == 0.0 || y == 0.0)
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
        valid(self)?;
        valid(other)?;
        if !within(&[self.hi, self.lo, other.hi, other.lo], 508) {
            return Err(OutsideProvenDomain(Magnitude));
        }
        if !in_two_prod_domain(self.hi, other.hi)
            || !normal_or_zero(self.hi, other.lo)
            || !normal_or_zero(self.lo, other.hi)
        {
            return Err(OutsideProvenDomain(ProductUnderflow));
        }
        admit(self.mul(other), self.hi == 0.0 || other.hi == 0.0)
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
        valid(self)?;
        valid_f64(y)?;
        if y == 0.0 {
            return Err(DivisionByZero);
        }
        quotient_range(&[self.hi, self.lo, y])?;
        admit(self.div_f64(y), self.hi == 0.0)
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
        valid(self)?;
        valid(other)?;
        // A double-word number is zero exactly when its leading word is.
        if other.hi == 0.0 {
            return Err(DivisionByZero);
        }
        quotient_range(&[self.hi, self.lo, other.hi, other.lo])?;
        admit(self.div(other), self.hi == 0.0)
    }
}
