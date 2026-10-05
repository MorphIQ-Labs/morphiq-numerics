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
//! The bounds are proved for an unbounded exponent range. They hold in
//! binary64 whenever every operation of the algorithm returns what it would
//! there: when no intermediate overflows, no rounded intermediate is
//! subnormal, and each exact product is within [`two_prod`]'s domain.

use crate::eft::{fast_two_sum, two_prod, two_sum};

/// An unevaluated sum `hi + lo` of two binary64 numbers with
/// `hi = RN(hi + lo)`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct DoubleWord {
    hi: f64,
    lo: f64,
}

impl DoubleWord {
    /// `x` as a double-word number, `x + 0`.
    #[must_use]
    #[inline]
    pub const fn from_f64(x: f64) -> Self {
        Self { hi: x, lo: 0.0 }
    }

    /// The exact sum `a + b`, by [`two_sum`].
    #[must_use]
    #[inline]
    pub const fn sum(a: f64, b: f64) -> Self {
        let (hi, lo) = two_sum(a, b);
        Self { hi, lo }
    }

    /// The exact product `a · b`, by [`two_prod`], within its domain.
    #[must_use]
    #[inline]
    pub const fn product(a: f64, b: f64) -> Self {
        let (hi, lo) = two_prod(a, b);
        Self { hi, lo }
    }

    /// `hi + lo` as a double-word number, or `None` unless `hi = RN(hi + lo)`.
    #[must_use]
    #[inline]
    pub fn from_parts(hi: f64, lo: f64) -> Option<Self> {
        (hi + lo == hi && hi.is_finite() && lo.is_finite()).then_some(Self { hi, lo })
    }

    /// The leading word, `RN(hi + lo)`: the value rounded to binary64.
    #[must_use]
    #[inline]
    pub const fn hi(self) -> f64 {
        self.hi
    }

    /// The trailing word, `hi + lo - RN(hi + lo)`.
    #[must_use]
    #[inline]
    pub const fn lo(self) -> f64 {
        self.lo
    }

    /// `-(hi + lo)`, exactly.
    #[must_use]
    #[inline]
    pub const fn neg(self) -> Self {
        Self {
            hi: -self.hi,
            lo: -self.lo,
        }
    }

    /// `(hi + lo) + y`, with relative error at most `2u²`.
    ///
    /// DWPlusFP: Joldes et al. 2017, Algorithm 4; bound proved in Muller and
    /// Rideau 2022, Table 1.
    #[must_use]
    #[inline]
    pub const fn add_f64(self, y: f64) -> Self {
        let (s_hi, s_lo) = two_sum(self.hi, y);
        let v = self.lo + s_lo;
        let (hi, lo) = fast_two_sum(s_hi, v);
        Self { hi, lo }
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
        let (s_hi, s_lo) = two_sum(self.hi, other.hi);
        let (t_hi, t_lo) = two_sum(self.lo, other.lo);
        let c = s_lo + t_hi;
        let (v_hi, v_lo) = fast_two_sum(s_hi, c);
        let w = t_lo + v_lo;
        let (hi, lo) = fast_two_sum(v_hi, w);
        Self { hi, lo }
    }

    /// `(x_hi + x_lo) - (y_hi + y_lo)`: [`add`](Self::add) of the exact
    /// negation, with the same bound.
    #[must_use]
    #[inline]
    pub const fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }

    /// `(hi + lo) · y`, with relative error at most `1.5u² + 4u³`.
    ///
    /// DWTimesFP1: Joldes et al. 2017, Algorithm 7; bound proved in Muller
    /// and Rideau 2022, Table 1.
    #[must_use]
    #[inline]
    pub const fn mul_f64(self, y: f64) -> Self {
        let (c_hi, c_lo1) = two_prod(self.hi, y);
        let c_lo2 = self.lo * y;
        let (t_hi, t_lo1) = fast_two_sum(c_hi, c_lo2);
        let t_lo2 = t_lo1 + c_lo1;
        let (hi, lo) = fast_two_sum(t_hi, t_lo2);
        Self { hi, lo }
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
        let (c_hi, c_lo1) = two_prod(self.hi, other.hi);
        let t_lo1 = self.hi * other.lo;
        let t_lo2 = self.lo * other.hi;
        let c_lo2 = t_lo1 + t_lo2;
        let c_lo3 = c_lo1 + c_lo2;
        let (hi, lo) = fast_two_sum(c_hi, c_lo3);
        Self { hi, lo }
    }

    /// `(hi + lo) / y`, with relative error at most `3u²`, for `y ≠ 0`.
    ///
    /// DWDivFP3: Joldes et al. 2017, Algorithm 15; bound proved there
    /// (Theorem 6.2) and in Muller and Rideau 2022, Table 1. Lines 3 and 4 are
    /// exact by the paper's Property 6.1 and the Sterbenz lemma.
    #[must_use]
    #[inline]
    pub const fn div_f64(self, y: f64) -> Self {
        let t_hi = self.hi / y;
        let (pi_hi, pi_lo) = two_prod(t_hi, y);
        let delta_hi = self.hi - pi_hi;
        let delta_t = delta_hi - pi_lo;
        let delta = delta_t + self.lo;
        let t_lo = delta / y;
        let (hi, lo) = fast_two_sum(t_hi, t_lo);
        Self { hi, lo }
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
        let t_hi = self.hi / other.hi;
        let r = other.mul_f64(t_hi);
        let pi_hi = self.hi - r.hi;
        let delta_lo = self.lo - r.lo;
        let delta = pi_hi + delta_lo;
        let t_lo = delta / other.hi;
        let (hi, lo) = fast_two_sum(t_hi, t_lo);
        Self { hi, lo }
    }
}
