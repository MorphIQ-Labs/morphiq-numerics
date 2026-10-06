//! Exact rationals `mantissa · 2^exponent` for the unit tests, sharing no
//! arithmetic with the library: big-integer arithmetic decides every
//! comparison exactly.

use crate::q128::Q128;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_traits::Signed;

/// `mantissa · 2^exponent`, exactly.
#[derive(Clone, Debug)]
pub(crate) struct Exact {
    pub(crate) mantissa: BigInt,
    pub(crate) exponent: i64,
}

impl Exact {
    pub(crate) fn of(q: Q128) -> Self {
        let (negative, m, e) = q.parts();
        let magnitude = BigInt::from(m);
        Self {
            mantissa: if negative { -magnitude } else { magnitude },
            exponent: i64::from(e),
        }
    }

    /// A positive reference value from a fixture: `m` in hexadecimal, `2^e`.
    pub(crate) fn of_hex(m: &str, e: i64) -> Self {
        Self {
            mantissa: BigInt::parse_bytes(m.as_bytes(), 16).unwrap(),
            exponent: e,
        }
    }

    /// `|self − reference| ≤ 2^−bound_log2 · |reference|`, decided exactly,
    /// with the bound given as `numerator / 2^shift`.
    pub(crate) fn within(&self, reference: &Self, numerator: u64, shift: i64) -> bool {
        let error = self.sub(reference).abs();
        let bound = reference.abs().mul(&Self {
            mantissa: BigInt::from(numerator),
            exponent: -shift,
        });
        error.cmp(&bound) != Ordering::Greater
    }

    pub(crate) fn of_f64(x: f64) -> Self {
        let bits = x.to_bits();
        let biased = i64::try_from((bits >> 52) & 0x7ff).unwrap();
        let fraction = bits & ((1 << 52) - 1);
        let (significand, exponent) = if biased == 0 {
            (fraction, -1074)
        } else {
            (fraction | (1 << 52), biased - 1075)
        };
        let magnitude = BigInt::from(significand);
        Self {
            mantissa: if bits >> 63 == 1 {
                -magnitude
            } else {
                magnitude
            },
            exponent,
        }
    }

    pub(crate) fn pow2(k: i64) -> Self {
        Self {
            mantissa: BigInt::from(1),
            exponent: k,
        }
    }

    /// Both mantissas on the finer grid.
    pub(crate) fn aligned(&self, other: &Self) -> (BigInt, BigInt) {
        let e = self.exponent.min(other.exponent);
        let shift = |x: &Self| &x.mantissa << usize::try_from(x.exponent - e).unwrap();
        (shift(self), shift(other))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let (a, b) = self.aligned(other);
        Self {
            mantissa: a + b,
            exponent: self.exponent.min(other.exponent),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            mantissa: -&self.mantissa,
            exponent: self.exponent,
        }
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        Self {
            mantissa: &self.mantissa * &other.mantissa,
            exponent: self.exponent + other.exponent,
        }
    }

    pub(crate) fn abs(&self) -> Self {
        Self {
            mantissa: self.mantissa.abs(),
            exponent: self.exponent,
        }
    }

    pub(crate) fn cmp(&self, other: &Self) -> Ordering {
        let (a, b) = self.aligned(other);
        a.cmp(&b)
    }
}
