//! Test oracles for `morphiq-numerics`. Never published.
//!
//! [`Exact`] holds a binary64 value, or any sum or product of them, as an
//! integer times a power of two, so a check like "`s + t` equals `a + b`" is
//! decided exactly rather than to a tolerance. It shares no arithmetic with
//! the library.

pub mod determinism;

use core::cmp::Ordering;
use core::ops::{Add, Mul, Neg, Sub};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

/// `mantissa · 2^exponent`, exactly.
#[derive(Clone, Debug)]
pub struct Exact {
    mantissa: BigInt,
    exponent: i64,
}

impl Exact {
    /// The exact value of a finite binary64 number, decoded from its bits
    /// (IEEE 754-2019 §3.4).
    ///
    /// # Panics
    ///
    /// If `x` is infinite or a NaN.
    #[must_use]
    pub fn of(x: f64) -> Self {
        assert!(x.is_finite(), "{x} has no exact value");
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

    /// `2^exponent`.
    #[must_use]
    pub fn power_of_two(exponent: i64) -> Self {
        Self {
            mantissa: BigInt::from(1),
            exponent,
        }
    }

    /// An integer `n`.
    #[must_use]
    pub fn integer(n: i64) -> Self {
        Self {
            mantissa: BigInt::from(n),
            exponent: 0,
        }
    }

    /// Both mantissas at the smaller of the two exponents.
    fn aligned(&self, other: &Self) -> (BigInt, BigInt, i64) {
        let exponent = self.exponent.min(other.exponent);
        let shift = |x: &Self| &x.mantissa << usize::try_from(x.exponent - exponent).unwrap();
        (shift(self), shift(other), exponent)
    }

    /// `|self|`.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self {
            mantissa: self.mantissa.abs(),
            exponent: self.exponent,
        }
    }

    /// Whether the value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.mantissa.is_zero()
    }
}

impl Add for &Exact {
    type Output = Exact;
    fn add(self, other: &Exact) -> Exact {
        let (a, b, exponent) = self.aligned(other);
        Exact {
            mantissa: a + b,
            exponent,
        }
    }
}

impl Sub for &Exact {
    type Output = Exact;
    fn sub(self, other: &Exact) -> Exact {
        let (a, b, exponent) = self.aligned(other);
        Exact {
            mantissa: a - b,
            exponent,
        }
    }
}

impl Mul for &Exact {
    type Output = Exact;
    fn mul(self, other: &Exact) -> Exact {
        Exact {
            mantissa: &self.mantissa * &other.mantissa,
            exponent: self.exponent + other.exponent,
        }
    }
}

impl Neg for &Exact {
    type Output = Exact;
    fn neg(self) -> Exact {
        Exact {
            mantissa: -&self.mantissa,
            exponent: self.exponent,
        }
    }
}

impl PartialEq for Exact {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Exact {}

impl PartialOrd for Exact {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Exact {
    fn cmp(&self, other: &Self) -> Ordering {
        let (a, b, _) = self.aligned(other);
        a.cmp(&b)
    }
}

/// A reproducible stream of 64-bit words (xorshift64), so test inputs need no
/// platform function and no seed from the environment.
#[derive(Clone, Debug)]
pub struct Words(u64);

impl Words {
    /// A stream from a nonzero seed.
    #[must_use]
    pub const fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// The next word.
    pub fn next_word(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A normal binary64 number with the given exponent (`2^e ≤ |x| < 2^(e+1)`),
    /// a random significand and a random sign.
    ///
    /// # Panics
    ///
    /// If `e` is outside the normal exponent range.
    pub fn with_exponent(&mut self, e: i64) -> f64 {
        assert!((-1022..=1023).contains(&e));
        let word = self.next_word();
        let biased = u64::try_from(e + 1023).unwrap();
        f64::from_bits((word & (1 << 63)) | (biased << 52) | (word >> 12))
    }
}
