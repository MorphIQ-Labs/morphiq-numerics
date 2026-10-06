//! `Q128`: sign-magnitude numbers with a 128-bit significand, for the accurate
//! paths of the elementary functions.
//!
//! The contract the certificates assume is in
//! [`docs/exp.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md)
//! §6:
//! - multiplication: the exact product truncated toward zero to 128 bits,
//!   relative error in `[−2^−127, 0]`;
//! - addition: absolute error at most `2^−126·max(|a|, |b|)`, from truncating
//!   the smaller operand to the larger's 128-bit grid while aligning;
//! - conversion from binary64 and rounding to binary64 (nearest-even,
//!   subnormals included): exact, in integer arithmetic.
//!
//! Exponents stay within a few thousand of zero in every use, far inside `i32`.

use core::cmp::Ordering;

/// `(−1)^negative · m · 2^e`, with `m` normalized (top bit set) or zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Q128 {
    negative: bool,
    m: u128,
    e: i32,
}

const TOP: u128 = 1 << 127;
const LOW_64: u128 = (1 << 64) - 1;

impl Q128 {
    /// Zero.
    pub(crate) const ZERO: Self = Self {
        negative: false,
        m: 0,
        e: 0,
    };

    /// One.
    pub(crate) const ONE: Self = Self {
        negative: false,
        m: TOP,
        e: -127,
    };

    /// `(−1)^negative · m · 2^e` for any `m`, normalized exactly.
    pub(crate) const fn new(negative: bool, m: u128, e: i32) -> Self {
        if m == 0 {
            return Self::ZERO;
        }
        let shift = m.leading_zeros();
        Self {
            negative,
            m: m << shift,
            #[allow(clippy::cast_possible_wrap)] // shift <= 127
            e: e - shift as i32,
        }
    }

    /// The exact value of a finite binary64 number.
    pub(crate) const fn from_f64(x: f64) -> Self {
        let bits = x.to_bits();
        let biased = ((bits >> 52) & 0x7ff) as i32;
        let fraction = bits & ((1 << 52) - 1);
        let (significand, e) = if biased == 0 {
            (fraction, -1074)
        } else {
            (fraction | (1 << 52), biased - 1075)
        };
        Self::new(bits >> 63 == 1, significand as u128, e)
    }

    /// `−self`, exactly.
    pub(crate) const fn neg(self) -> Self {
        if self.m == 0 {
            return self;
        }
        Self {
            negative: !self.negative,
            ..self
        }
    }

    /// `self · 2^k`, exactly.
    pub(crate) const fn mul_pow2(self, k: i32) -> Self {
        if self.m == 0 {
            return self;
        }
        Self {
            e: self.e + k,
            ..self
        }
    }

    /// `|self|` against `|other|`, exactly.
    pub(crate) const fn cmp_abs(self, other: Self) -> Ordering {
        match (self.m == 0, other.m == 0) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => {
                if self.e != other.e {
                    if self.e < other.e {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                } else if self.m < other.m {
                    Ordering::Less
                } else if self.m > other.m {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
        }
    }

    /// `(negative, m, e)`, for the tests' exact checks.
    #[cfg(test)]
    pub(crate) const fn parts(self) -> (bool, u128, i32) {
        (self.negative, self.m, self.e)
    }

    /// Whether `self` is negative (zero is not).
    pub(crate) const fn is_negative(self) -> bool {
        self.negative && self.m != 0
    }

    /// The product, the exact 256-bit product of the significands truncated
    /// toward zero to its top 128 bits.
    pub(crate) const fn mul(self, other: Self) -> Self {
        if self.m == 0 || other.m == 0 {
            return Self::ZERO;
        }
        let (a1, a0) = (self.m >> 64, self.m & LOW_64);
        let (b1, b0) = (other.m >> 64, other.m & LOW_64);
        let p00 = a0 * b0;
        let p01 = a0 * b1;
        let p10 = a1 * b0;
        let p11 = a1 * b1;
        // The 256-bit product hi · 2^128 + lo.
        let mid = (p00 >> 64) + (p01 & LOW_64) + (p10 & LOW_64);
        let lo = (p00 & LOW_64) | (mid << 64);
        let hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
        // Both significands are at least 2^127, so the product is at least
        // 2^254: its top bit is bit 255 or bit 254.
        let (m, e) = if hi & TOP != 0 {
            (hi, self.e + other.e + 128)
        } else {
            ((hi << 1) | (lo >> 127), self.e + other.e + 127)
        };
        Self {
            negative: self.negative != other.negative,
            m,
            e,
        }
    }

    /// The sum: the smaller operand truncated to the larger's grid, then added.
    pub(crate) const fn add(self, other: Self) -> Self {
        if self.m == 0 {
            return other;
        }
        if other.m == 0 {
            return self;
        }
        let (big, small) = match self.cmp_abs(other) {
            Ordering::Less => (other, self),
            _ => (self, other),
        };
        // |big| >= |small| and both are normalized, so big.e >= small.e.
        #[allow(clippy::cast_sign_loss)] // non-negative
        let d = (big.e - small.e) as u32;
        let aligned = if d >= 128 { 0 } else { small.m >> d };
        if big.negative == small.negative {
            let (sum, carry) = big.m.overflowing_add(aligned);
            if carry {
                Self {
                    negative: big.negative,
                    m: (sum >> 1) | TOP,
                    e: big.e + 1,
                }
            } else {
                Self {
                    negative: big.negative,
                    m: sum,
                    e: big.e,
                }
            }
        } else {
            Self::new(big.negative, big.m - aligned, big.e)
        }
    }

    /// `self` rounded to binary64, to nearest with ties to even, subnormals
    /// included; `±∞` beyond the largest finite magnitude.
    pub(crate) const fn to_f64(self) -> f64 {
        let sign = if self.negative { 1u64 << 63 } else { 0 };
        if self.m == 0 {
            return f64::from_bits(sign);
        }
        // |self| lies in [2^top, 2^(top + 1)).
        let top = self.e + 127;
        if top > 1023 {
            return f64::from_bits(sign | 0x7ff0_0000_0000_0000);
        }
        // The quantum of the result's binade, and the bits below it.
        let quantum = if top >= -1022 { top - 52 } else { -1074 };
        #[allow(clippy::cast_sign_loss)] // quantum - e >= 75
        let shift = (quantum - self.e) as u32;
        let mut kept = if shift >= 128 { 0 } else { self.m >> shift };
        let round_up = if shift > 128 {
            false // below half the least subnormal
        } else {
            let half = 1u128 << (shift - 1);
            let rem = if shift == 128 {
                self.m
            } else {
                self.m & ((1u128 << shift) - 1)
            };
            rem > half || (rem == half && kept & 1 == 1)
        };
        if round_up {
            kept += 1;
        }
        #[allow(clippy::cast_possible_truncation)] // kept <= 2^53
        let mut significand = kept as u64;
        if top >= -1022 {
            // Normal: significand in [2^52, 2^53]; 2^53 carries into the
            // exponent, and a carry out of the largest binade gives biased
            // 2047 with a zero fraction, the encoding of infinity.
            let mut biased = top + 1023;
            if significand == 1 << 53 {
                significand = 1 << 52;
                biased += 1;
            }
            #[allow(clippy::cast_sign_loss)] // biased >= 1
            let field = (biased as u64) << 52;
            f64::from_bits(sign | field | (significand & ((1 << 52) - 1)))
        } else {
            // Subnormal: the encoding is the significand itself, and 2^52
            // encodes the least normal number.
            f64::from_bits(sign | significand)
        }
    }
}

#[cfg(test)]
mod tests;
