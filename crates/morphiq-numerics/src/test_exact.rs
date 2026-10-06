//! Exact rationals `mantissa · 2^exponent` for the unit tests, sharing no
//! arithmetic with the library: big-integer arithmetic decides every
//! comparison exactly. The library takes no dependencies, not even for its
//! tests, so the big integer is here: schoolbook arithmetic on 64-bit limbs.
//! Also a reader for the fixtures' JSON, which needs only the shape the
//! generators write.

use crate::q128::Q128;
use crate::q256::Q256;
use core::cmp::Ordering;
use std::vec;
use std::vec::Vec;

/// A signed integer of any size: sign and little-endian 64-bit limbs, with no
/// high zero limbs (zero has none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BigInt {
    negative: bool,
    limbs: Vec<u64>,
}

impl BigInt {
    pub(crate) fn from_u128(v: u128) -> Self {
        #[allow(clippy::cast_possible_truncation)]
        Self::normalized(false, vec![v as u64, (v >> 64) as u64])
    }

    fn normalized(negative: bool, mut limbs: Vec<u64>) -> Self {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        Self {
            negative: negative && !limbs.is_empty(),
            limbs,
        }
    }

    /// From hexadecimal digits.
    pub(crate) fn parse_hex(digits: &str) -> Self {
        let mut v = Self::from_u128(0);
        for c in digits.chars() {
            let digit = c.to_digit(16).unwrap();
            v = v.shl(4).add(&Self::from_u128(u128::from(digit)));
        }
        v
    }

    pub(crate) fn is_negative(&self) -> bool {
        self.negative
    }

    pub(crate) fn neg(&self) -> Self {
        Self::normalized(!self.negative, self.limbs.clone())
    }

    pub(crate) fn abs(&self) -> Self {
        Self::normalized(false, self.limbs.clone())
    }

    fn cmp_magnitude(a: &[u64], b: &[u64]) -> Ordering {
        a.len()
            .cmp(&b.len())
            .then_with(|| a.iter().rev().cmp(b.iter().rev()))
    }

    fn add_magnitude(a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut out = Vec::with_capacity(a.len().max(b.len()) + 1);
        let mut carry = 0u128;
        for i in 0..a.len().max(b.len()) {
            let s =
                u128::from(*a.get(i).unwrap_or(&0)) + u128::from(*b.get(i).unwrap_or(&0)) + carry;
            #[allow(clippy::cast_possible_truncation)]
            out.push(s as u64);
            carry = s >> 64;
        }
        #[allow(clippy::cast_possible_truncation)]
        out.push(carry as u64);
        out
    }

    /// `a − b` for `|a| ≥ |b|`.
    fn sub_magnitude(a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut out = Vec::with_capacity(a.len());
        let mut borrow = false;
        for (i, &x) in a.iter().enumerate() {
            let (d, b1) = x.overflowing_sub(*b.get(i).unwrap_or(&0));
            let (d, b2) = d.overflowing_sub(u64::from(borrow));
            out.push(d);
            borrow = b1 || b2;
        }
        out
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        if self.negative == other.negative {
            return Self::normalized(
                self.negative,
                Self::add_magnitude(&self.limbs, &other.limbs),
            );
        }
        match Self::cmp_magnitude(&self.limbs, &other.limbs) {
            Ordering::Less => Self::normalized(
                other.negative,
                Self::sub_magnitude(&other.limbs, &self.limbs),
            ),
            _ => Self::normalized(
                self.negative,
                Self::sub_magnitude(&self.limbs, &other.limbs),
            ),
        }
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        let mut out = vec![0u64; self.limbs.len() + other.limbs.len() + 1];
        for (i, &a) in self.limbs.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &b) in other.limbs.iter().enumerate() {
                let t = u128::from(a) * u128::from(b) + u128::from(out[i + j]) + carry;
                #[allow(clippy::cast_possible_truncation)]
                {
                    out[i + j] = t as u64;
                }
                carry = t >> 64;
            }
            let mut k = i + other.limbs.len();
            while carry != 0 {
                let t = u128::from(out[k]) + carry;
                #[allow(clippy::cast_possible_truncation)]
                {
                    out[k] = t as u64;
                }
                carry = t >> 64;
                k += 1;
            }
        }
        Self::normalized(self.negative != other.negative, out)
    }

    pub(crate) fn shl(&self, n: usize) -> Self {
        let (limbs, bits) = (n / 64, n % 64);
        let mut out = vec![0u64; limbs];
        let mut carry = 0u64;
        for &x in &self.limbs {
            if bits == 0 {
                out.push(x);
            } else {
                out.push((x << bits) | carry);
                carry = x >> (64 - bits);
            }
        }
        out.push(carry);
        Self::normalized(self.negative, out)
    }

    pub(crate) fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => Self::cmp_magnitude(&self.limbs, &other.limbs),
            (true, true) => Self::cmp_magnitude(&other.limbs, &self.limbs),
        }
    }
}

/// The objects of the array at `path` in a fixture, each as its raw text: the
/// generators write flat objects, so no array element contains a bracket.
pub(crate) fn entries<'a>(fixture: &'a str, path: &[&str]) -> Vec<&'a str> {
    let mut at = 0;
    for key in path {
        at += fixture[at..].find(&std::format!("\"{key}\":")).unwrap();
    }
    let start = at + fixture[at..].find('[').unwrap() + 1;
    let end = start + fixture[start..].find(']').unwrap();
    fixture[start..end]
        .split('}')
        .filter(|object| object.contains('{'))
        .collect()
}

/// A field of an object `entries` returned, as its raw text without quotes.
pub(crate) fn field<'a>(object: &'a str, key: &str) -> &'a str {
    let after = &object[object.find(&std::format!("\"{key}\":")).unwrap() + key.len() + 3..];
    let value = after.trim_start();
    let end = value.find([',', '\n']).unwrap_or(value.len());
    value[..end].trim().trim_matches('"')
}

/// A binary64 written as its encoding in hexadecimal.
pub(crate) fn word(object: &str, key: &str) -> f64 {
    f64::from_bits(u64::from_str_radix(field(object, key), 16).unwrap())
}

/// `mantissa · 2^exponent`, exactly.
#[derive(Clone, Debug)]
pub(crate) struct Exact {
    pub(crate) mantissa: BigInt,
    pub(crate) exponent: i64,
}

impl Exact {
    pub(crate) fn of(q: Q128) -> Self {
        let (negative, m, e) = q.parts();
        let magnitude = BigInt::from_u128(m);
        Self {
            mantissa: if negative { magnitude.neg() } else { magnitude },
            exponent: i64::from(e),
        }
    }

    pub(crate) fn of_q256(q: Q256) -> Self {
        let (negative, m, e) = q.parts();
        let magnitude = m.iter().rev().fold(BigInt::from_u128(0), |acc, &limb| {
            acc.shl(64).add(&BigInt::from_u128(u128::from(limb)))
        });
        Self {
            mantissa: if negative { magnitude.neg() } else { magnitude },
            exponent: i64::from(e),
        }
    }

    /// A positive reference value from a fixture: `m` in hexadecimal, `2^e`.
    pub(crate) fn of_hex(m: &str, e: i64) -> Self {
        Self {
            mantissa: BigInt::parse_hex(m),
            exponent: e,
        }
    }

    /// `|self − reference| ≤ 2^−bound_log2 · |reference|`, decided exactly,
    /// with the bound given as `numerator / 2^shift`.
    pub(crate) fn within(&self, reference: &Self, numerator: u64, shift: i64) -> bool {
        let error = self.sub(reference).abs();
        let bound = reference.abs().mul(&Self {
            mantissa: BigInt::from_u128(u128::from(numerator)),
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
        let magnitude = BigInt::from_u128(u128::from(significand));
        Self {
            mantissa: if bits >> 63 == 1 {
                magnitude.neg()
            } else {
                magnitude
            },
            exponent,
        }
    }

    pub(crate) fn pow2(k: i64) -> Self {
        Self {
            mantissa: BigInt::from_u128(1),
            exponent: k,
        }
    }

    /// Both mantissas on the finer grid.
    pub(crate) fn aligned(&self, other: &Self) -> (BigInt, BigInt) {
        let e = self.exponent.min(other.exponent);
        let shift = |x: &Self| x.mantissa.shl(usize::try_from(x.exponent - e).unwrap());
        (shift(self), shift(other))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let (a, b) = self.aligned(other);
        Self {
            mantissa: a.add(&b),
            exponent: self.exponent.min(other.exponent),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            mantissa: self.mantissa.neg(),
            exponent: self.exponent,
        }
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        Self {
            mantissa: self.mantissa.mul(&other.mantissa),
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
