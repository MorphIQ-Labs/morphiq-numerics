//! `Q256`: sign-magnitude numbers with a 256-bit significand, for the accurate
//! paths of `sin` and `cos`, whose worst cases need more than `Q128` reaches.
//!
//! The contract is `Q128`'s ([`docs/exp.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md)
//! §6) at twice the width:
//! - multiplication: the exact product truncated toward zero to 256 bits,
//!   relative error in `[−2^−255, 0]`;
//! - addition: absolute error at most `2^−254·max(|a|, |b|)`, from truncating
//!   the smaller operand to the larger's 256-bit grid while aligning;
//! - conversion from binary64 and rounding to binary64 (nearest-even,
//!   subnormals included): exact, in integer arithmetic.
//!
//! The significand is four 64-bit limbs, least significant first.

use core::cmp::Ordering;

/// `(−1)^negative · m · 2^e`, with `m` normalized (bit 255 set) or zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Q256 {
    negative: bool,
    m: [u64; 4],
    e: i32,
}

const ZERO_LIMBS: [u64; 4] = [0; 4];

/// The number of leading zero bits of a 256-bit integer.
fn leading_zeros(m: &[u64; 4]) -> u32 {
    let mut n = 0;
    for &limb in m.iter().rev() {
        if limb == 0 {
            n += 64;
        } else {
            return n + limb.leading_zeros();
        }
    }
    n
}

/// `m << s` for `s < 256`, the high bits dropped.
fn shl(m: &[u64; 4], s: u32) -> [u64; 4] {
    let (words, bits) = ((s / 64) as usize, s % 64);
    let mut out = [0u64; 4];
    for i in (words..4).rev() {
        let lo = m[i - words];
        out[i] = if bits == 0 {
            lo
        } else {
            let below = if i > words {
                m[i - words - 1] >> (64 - bits)
            } else {
                0
            };
            (lo << bits) | below
        };
    }
    out
}

/// `m >> s`, truncating; zero for `s >= 256`.
fn shr(m: &[u64; 4], s: u32) -> [u64; 4] {
    if s >= 256 {
        return ZERO_LIMBS;
    }
    let (words, bits) = ((s / 64) as usize, s % 64);
    let mut out = [0u64; 4];
    for i in 0..4 - words {
        let hi = m[i + words];
        out[i] = if bits == 0 {
            hi
        } else {
            let above = if i + words + 1 < 4 {
                m[i + words + 1] << (64 - bits)
            } else {
                0
            };
            (hi >> bits) | above
        };
    }
    out
}

fn is_zero(m: &[u64; 4]) -> bool {
    m.iter().all(|&l| l == 0)
}

fn cmp(a: &[u64; 4], b: &[u64; 4]) -> Ordering {
    a.iter().rev().cmp(b.iter().rev())
}

/// `a + b` and the carry out.
fn add_limbs(a: &[u64; 4], b: &[u64; 4]) -> ([u64; 4], bool) {
    let mut out = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let s = u128::from(a[i]) + u128::from(b[i]) + carry;
        #[allow(clippy::cast_possible_truncation)]
        {
            out[i] = s as u64;
        }
        carry = s >> 64;
    }
    (out, carry != 0)
}

/// `a − b` for `a ≥ b`.
fn sub_limbs(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut borrow = false;
    for i in 0..4 {
        let (d, b1) = a[i].overflowing_sub(b[i]);
        let (d, b2) = d.overflowing_sub(u64::from(borrow));
        out[i] = d;
        borrow = b1 || b2;
    }
    out
}

impl Q256 {
    /// Zero.
    pub(crate) const ZERO: Self = Self {
        negative: false,
        m: ZERO_LIMBS,
        e: 0,
    };

    /// One.
    pub(crate) const ONE: Self = Self {
        negative: false,
        m: [0, 0, 0, 1 << 63],
        e: -255,
    };

    /// `(−1)^negative · m · 2^e` for any 256-bit `m` (limbs least significant
    /// first), normalized exactly.
    pub(crate) fn new(negative: bool, m: [u64; 4], e: i32) -> Self {
        if is_zero(&m) {
            return Self::ZERO;
        }
        let shift = leading_zeros(&m);
        Self {
            negative,
            m: shl(&m, shift),
            #[allow(clippy::cast_possible_wrap)] // shift < 256
            e: e - shift as i32,
        }
    }

    /// `(−1)^negative · m · 2^e` for a wider integer `m` (limbs least
    /// significant first), truncated toward zero to 256 bits: relative error in
    /// `[−2^−255, 0]`, as for a product.
    pub(crate) fn from_limbs(negative: bool, m: &[u64], e: i32) -> Self {
        let Some(top) = m.iter().rposition(|&l| l != 0) else {
            return Self::ZERO;
        };
        // The 256 bits ending at the top limb's leading one.
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        let bits = (64 * top as u32 + 64 - m[top].leading_zeros()) as i32;
        let drop = (bits - 256).max(0);
        #[allow(clippy::cast_sign_loss)]
        let (words, shift) = ((drop / 64) as usize, (drop % 64) as u32);
        let mut out = [0u64; 4];
        for (i, slot) in out.iter_mut().enumerate() {
            let lo = m.get(i + words).copied().unwrap_or(0);
            let hi = m.get(i + words + 1).copied().unwrap_or(0);
            *slot = if shift == 0 {
                lo
            } else {
                (lo >> shift) | (hi << (64 - shift))
            };
        }
        Self::new(negative, out, e + drop)
    }

    /// The exact value of a finite binary64 number.
    pub(crate) fn from_f64(x: f64) -> Self {
        let bits = x.to_bits();
        #[allow(clippy::cast_possible_truncation)] // the 11-bit exponent field
        let biased = ((bits >> 52) & 0x7ff) as i32;
        let fraction = bits & ((1 << 52) - 1);
        let (significand, e) = if biased == 0 {
            (fraction, -1074)
        } else {
            (fraction | (1 << 52), biased - 1075)
        };
        Self::new(bits >> 63 == 1, [significand, 0, 0, 0], e)
    }

    /// `−self`, exactly.
    pub(crate) fn neg(self) -> Self {
        if is_zero(&self.m) {
            return self;
        }
        Self {
            negative: !self.negative,
            ..self
        }
    }

    /// `|self|` against `|other|`, exactly.
    pub(crate) fn cmp_abs(self, other: Self) -> Ordering {
        match (is_zero(&self.m), is_zero(&other.m)) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => self.e.cmp(&other.e).then_with(|| cmp(&self.m, &other.m)),
        }
    }

    /// `(negative, m, e)`, for the tests' exact checks.
    #[cfg(test)]
    pub(crate) fn parts(self) -> (bool, [u64; 4], i32) {
        (self.negative, self.m, self.e)
    }

    /// The product: the exact 512-bit product of the significands truncated
    /// toward zero to its top 256 bits.
    pub(crate) fn mul(self, other: Self) -> Self {
        if is_zero(&self.m) || is_zero(&other.m) {
            return Self::ZERO;
        }
        let mut p = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let t =
                    u128::from(self.m[i]) * u128::from(other.m[j]) + u128::from(p[i + j]) + carry;
                #[allow(clippy::cast_possible_truncation)]
                {
                    p[i + j] = t as u64;
                }
                carry = t >> 64;
            }
            #[allow(clippy::cast_possible_truncation)]
            {
                p[i + 4] = carry as u64;
            }
        }
        // Both significands are at least 2^255, so the product is at least
        // 2^510: its top bit is bit 511 or bit 510.
        let hi = [p[4], p[5], p[6], p[7]];
        let (m, e) = if p[7] >> 63 == 1 {
            (hi, self.e + other.e + 256)
        } else {
            let lo = [p[0], p[1], p[2], p[3]];
            let m = shl(&hi, 1);
            (
                [m[0] | (lo[3] >> 63), m[1], m[2], m[3]],
                self.e + other.e + 255,
            )
        };
        Self {
            negative: self.negative != other.negative,
            m,
            e,
        }
    }

    /// The sum: the smaller operand truncated to the larger's grid, then added.
    pub(crate) fn add(self, other: Self) -> Self {
        if is_zero(&self.m) {
            return other;
        }
        if is_zero(&other.m) {
            return self;
        }
        let (big, small) = match self.cmp_abs(other) {
            Ordering::Less => (other, self),
            _ => (self, other),
        };
        #[allow(clippy::cast_sign_loss)] // big.e >= small.e
        let aligned = shr(&small.m, (big.e - small.e) as u32);
        if big.negative == small.negative {
            let (sum, carry) = add_limbs(&big.m, &aligned);
            if carry {
                let mut m = shr(&sum, 1);
                m[3] |= 1 << 63;
                Self {
                    negative: big.negative,
                    m,
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
            Self::new(big.negative, sub_limbs(&big.m, &aligned), big.e)
        }
    }

    /// `1/self` for a nonzero `self` whose magnitude is a normal binary64's,
    /// within `2^−252` relatively: three Newton steps
    /// `y ← y + y·(1 − self·y)` from `y_0 = RN(1/RN(self))`, each step squaring
    /// the error, under this type's own rounding (certified:
    /// `formal/trig/recip_0.g` to `recip_3.g`).
    pub(crate) fn recip(self) -> Self {
        let mut y = Self::from_f64(1.0 / self.to_f64());
        for _ in 0..3 {
            let error = Self::ONE.add(self.mul(y).neg());
            y = y.add(y.mul(error));
        }
        y
    }

    /// `self` rounded to binary64, to nearest with ties to even, subnormals
    /// included; `±∞` beyond the largest finite magnitude.
    pub(crate) fn to_f64(self) -> f64 {
        let sign = if self.negative { 1u64 << 63 } else { 0 };
        if is_zero(&self.m) {
            return f64::from_bits(sign);
        }
        // |self| lies in [2^top, 2^(top + 1)).
        let top = self.e + 255;
        if top > 1023 {
            return f64::from_bits(sign | 0x7ff0_0000_0000_0000);
        }
        let quantum = if top >= -1022 { top - 52 } else { -1074 };
        #[allow(clippy::cast_sign_loss)] // quantum - e >= 203
        let shift = (quantum - self.e) as u32;
        // The kept bits (at most 53) and the comparison of the rest with half.
        let kept = shr(&self.m, shift)[0];
        let round_up = if shift > 256 {
            false // below half the least subnormal
        } else {
            let rest = if shift == 256 {
                self.m
            } else {
                shl(&self.m, 256 - shift)
            };
            // rest holds the discarded bits at the top: half is bit 255 alone.
            let half = [0, 0, 0, 1 << 63];
            match cmp(&rest, &half) {
                Ordering::Greater => true,
                Ordering::Equal => kept & 1 == 1,
                Ordering::Less => false,
            }
        };
        let mut significand = kept + u64::from(round_up);
        if top >= -1022 {
            let mut biased = top + 1023;
            if significand == 1 << 53 {
                significand = 1 << 52;
                biased += 1;
            }
            #[allow(clippy::cast_sign_loss)] // biased >= 1
            let field = (biased as u64) << 52;
            f64::from_bits(sign | field | (significand & ((1 << 52) - 1)))
        } else {
            f64::from_bits(sign | significand)
        }
    }
}

#[cfg(test)]
mod tests;
