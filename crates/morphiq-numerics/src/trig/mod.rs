//! `sin`, `cos` and `sincos`.
//!
//! The derivation is in
//! [`docs/sin_cos.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sin_cos.md);
//! section numbers below refer to it.

mod reduction;
mod tables;

use crate::double_word::DoubleWord;
use crate::eft::two_prod;
use crate::ln::decide_with;
use crate::q256::Q256;
use reduction::{FRACTION_BITS, HALF_PI, HALF_PI_EXPONENT, TWO_OVER_PI};
use tables::{COS_STEPS, POLY_C, POLY_S, SIN_STEPS, TABLE};

/// `RN(π/4)`, below `π/4`: up to it, `x` needs no reduction (§3).
const QUARTER_PI: f64 = f64::from_bits(0x3fe9_21fb_5444_2d18);
/// The largest `x` with `RN(sin x) = x` (§1; the reference fixture's threshold
/// "largest x with sin(x) = x", Lefèvre and Muller's Table 2, `1.4422·2^−26`).
const SIN_IS_X: f64 = f64::from_bits(0x3e47_1374_4912_3ef6);
/// `cos x` for `|x| < 2^−25` (§1): the largest `|x|` with
/// `RN(cos x) = 1 − k·2^−53`, `k = 0..3`; beyond the last, `1 − 4·2^−53`.
const COS_STEPS_SMALL: [f64; 4] = [
    f64::from_bits(0x3e46_a09e_667f_3bcc),
    f64::from_bits(0x3e53_988e_1409_212e),
    f64::from_bits(0x3e59_4c58_3ada_5b52),
    f64::from_bits(0x3e5d_eeea_1168_3f49),
];
/// `2^−25`.
const COS_SMALL: f64 = f64::from_bits(0x3e60_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−62` (§6).
const EPS: f64 = f64::from_bits(0x3c10_0000_0000_0004);
/// `1.5 · 2^52`: adding and subtracting it rounds to the nearest integer.
const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);

/// `sin x`: correctly rounded wherever Lefèvre and Muller's worst cases cover it
/// (`|x| ≤ 1.4422·2^−26` and `2^−24 ≤ |x| ≤ 2 + 4675/8192`) and whenever the
/// rounding test decides; otherwise within `(1/2 + 2^−140)` ulp (§6).
///
/// `sin(±0) = ±0`; `sin(±∞)` and `sin(NaN)` are NaN.
#[must_use]
pub fn sin(x: f64) -> f64 {
    if !x.is_finite() {
        return f64::NAN;
    }
    if x.abs() <= SIN_IS_X {
        return x;
    }
    let reduced = Reduced::of(x);
    reduced.finish(Function::Sin)
}

/// `cos x`: correctly rounded wherever Lefèvre and Muller's worst cases cover it
/// (`|x| ≤ 12867/8192`) and whenever the rounding test decides; otherwise
/// within `(1/2 + 2^−140)` ulp (§6).
///
/// `cos(±∞)` and `cos(NaN)` are NaN.
#[must_use]
pub fn cos(x: f64) -> f64 {
    if !x.is_finite() {
        return f64::NAN;
    }
    let a = x.abs();
    if a < COS_SMALL {
        let k = COS_STEPS_SMALL.iter().take_while(|&&t| a > t).count();
        #[allow(clippy::cast_precision_loss)] // k <= 4
        return 1.0 - k as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
    }
    Reduced::of(x).finish(Function::Cos)
}

/// The largest `x` with `RN(tan y) = y` for every `|y| ≤ x` (§8; the reference
/// fixture's threshold, Lefèvre and Muller's Table 2 value `1.817·2^−27`).
const TAN_IS_X: f64 = f64::from_bits(0x3e4d_12ed_0af1_a27e);
/// `tan`'s rounding-test constant, `ε₁ = 2^−60` (§8).
const EPS_TAN: f64 = f64::from_bits(0x3c30_0000_0000_0004);

/// `tan x`: correctly rounded wherever Lefèvre and Muller's worst cases cover
/// it (`|x| ≤ 1.817·2^−27` and `2^−25 ≤ |x| ≤ arctan 2`) and whenever the
/// rounding test decides; otherwise within `(1/2 + 2^−142)` ulp (§8).
///
/// `tan(±0) = ±0`; `tan(±∞)` and `tan(NaN)` are NaN.
#[must_use]
pub fn tan(x: f64) -> f64 {
    if !x.is_finite() {
        return f64::NAN;
    }
    if x.abs() <= TAN_IS_X {
        return x;
    }
    let reduced = Reduced::of(x);
    if let Some(v) = tan_fast(&reduced).and_then(|y| decide_with(y, EPS_TAN)) {
        return v;
    }
    tan_accurate(&reduced).to_f64()
}

/// `tan |x| = tan r` for even `k` and `−cot r` for odd `k` (§8): the quotient's
/// numerator, denominator and sign.
fn tan_parts<T: Copy>(reduced: &Reduced, s: T, c: T) -> (T, T, bool) {
    let odd = reduced.k & 1 == 1;
    let (num, den) = if odd { (c, s) } else { (s, c) };
    (num, den, odd != reduced.negative)
}

/// §8: the fast `sin r` and `cos r` divided with `checked_div`, within
/// `2^−60` of `tan x` (`formal/trig/fast_tan.g`); `None` outside the division's
/// proved domain, which sends the argument to the accurate path.
fn tan_fast(reduced: &Reduced) -> Option<DoubleWord> {
    let (s, c) = fast(&reduced.r);
    let (num, den, negate) = tan_parts(reduced, s, c);
    let q = num.checked_div(den).ok()?;
    Some(if negate { q.neg() } else { q })
}

/// §8: the accurate `sin r` and `cos r`, divided by `Q256::recip`, within
/// `2^−196` of `tan x` (`formal/trig/accurate_tan.g`).
fn tan_accurate(reduced: &Reduced) -> Q256 {
    let (s, c) = accurate(reduced.r);
    let (num, den, negate) = tan_parts(reduced, s, c);
    let q = num.mul(den.recip());
    if negate { q.neg() } else { q }
}

/// `(sin x, cos x)`, exactly the pair [`sin`] and [`cos`] return, with the
/// reduction shared.
#[must_use]
pub fn sincos(x: f64) -> (f64, f64) {
    if !x.is_finite() || x.abs() <= SIN_IS_X || x.abs() < COS_SMALL {
        return (sin(x), cos(x));
    }
    let reduced = Reduced::of(x);
    (reduced.finish(Function::Sin), reduced.finish(Function::Cos))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Function {
    Sin,
    Cos,
}

/// `|x| = k·π/2 + r` and `x`'s sign (§3).
struct Reduced {
    negative: bool,
    k: u32,
    r: Q256,
}

impl Reduced {
    fn of(x: f64) -> Self {
        let (k, r) = reduce(x.abs());
        Self {
            negative: x < 0.0,
            k,
            r,
        }
    }

    /// Which of `±sin r`, `±cos r` the function is, by `k` (§3): the
    /// quadrant, then `sin`'s oddness.
    fn select(&self, function: Function) -> (bool, bool) {
        let shift = if function == Function::Cos { 1 } else { 0 };
        let quadrant = (self.k + shift) & 3;
        let use_cos = quadrant & 1 == 1;
        let negate = (quadrant >= 2) != (function == Function::Sin && self.negative);
        (use_cos, negate)
    }

    fn finish(&self, function: Function) -> f64 {
        let (use_cos, negate) = self.select(function);
        let (s, c) = fast(&self.r);
        let y = if use_cos { c } else { s };
        let y = if negate { y.neg() } else { y };
        if let Some(v) = decide_with(y, EPS) {
            return v;
        }
        let (s, c) = accurate(self.r);
        let y = if use_cos { c } else { s };
        (if negate { y.neg() } else { y }).to_f64()
    }
}

/// §4: `(sin r, cos r)` as double-words, each within `2^−62`, by the table
/// at `a = i/64` and polynomials in `t = r − a`.
fn fast(r: &Q256) -> (DoubleWord, DoubleWord) {
    let r_hi = r.to_f64();
    let r_lo = r.add(Q256::from_f64(-r_hi)).to_f64();
    let negative = r_hi < 0.0;
    let (r_hi, r_lo) = if negative {
        (-r_hi, -r_lo)
    } else {
        (r_hi, r_lo)
    };
    let i = (r_hi * 64.0 + SHIFTER) - SHIFTER;
    // t = r − i/64: exact, by Sterbenz's lemma for i ≥ 1.
    let t = DoubleWord::sum(r_hi - i * 0.015_625, r_lo);
    let (t_hi, t_lo) = (t.hi(), t.lo());
    let (u_hi, u_lo) = two_prod(t_hi, t_hi);
    let [s0, s1, s2] = POLY_S;
    let [c0, c1, c2] = POLY_C;
    let ps = s0 + u_hi * (s1 + u_hi * s2);
    let pc = c0 + u_hi * (c1 + u_hi * c2);
    // sin t = t + t³·Ps(t²); cos t − 1 = −t²/2 + t⁴·Pc(t²).
    let sin_t = t.add_f64((t_hi * u_hi) * ps);
    let cos_t_m1 =
        DoubleWord::sum(-0.5 * u_hi, -0.5 * u_lo).add_f64((u_hi * u_hi) * pc - t_hi * t_lo);
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 0 <= i <= 50
    let [(s_hi, s_lo), (c_hi, c_lo)] = TABLE[i as usize];
    let s = DoubleWord::sum(f64::from_bits(s_hi), f64::from_bits(s_lo));
    let c = DoubleWord::sum(f64::from_bits(c_hi), f64::from_bits(c_lo));
    let sin = s.add(s.mul(cos_t_m1).add(c.mul(sin_t)));
    let cos = c.add(c.mul(cos_t_m1).sub(s.mul(sin_t)));
    (if negative { sin.neg() } else { sin }, cos)
}

/// §5: `(sin r, cos r)` in `Q256` from their series in `s = r²`.
fn accurate(r: Q256) -> (Q256, Q256) {
    let s = r.mul(r);
    let series = |steps: &[([u64; 4], i32)]| {
        let mut h = Q256::ONE;
        for &(m, e) in steps.iter().rev() {
            h = Q256::ONE.add(s.mul(Q256::new(false, m, e)).mul(h).neg());
        }
        h
    };
    (r.mul(series(&SIN_STEPS)), series(&COS_STEPS))
}

/// The 64 bits of 2/π of weights `2^−(end−63)` to `2^−end` (1-based, most
/// significant first), as an integer; bits before the first are zero.
fn two_over_pi_bits(end: i32) -> u64 {
    if end < 1 {
        return 0;
    }
    #[allow(clippy::cast_sign_loss)] // end >= 1
    let p = (end - 1) as usize;
    let (w, o) = (p / 64, p % 64);
    let here = TWO_OVER_PI[w] >> (63 - o);
    // The rest comes from the previous word, unless this one holds all 64 bits
    // or there is none before it.
    if o == 63 || w == 0 {
        here
    } else {
        here | (TWO_OVER_PI[w - 1] << (o + 1))
    }
}

/// §3: `x = k·π/2 + r`, `|r| ≤ π/4`, for finite `x ≥ 0`: `k mod 4` and `r` in
/// `Q256`, within `2^−199` of `r` relatively.
///
/// Payne–Hanek: with `x = m·2^E`, bits of `2/π` of weight above `2^(1−E)` only
/// add multiples of 4 to `x·(2/π)`, so the window from there down to
/// `2^−(E+F)` is multiplied by `m` exactly. Its integer part gives `k mod 4`
/// and its `F`-bit fraction `f`, so `r = f·π/2`.
pub(crate) fn reduce(x: f64) -> (u32, Q256) {
    if x <= QUARTER_PI {
        return (0, Q256::from_f64(x));
    }
    let bits = x.to_bits();
    let m = (bits & ((1 << 52) - 1)) | (1 << 52);
    #[allow(clippy::cast_possible_truncation)] // the 11-bit exponent field
    let e = ((bits >> 52) as i32) - 1075;
    #[allow(clippy::cast_possible_wrap)]
    let f = FRACTION_BITS as i32;
    // The window: weights 2^-i0 .. 2^-i1, as an integer of up to 317 bits.
    let (i0, i1) = ((e - 1).max(1), e + f);
    let mut window = [0u64; 5];
    for (j, limb) in window.iter_mut().enumerate() {
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        let end = i1 - 64 * j as i32;
        // Keep the bits of weight at least 2^-i0: positions up to end - i0.
        let keep = end - i0;
        *limb = if keep < 0 {
            0
        } else if keep >= 63 {
            two_over_pi_bits(end)
        } else {
            two_over_pi_bits(end) & ((1u64 << (keep + 1)) - 1)
        };
    }
    // P = m · window: x (2/π) mod 4, scaled by 2^F.
    let mut product = [0u64; 6];
    let mut carry = 0u128;
    for (j, &limb) in window.iter().enumerate() {
        let t = u128::from(m) * u128::from(limb) + carry;
        #[allow(clippy::cast_possible_truncation)]
        {
            product[j] = t as u64;
        }
        carry = t >> 64;
    }
    #[allow(clippy::cast_possible_truncation)]
    {
        product[5] = carry as u64;
    }
    // k: bits F and F + 1. The fraction: bits below F.
    let (word, bit) = ((FRACTION_BITS / 64) as usize, FRACTION_BITS % 64);
    #[allow(clippy::cast_possible_truncation)]
    let mut k =
        ((product[word] >> bit) | product.get(word + 1).map_or(0, |&h| h << (64 - bit))) as u32 & 3;
    let mut fraction = [0u64; 5];
    fraction[..word].copy_from_slice(&product[..word]);
    fraction[word] = product[word] & ((1 << bit) - 1);
    // Round to the nearest multiple: f in [-1/2, 1/2).
    let negative = fraction[word] >> (bit - 1) == 1;
    if negative {
        // |f| = 2^F - fraction.
        let mut borrow = 0u64;
        for limb in fraction.iter_mut() {
            let (d, b1) = 0u64.overflowing_sub(*limb);
            let (d, b2) = d.overflowing_sub(borrow);
            *limb = d;
            borrow = u64::from(b1 || b2);
        }
        fraction[word] &= (1 << bit) - 1;
        k = (k + 1) & 3;
    }
    let f = Q256::from_limbs(negative, &fraction, -f);
    (k, f.mul(Q256::new(false, HALF_PI, HALF_PI_EXPONENT)))
}

#[cfg(test)]
mod tests;
