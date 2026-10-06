//! `sin`, `cos` and `sincos`.
//!
//! The derivation is in
//! [`docs/sin_cos.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sin_cos.md);
//! section numbers below refer to it.

mod reduction;

use crate::q256::Q256;
use reduction::{FRACTION_BITS, HALF_PI, HALF_PI_EXPONENT, TWO_OVER_PI};

/// `RN(π/4)`, below `π/4`: up to it, `x` needs no reduction (§3).
const QUARTER_PI: f64 = f64::from_bits(0x3fe9_21fb_5444_2d18);

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
    if o == 63 || w == 0 {
        if w == 0 && o < 63 {
            return here;
        }
        return here | if o == 63 { 0 } else { TWO_OVER_PI[w - 1] << (o + 1) };
    }
    here | (TWO_OVER_PI[w - 1] << (o + 1))
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
    let mut k = ((product[word] >> bit) | product.get(word + 1).map_or(0, |&h| h << (64 - bit))) as u32 & 3;
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
