//! The IEEE 754 square root, rounded to nearest with ties to even, in integer
//! arithmetic (`docs/sqrt.md`): the crate is `no_std` and can't reach a
//! platform `sqrt`.

/// The trailing significand field.
const FRACTION: u64 = (1 << 52) - 1;

/// `⌊√r⌋` and `r − ⌊√r⌋²`, by the binary digit-by-digit method.
const fn isqrt(r: u128) -> (u128, u128) {
    let mut rem = r;
    let mut root = 0_u128;
    let mut bit = 1_u128 << 126;
    while bit > r {
        bit >>= 2;
    }
    while bit != 0 {
        if rem >= root + bit {
            rem -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    (root, rem)
}

/// `√x`, correctly rounded: the binary64 number nearest `√x`, IEEE 754's
/// `squareRoot` (§5.4.1). `sqrt(±0) = ±0`, `sqrt(+∞) = +∞`, and a NaN or any
/// `x < 0` gives NaN.
///
/// Computed in integer arithmetic by the digit-by-digit method, and checked bit
/// for bit against Flocq's proved IEEE 754 square root
/// (`formal/binary64/IEEE64Sqrt.v`) on the cross-check corpus
/// ([`docs/sqrt.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sqrt.md)).
#[must_use]
pub const fn sqrt(x: f64) -> f64 {
    if x.is_nan() || (x < 0.0) {
        return f64::NAN;
    }
    if x == 0.0 || x == f64::INFINITY {
        return x;
    }
    // x = m·2^e with 2^52 <= m < 2^53, normalizing a subnormal.
    let bits = x.to_bits();
    let biased = (bits >> 52) as i32;
    let (mut m, mut e) = if biased == 0 {
        let f = bits & FRACTION;
        let shift = f.leading_zeros() as i32 - 11;
        (f << shift, -1074 - shift)
    } else {
        ((bits & FRACTION) | (1 << 52), biased - 1075)
    };
    // An even exponent: m in [2^52, 2^54).
    if e & 1 != 0 {
        m <<= 1;
        e -= 1;
    }
    // √(m·2^54) has 54 bits: 53 kept and a rounding bit; the remainder is the
    // sticky bit. √x = s·2^((e − 54)/2).
    let (s, rem) = isqrt((m as u128) << 54);
    let (kept, half) = ((s >> 1) as u64, s & 1 == 1);
    // A tie would need s odd with s² = m·2^54, which is even: impossible, but
    // the rule is stated whole.
    let up = half && (rem != 0 || kept & 1 == 1);
    let mut significand = kept + up as u64;
    let mut exponent = (e - 54) / 2 + 1;
    if significand == 1 << 53 {
        significand >>= 1;
        exponent += 1;
    }
    // √x = significand·2^exponent: always normal, since √(2^−1074) = 2^−537.
    f64::from_bits((((exponent + 1075) as u64) << 52) | (significand & FRACTION))
}

#[cfg(test)]
mod tests;
