//! `ln` and `ln_1p`: natural logarithms rounded to nearest, ties to even.
//!
//! The derivation, every bound and the certificates are in
//! [`docs/ln.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/ln.md);
//! section numbers below refer to it.

mod tables;

use crate::double_word::DoubleWord;
use crate::eft::{two_prod, two_sum};
use crate::q128::Q128;
use crate::ulp::ulp;
use tables::{LN2_HI, LN2_LO, LN2_Q128, NEG_LN_R_BITS, NEG_LN_R_Q128, POLY, R_BITS, RECIPROCALS};

/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−63` (§5).
const EPS: f64 = f64::from_bits(0x3c00_0000_0000_0004);
/// The binary64 fraction field.
const FRACTION: u64 = (1 << 52) - 1;
/// `2^54`, which scales a subnormal argument to a normal one (§3).
const TWO_54: f64 = f64::from_bits(0x4350_0000_0000_0000);
/// `2^−54`, below which `ln_1p(x)` is `x` (§7).
const TWO_M54: f64 = f64::from_bits(0x3c90_0000_0000_0000);
/// `2^−7`, below which `ln_1p` takes `z = x` (§7).
const TWO_M7: f64 = f64::from_bits(0x3f80_0000_0000_0000);
/// `2^53`, from which `ln_1p` splits `1 + x` as `(x, 1)` (§7).
const TWO_53: f64 = f64::from_bits(0x4340_0000_0000_0000);
/// The accurate path's series degree, `DEGREE` of `generators/ln_constants.py`.
const DEGREE: usize = RECIPROCALS.len();

/// `ln x`, correctly rounded: the binary64 number nearest to the natural
/// logarithm of `x`, ties to even, for every binary64 `x`.
///
/// `ln(±0) = −∞`, `ln(+∞) = +∞` and `ln(1) = +0`; a NaN, a negative `x` and
/// `−∞` give NaN.
#[must_use]
pub fn ln(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x < 0.0 {
        return f64::NAN;
    }
    if x == 0.0 {
        return f64::NEG_INFINITY;
    }
    if x == f64::INFINITY {
        return x;
    }
    if x == 1.0 {
        return 0.0;
    }
    let reduced = Reduced::of(x);
    if let Some(y) = decide(reduced.fast_value()) {
        return y;
    }
    reduced.accurate_value(reduced.z_exact()).to_f64()
}

/// `ln(1 + x)`, without rounding `1 + x`: correctly rounded whenever the
/// rounding test decides it, and otherwise within `(1/2 + 2^−70)` ulp (§7).
///
/// `ln_1p(−1) = −∞`, `ln_1p(+∞) = +∞` and `ln_1p(±0) = ±0`; a NaN, `x < −1`
/// and `−∞` give NaN.
#[must_use]
pub fn ln_1p(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x < -1.0 {
        return f64::NAN;
    }
    if x == -1.0 {
        return f64::NEG_INFINITY;
    }
    if x == f64::INFINITY {
        return x;
    }
    let magnitude = x.abs();
    if magnitude < TWO_M54 {
        return x;
    }
    if magnitude < TWO_M7 {
        // z = x exactly: case A, with no E or table term.
        if let Some(y) = decide(ln_1p_double_word(DoubleWord::from_f64(x))) {
            return y;
        }
        let z = Q128::from_f64(x);
        return z.mul(series(z)).to_f64();
    }
    let (h, l) = split(x);
    let reduced = Reduced::of(h);
    if let Some(y) = decide(reduced.fast_value().add_f64(l / h)) {
        return y;
    }
    reduced.accurate_value(reduced.z_prime(l)).to_f64()
}

/// `1 + x = h + l` exactly, `|l| ≤ 2^−53·(1 + 2u)·|h|`, for `x ≥ −1` (§7).
fn split(x: f64) -> (f64, f64) {
    if x < TWO_53 {
        two_sum(1.0, x)
    } else {
        (x, 1.0)
    }
}

/// The reduction of §3: `x = 2^E·y`, `y ∈ [0.70703125, 1.4140625)`, and
/// `R[i] ≈ 1/y`, so `ln x = E·ln 2 − ln R[i] + ln(1 + z)` with
/// `z = y·R[i] − 1`.
pub(crate) struct Reduced {
    pub(crate) e: i32,
    i: usize,
    y: f64,
    r: f64,
}

impl Reduced {
    /// §3, steps 1–3, for finite `x > 0`.
    pub(crate) fn of(x: f64) -> Self {
        let (bits, scaled) = if x < f64::MIN_POSITIVE {
            ((x * TWO_54).to_bits(), 54)
        } else {
            (x.to_bits(), 0)
        };
        #[allow(clippy::cast_possible_truncation)] // the 11-bit exponent field
        let biased = (bits >> 52) as i32;
        let fraction = bits & FRACTION;
        #[allow(clippy::cast_possible_truncation)] // 7 bits
        let i = (fraction >> 45) as usize;
        let (y, e) = if i < 53 {
            (
                f64::from_bits((1023 << 52) | fraction),
                biased - 1023 - scaled,
            )
        } else {
            (
                f64::from_bits((1022 << 52) | fraction),
                biased - 1022 - scaled,
            )
        };
        Self {
            e,
            i,
            y,
            r: f64::from_bits(R_BITS[i]),
        }
    }

    /// §4: `Y ≈ ln x` as a double-word, within `2^−64` (certified:
    /// `formal/ln/fast_a.g`, `fast_b.g`, `fast_c.g`).
    pub(crate) fn fast_value(&self) -> DoubleWord {
        let e = f64::from(self.e);
        DoubleWord::sum(e * LN2_HI, e * LN2_LO).add(self.ln_y_fast())
    }

    /// §4, steps 1–5: `S = (−ln R[i]) + ln(1 + z) ≈ ln y` as a double-word,
    /// within `2^−64` of `ln y` (`formal/ln/fast_a.g` and `fast_b.g` with
    /// `E = 0`). Shared with `log2`.
    pub(crate) fn ln_y_fast(&self) -> DoubleWord {
        // z = y·R[i] − 1 exactly: the product by two_prod, p − 1 by Sterbenz.
        let (p, q) = two_prod(self.y, self.r);
        let ln_1p_z = ln_1p_double_word(DoubleWord::sum(p - 1.0, q));
        let (n_hi, n_lo) = NEG_LN_R_BITS[self.i];
        DoubleWord::sum(f64::from_bits(n_hi), f64::from_bits(n_lo)).add(ln_1p_z)
    }

    /// §6 for `ln y`: `(−ln R[i]) + z·G_1` in `Q128`, the table term skipped
    /// where `R[i] = 1`, within `2^−123` of `ln y` (`formal/ln/accurate_sum_a.g`
    /// and `_b.g`). Shared with `log2`.
    pub(crate) fn ln_y_accurate(&self, z: Q128) -> Q128 {
        let ln_1p_z = z.mul(series(z));
        if self.r == 1.0 {
            return ln_1p_z;
        }
        let (negative, m, e) = NEG_LN_R_Q128[self.i];
        Q128::new(negative, m, e).add(ln_1p_z)
    }

    /// `z = y·R[i] − 1` exactly, from the significands in integer arithmetic
    /// (§6, step 1).
    pub(crate) fn z_exact(&self) -> Q128 {
        let (m_y, e_y) = significand(self.y);
        let (m_r, e_r) = significand(self.r);
        let product = u128::from(m_y) * u128::from(m_r);
        let scale = e_y + e_r;
        // 1 on the product's grid: scale is between −106 and −104.
        #[allow(clippy::cast_sign_loss)]
        let one = 1u128 << (-scale) as u32;
        if product >= one {
            Q128::new(false, product - one, scale)
        } else {
            Q128::new(true, one - product, scale)
        }
    }

    /// `ln_1p`'s `z' = (y·R[i] − 1) + R[i]·l·2^−E` (§7): the second term an
    /// exact `Q128` product, the sum one `Q128` addition.
    fn z_prime(&self, l: f64) -> Q128 {
        let low = Q128::from_f64(self.r)
            .mul(Q128::from_f64(l))
            .mul_pow2(-self.e);
        self.z_exact().add(low)
    }

    /// §6: `(E·ln 2 + (−ln R[i])) + z·G_1` in `Q128`, a zero term skipped,
    /// within `2^−123` of `ln x` (certified: `formal/ln/accurate_sum_*.g`).
    pub(crate) fn accurate_value(&self, z: Q128) -> Q128 {
        let ln_1p_z = z.mul(series(z));
        let e_ln2 = (self.e != 0)
            .then(|| Q128::from_f64(f64::from(self.e)).mul(Q128::new(false, LN2_Q128, -128)));
        let neg_ln_r = (self.r != 1.0).then(|| {
            let (negative, m, e) = NEG_LN_R_Q128[self.i];
            Q128::new(negative, m, e)
        });
        match (e_ln2, neg_ln_r) {
            (Some(a), Some(b)) => a.add(b).add(ln_1p_z),
            (Some(t), None) | (None, Some(t)) => t.add(ln_1p_z),
            (None, None) => ln_1p_z,
        }
    }
}

/// `(m, e)` with `v = m·2^e`, for a positive normal `v`.
fn significand(v: f64) -> (u64, i32) {
    let bits = v.to_bits();
    #[allow(clippy::cast_possible_truncation)] // the 11-bit exponent field
    let biased = (bits >> 52) as i32;
    ((bits & FRACTION) | (1 << 52), biased - 1075)
}

/// §4, steps 1–4: `P ≈ ln(1 + z)` for the double-word `z = z_hi + z_lo`,
/// `|z| ≤ 0.0078126`, within `3·2^−66` (certified: `formal/ln/tail.g`,
/// `formal/ln/p.g`).
fn ln_1p_double_word(z: DoubleWord) -> DoubleWord {
    let (z_hi, z_lo) = (z.hi(), z.lo());
    let [c3, c4, c5, c6, c7, c8, c9] = POLY;
    let w8 = c8 + z_hi * c9;
    let w7 = c7 + z_hi * w8;
    let w6 = c6 + z_hi * w7;
    let w5 = c5 + z_hi * w6;
    let w4 = c4 + z_hi * w5;
    let w = c3 + z_hi * w4;
    // z_hi² = s_hi + s_lo exactly; s_hi = RN(z_hi²).
    let (s_hi, s_lo) = two_prod(z_hi, z_hi);
    let t = (z_hi * s_hi) * w;
    // −z_hi²/2: halving is exact, and the pair stays a double-word.
    let b = DoubleWord::sum(-0.5 * s_hi, -0.5 * s_lo);
    let v = t - z_hi * z_lo;
    z.add(b).add_f64(v)
}

/// `G_1 = 1 − z·(1/2 − z·(1/3 − …))` to degree `DEGREE` in `Q128`, so that
/// `ln(1 + z) ≈ z·G_1` (§6, step 2; the levels certified in
/// `formal/ln/accurate_level_*.g`).
fn series(z: Q128) -> Q128 {
    let mut g = reciprocal(DEGREE);
    for k in (1..DEGREE).rev() {
        g = reciprocal(k).add(z.mul(g).neg());
    }
    g
}

/// `1/k` as a `Q128` constant (generated), `1 ≤ k ≤ DEGREE`.
fn reciprocal(k: usize) -> Q128 {
    let (m, e) = RECIPROCALS[k - 1];
    Q128::new(false, m, e)
}

/// §5: `y_hi` when the rounding test proves it is `RN` of the value `Y`
/// approximates within `ε₁ = 2^−63`.
pub(crate) fn decide(y: DoubleWord) -> Option<f64> {
    decide_with(y, EPS)
}

/// §5's rounding test with `eps = ε₁·(1 + 2^−50)` for any certified `ε₁`:
/// `y_hi` when it is provably `RN` of the value `Y` approximates within `ε₁`.
/// Shared with `expm1`.
pub(crate) fn decide_with(y: DoubleWord, eps: f64) -> Option<f64> {
    let (y_hi, y_lo) = (y.hi(), y.lo());
    let magnitude = y_hi.abs();
    // The smaller of the gaps on either side of y_hi: toward zero at a power
    // of two.
    let g = if magnitude.to_bits() & FRACTION == 0 {
        ulp(magnitude) * 0.5
    } else {
        ulp(magnitude)
    };
    (y_lo.abs() + eps * magnitude < g * 0.5).then_some(y_hi)
}

#[cfg(test)]
mod tests;
