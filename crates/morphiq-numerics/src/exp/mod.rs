//! `exp`: `e^x` rounded to nearest, ties to even.
//!
//! The derivation, every bound and the certificates are in
//! [`docs/exp.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md);
//! section numbers below refer to it.

pub(crate) mod bounded;
mod bounded_tables;
#[cfg(feature = "simd")]
pub(crate) mod lanes;
pub(crate) mod tables;

use crate::double_word::DoubleWord;
use crate::eft::{fast_two_sum, two_prod, two_sum};
use crate::q128::Q128;
use crate::ulp::ulp;
use tables::{
    INV_L, INV_N, L1, L2, L3, L4, POLY, POLY_S, RECIPROCALS, S_L1, S_L2, S_L2D, S_L3, S_T, SHIFTER,
    T_BITS, T_Q128,
};

/// The least `x` whose exponential rounds to `+∞` (§1; the reference
/// fixture's threshold "least x overflowing").
const X_OVERFLOW: f64 = f64::from_bits(0x4086_2e42_fefa_39f0);
/// The greatest `x` whose exponential rounds to `+0` (§1; "largest x rounding
/// to 0").
const X_ZERO: f64 = f64::from_bits(0xc087_4910_d52d_3052);
/// `−2^−54` and `2^−53`: between them `e^x` rounds to 1 (§1).
const ONE_LOW: f64 = f64::from_bits(0xbc90_0000_0000_0000);
const ONE_HIGH: f64 = f64::from_bits(0x3ca0_0000_0000_0000);
/// `2^−30`: below it the accurate path takes its small-argument form (§8.4).
const SMALL: f64 = f64::from_bits(0x3e10_0000_0000_0000);
/// The fallback's rounding test: `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−69` (§8.3).
const EPS: f64 = f64::from_bits(0x3ba0_0000_0000_0004);
/// The binary64 fraction field.
const FRACTION: u64 = (1 << 52) - 1;
/// `704`'s encoding: below it in magnitude, the stages run (§3).
const STAGES: u64 = 0x4086_0000_0000_0000;
/// Every bit but the sign.
const MAGNITUDE: u64 = !(1 << 63);
/// `1.5·2^12`: adding and subtracting it rounds to the nearest multiple of
/// `2^−40` (§6).
const SPLIT: f64 = f64::from_bits(0x40b8_0000_0000_0000);
/// Clears the low 32 bits of the fraction field, keeping 21 significant bits
/// (§6).
const HIGH_21: u64 = !((1 << 32) - 1);
/// Stage A's error bound with the test's own rounding, `E_A = 1.5·2^−61`
/// (§5, §7).
const E_A: f64 = f64::from_bits(0x3c28_0000_0000_0000);
/// Stage B's error bound with the test's own rounding, `E_B = 2^−70` (§6,
/// §7).
const E_B: f64 = f64::from_bits(0x3b90_0000_0000_0000);

/// `e^x`, correctly rounded: the binary64 number nearest to `e^x`, ties to
/// even, for every binary64 `x`, subnormal results included.
///
/// `exp(NaN)` is NaN, `exp(+∞) = +∞` and `exp(−∞) = +0`.
#[must_use]
pub fn exp(x: f64) -> f64 {
    // |x| < 704, which also excludes NaN and the infinities (§3).
    if x.to_bits() & MAGNITUDE < STAGES {
        let stages = Stages::of(x);
        if let Some(y) = stages.a() {
            return y;
        }
        if let Some(y) = stages.b() {
            return y;
        }
    }
    fallback(x)
}

/// §8: every argument the stages don't decide.
#[cold]
#[inline(never)]
pub(crate) fn fallback(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x >= X_OVERFLOW {
        return f64::INFINITY;
    }
    if x <= X_ZERO {
        return 0.0;
    }
    if (ONE_LOW..ONE_HIGH).contains(&x) {
        return 1.0;
    }
    let reduced = Reduced::of(x);
    if reduced.k >= -1021
        && let Some(y) = reduced.fast()
    {
        return y;
    }
    if x.abs() >= SMALL {
        reduced.accurate()
    } else {
        small(x)
    }
}

/// The stages' reduction (§3): `x = k·ln 2 + j·L + r`, `L = ln 2 / 512`,
/// for `|x| < 704`.
pub(crate) struct Stages {
    /// `n = 512·k + j`, an integer, `|n| ≤ 520,018`.
    n: f64,
    j: usize,
    k: i64,
    /// `r1 = x − n·S_L1`, exact.
    r1: f64,
}

impl Stages {
    /// §3: `n`, read from the shifter's encoding, and `r1`.
    #[inline]
    pub(crate) fn of(x: f64) -> Self {
        let t = x * INV_N + SHIFTER;
        let n = t - SHIFTER;
        // t is in [2^52, 2^53), where its encoding is SHIFTER's plus n.
        #[allow(clippy::cast_possible_wrap)] // both encodings are below 2^63
        let n_int = t.to_bits() as i64 - SHIFTER.to_bits() as i64;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // in [0, 512)
        let j = (n_int & 511) as usize;
        Self {
            n,
            j,
            k: n_int >> 9,
            r1: x - n * S_L1,
        }
    }

    /// The final power-of-two exponent, also used by `expm1`.
    #[inline]
    pub(crate) fn exponent(&self) -> i64 {
        self.k
    }

    /// `(j, k)`, for the internal cross-check.
    #[cfg(test)]
    pub(crate) fn jk(&self) -> (usize, i64) {
        (self.j, self.k)
    }

    /// `[n, r1]`, for the internal cross-check.
    #[cfg(test)]
    pub(crate) fn words(&self) -> [f64; 2] {
        [self.n, self.r1]
    }

    /// §5 and §7: stage A's `y + l`, scaled by `2^k` when the test proves `y`'s
    /// rounding of it is `RN(e^x / 2^k)`.
    #[inline]
    pub(crate) fn a(&self) -> Option<f64> {
        let (y, l) = self.a_value();
        decide(y, l, E_A, self.k)
    }

    /// §5: `y + l`, within `2^−60.7` of `2^(j/512)·e^r` (certified:
    /// `formal/exp/stage_a.g`).
    #[inline]
    pub(crate) fn a_value(&self) -> (f64, f64) {
        let r = self.r1 - self.n * S_L2D;
        stage_a_at(self.j, r)
    }

    /// §6 and §7: stage B's `y + l`, scaled by `2^k` when the test proves
    /// `y`'s rounding of it is `RN(e^x / 2^k)`.
    #[inline]
    pub(crate) fn b(&self) -> Option<f64> {
        let (y, l) = self.b_value();
        decide(y, l, E_B, self.k)
    }

    /// §6: `y + l`, within `2^−70.2` of `2^(j/512)·e^r` (certified:
    /// `formal/exp/stage_b.g`).
    #[inline]
    pub(crate) fn b_value(&self) -> (f64, f64) {
        // n·S_L2 is exact; r_h is r0 rounded to a multiple of 2^-40, and
        // r1 − r_h − n·S_L2 is exact.
        let p2 = self.n * S_L2;
        let r0 = self.r1 - p2;
        let r_h = (r0 + SPLIT) - SPLIT;
        let r_t = ((self.r1 - r_h) - p2) - self.n * S_L3;
        stage_b_at(self.j, r_h, r_t)
    }
}

/// Stage A at a double-word argument `s + se` (§5a): `(y, l, k)` with `y + l`
/// within `0x1.7p−61` of `2^(j/512)·e^R`, `R = s + se − (512k + j)·L`, for
/// `|s| < 704` and `|se| ≤ 2^−42` (certified: `formal/exp/stage_a_dw.g`).
/// The low word joins stage A's reduced argument with one more rounding.
#[inline]
pub(crate) fn stage_a_double_word(s: f64, se: f64) -> (f64, f64, i64) {
    let Stages { n, j, k, r1 } = Stages::of(s);
    let r = (r1 - n * S_L2D) + se;
    let (y, l) = stage_a_at(j, r);
    (y, l, k)
}

/// Shared exponential stage A after the caller's proved reduction.
#[inline]
pub(crate) fn stage_a_at(j: usize, r: f64) -> (f64, f64) {
    let [d3, d4, d5] = POLY_S;
    let u = r + (r * r) * (0.5 + r * (d3 + r * (d4 + r * d5)));
    let (th, tl) = table(j);
    (th, tl + th * u)
}

/// Shared exponential stage B: `r_h` is on the `2^-40` grid and the
/// caller supplies the proved residual `r_t`.
#[inline]
pub(crate) fn stage_b_at(j: usize, r_h: f64, r_t: f64) -> (f64, f64) {
    let r_hi = r_h + r_t;
    let [d3, d4, d5] = POLY_S;
    let q = (r_hi * r_hi) * (0.5 + r_hi * (d3 + r_hi * (d4 + r_hi * d5)));
    let (th, tl) = table(j);
    // a: th's leading 21 bits, so a·r_h and th − a are exact.
    let a = f64::from_bits(th.to_bits() & HIGH_21);
    let rest = tl + (tl * r_hi + ((th - a) * r_h + th * (r_t + q)));
    let (y, e) = fast_two_sum(th, a * r_h);
    (y, e + rest)
}

/// The library's fast `exp` kernel at the double-word argument `s + se`:
/// `(Y, k)` with `exp(s + se) ≈ Y·2^k` (`docs/exp.md` §3–§4; the low word
/// joins the reduction's `rr`). For `|s| < 710` and `|se| <= 2^-44`,
/// the normalized mantissa error is at most `209 * 2^-78`, proved by
/// `ErfcxReflectionExp.reflection_exp_ieee`. Scaling is left to the caller.
#[inline]
pub(crate) fn stage_b_double_word(s: f64, se: f64) -> (f64, f64, i32) {
    // Stage B at an exact double-word square. The low input word joins
    // the residual before the shared polynomial and table reconstruction.
    // The reduction is the stages' own (§3), as the proof's `stage_of` models.
    let Stages { n, j, k, r1 } = Stages::of(s);
    let p2 = n * S_L2;
    let r0 = r1 - p2;
    let rh = (r0 + 6144.0) - 6144.0;
    let rt = (((r1 - rh) - p2) - n * S_L3) + se;
    let (yh, yl) = stage_b_at(j, rh, rt);
    let (yh, yl) = fast_two_sum(yh, yl);
    #[allow(clippy::cast_possible_truncation)] // |k| <= 1025 for |s| < 710
    (yh, yl, k as i32)
}

/// `2^(j/512)` as a double-word `(hi, lo)`.
#[inline]
fn table(j: usize) -> (f64, f64) {
    let (hi, lo) = S_T[j];
    (f64::from_bits(hi), f64::from_bits(lo))
}

/// §7: `RN(y + RN(l − e))·2^k` when it equals `RN(y + RN(l + e))`, for
/// `|y + l − Z| ≤ ε` with `e` at least `ε` plus the test's own rounding;
/// `y + l` near `[1, 2]` and `|k| ≤ 1016`, so the scaling, on the exponent
/// field, is exact.
#[inline]
pub(crate) fn decide(y: f64, l: f64, e: f64, k: i64) -> Option<f64> {
    let low = y + (l - e);
    let high = y + (l + e);
    #[allow(clippy::cast_sign_loss)] // two's complement: adds k to the exponent
    let scale = (k << 52) as u64;
    #[allow(clippy::float_cmp)] // the test is the equality of two roundings
    let decided = low == high;
    decided.then(|| f64::from_bits(low.to_bits().wrapping_add(scale)))
}

/// The reduction of §8.1: `x = k·ln 2 + j·L + r`, `L = ln 2 / 128`.
pub(crate) struct Reduced {
    /// `n = 128·k + j`, an integer, `|n| < 2^18`.
    n: f64,
    j: usize,
    pub(crate) k: i32,
    /// `r1 = x − n·L1`, exact.
    r1: f64,
    /// `n·L2 = p2 + e2`, exactly.
    p2: f64,
    e2: f64,
    /// `r` as the double-word `(r_hi, r_lo)`, within `2^−113` of `x − n·L`.
    r: DoubleWord,
}

impl Reduced {
    /// `[n, r1, p2, e2, r_hi, r_lo]`, for the internal cross-check.
    #[cfg(test)]
    pub(crate) fn words(&self) -> [f64; 6] {
        [self.n, self.r1, self.p2, self.e2, self.r.hi(), self.r.lo()]
    }

    /// `(j, k)`, for the internal cross-check.
    #[cfg(test)]
    pub(crate) fn jk(&self) -> (usize, i32) {
        (self.j, self.k)
    }

    /// §8.1, steps 1–4.
    pub(crate) fn of(x: f64) -> Self {
        let n = (x * INV_L + SHIFTER) - SHIFTER;
        // |n| < 2^18 (§8.1, step 2), so the conversion is exact.
        #[allow(clippy::cast_possible_truncation)]
        let n_int = n as i32;
        #[allow(clippy::cast_sign_loss)] // rem_euclid is in [0, 128)
        let j = n_int.rem_euclid(128) as usize;
        let k = n_int.div_euclid(128);
        let r1 = x - n * L1;
        let (p2, e2) = two_prod(n, L2);
        let (s, t) = two_sum(r1, -p2);
        let rr = (t - e2) - n * L3;
        Self {
            n,
            j,
            k,
            r1,
            p2,
            e2,
            r: DoubleWord::sum(s, rr),
        }
    }

    /// §8.2 and §8.3: `Y ≈ 2^(j/128)·e^r` in double-word arithmetic, returned
    /// scaled by `2^k` when the rounding test proves `y_hi` is correctly
    /// rounded. Only for `k ≥ −1021`, where the result is normal (§8.2,
    /// decision 3).
    fn fast(&self) -> Option<f64> {
        decide_scaled(self.fast_value(), self.k)
    }

    /// §8.2: `Y`, within `ε₁ = 2^−69` of `2^(j/128)·e^r` (certified:
    /// `formal/exp/fast.g`).
    pub(crate) fn fast_value(&self) -> DoubleWord {
        fast_at(self.r, self.j)
    }

    /// §8.4, general case, rounded once.
    fn accurate(&self) -> f64 {
        self.accurate_value().to_f64()
    }

    /// §8.4, general case: `e^x` from the reduction, the series to degree 12
    /// and the product with `2^(j/128)` in `Q128`, within `2^−123.9`.
    pub(crate) fn accurate_value(&self) -> Q128 {
        let (p3, e3) = two_prod(self.n, L3);
        let r = [-self.p2, -self.e2, -p3, -e3, -(self.n * L4)]
            .into_iter()
            .fold(Q128::from_f64(self.r1), |sum, term| {
                sum.add(Q128::from_f64(term))
            });
        accurate_at(r, self.j, self.k)
    }
}

/// §8.2 at a reduced argument: `Y ≈ 2^(j/128)·e^r` for the double-word `r`,
/// `|r_hi| ≤ 0.0027077`, `|r_lo| ≤ 2^−62`, within `ε₁ = 2^−69` of
/// `2^(j/128)·e^R` when `r` is within `2^−113` of `R` (`formal/exp/fast.g`).
/// Shared with `exp2`.
pub(crate) fn fast_at(r: DoubleWord, j: usize) -> DoubleWord {
    let r_hi = r.hi();
    let [c3, c4, c5, c6] = POLY;
    let t5 = c5 + r_hi * c6;
    let t4 = c4 + r_hi * t5;
    let t3 = c3 + r_hi * t4;
    let h = 0.5 + r_hi * t3;
    let q = (r_hi * r_hi) * h;
    let p = r.add_f64(q);
    let e = DoubleWord::from_f64(1.0).add(p);
    let (t_hi, t_lo) = T_BITS[j];
    // An exact table pair: two_sum returns it unchanged.
    let t_j = DoubleWord::sum(f64::from_bits(t_hi), f64::from_bits(t_lo));
    t_j.mul(e)
}

/// §8.3: `y_hi·2^k` when the rounding test proves `y_hi` is `RN` of the value
/// `Y` approximates within `ε₁`, for `Y > 0` and `−1021 ≤ k ≤ 1024`.
pub(crate) fn decide_scaled(y: DoubleWord, k: i32) -> Option<f64> {
    let (y_hi, y_lo) = (y.hi(), y.lo());
    // The smaller of the gaps on either side of y_hi > 0.
    let g = if y_hi.to_bits() & FRACTION == 0 {
        ulp(y_hi) * 0.5
    } else {
        ulp(y_hi)
    };
    (y_lo.abs() + EPS * y_hi < g * 0.5).then(|| scale(y_hi, k))
}

/// §8.4 at a reduced argument: `2^k·2^(j/128)·e^r` in `Q128`, from the series to
/// degree 12 (the levels certified in `formal/exp/accurate_level_*.g`) and the
/// product with the table (`accurate_y.g`), for `|r| ≤ 0.0027078`. Shared with
/// `exp2`.
pub(crate) fn accurate_at(r: Q128, j: usize, k: i32) -> Q128 {
    // H_13 = 1, H_k = 1 + (r·(1/k))·H_(k+1).
    let mut h = Q128::ONE;
    for level in (1..=12).rev() {
        h = Q128::ONE.add(r.mul(reciprocal(level)).mul(h));
    }
    Q128::new(false, T_Q128[j], -127).mul(h).mul_pow2(k)
}

/// `1/k` as a `Q128` constant (generated), `1 ≤ k ≤ 12`.
fn reciprocal(k: usize) -> Q128 {
    let (m, e) = RECIPROCALS[k - 1];
    Q128::new(false, m, e)
}

/// `y·2^k` for `−1021 ≤ k ≤ 1024`, exact for the normal results the fast
/// path returns (§8.3, scaling).
pub(crate) fn scale(y: f64, k: i32) -> f64 {
    if k == 1024 {
        return y * pow2(1023) * 2.0;
    }
    y * pow2(k)
}

/// `2^k` for `−1022 ≤ k ≤ 1023`, from its encoding.
fn pow2(k: i32) -> f64 {
    #[allow(clippy::cast_sign_loss)] // k + 1023 >= 1
    f64::from_bits(((k + 1023) as u64) << 52)
}

/// §8.4, small arguments, `2^−54 ≤ |x| < 2^−30`: `RN(1 + x + d)` with
/// `d = e^x − 1 − x` to degree 5 in `Q128` (certified in `formal/exp/small.g`),
/// the rounding decided exactly.
pub(crate) fn small(x: f64) -> f64 {
    let (h, w) = small_parts(x);
    // RN(h + w): h, unless |w| reaches half the gap on w's side of h, which
    // [LM] keeps it from equalling.
    let up = !w.is_negative();
    let gap = if !up && h.to_bits() & FRACTION == 0 {
        ulp(h) * 0.5
    } else {
        ulp(h)
    };
    if w.cmp_abs(Q128::from_f64(gap * 0.5)) == core::cmp::Ordering::Less {
        h
    } else if up {
        f64::from_bits(h.to_bits() + 1)
    } else {
        f64::from_bits(h.to_bits() - 1)
    }
}

/// `e^x = h + w` within `2^−178` (§8.4, small arguments): `(h, l) = two_sum(1, x)`
/// and `w = l + d`.
pub(crate) fn small_parts(x: f64) -> (f64, Q128) {
    let (h, l) = two_sum(1.0, x);
    let xq = Q128::from_f64(x);
    let g5 = Q128::ONE.add(xq.mul(reciprocal(5)));
    let g4 = Q128::ONE.add(xq.mul(reciprocal(4)).mul(g5));
    let g3 = Q128::ONE.add(xq.mul(reciprocal(3)).mul(g4));
    let d = xq.mul(xq).mul(reciprocal(2)).mul(g3);
    (h, Q128::from_f64(l).add(d))
}

#[cfg(test)]
mod tests;
