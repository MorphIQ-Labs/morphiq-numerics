//! `exp`: `e^x` rounded to nearest, ties to even.
//!
//! The derivation, every bound and the certificates are in
//! [`docs/exp.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md);
//! section numbers below refer to it.

mod tables;

use crate::double_word::DoubleWord;
use crate::eft::{two_prod, two_sum};
use crate::q128::Q128;
use crate::ulp::ulp;
use tables::{INV_L, L1, L2, L3, L4, POLY, RECIPROCALS, SHIFTER, T_BITS, T_Q128};

/// The least `x` whose exponential rounds to `+∞` (§1; the reference
/// fixture's threshold "least x overflowing").
const X_OVERFLOW: f64 = f64::from_bits(0x4086_2e42_fefa_39f0);
/// The greatest `x` whose exponential rounds to `+0` (§1; "largest x rounding
/// to 0").
const X_ZERO: f64 = f64::from_bits(0xc087_4910_d52d_3052);
/// `−2^−54` and `2^−53`: between them `e^x` rounds to 1 (§1).
const ONE_LOW: f64 = f64::from_bits(0xbc90_0000_0000_0000);
const ONE_HIGH: f64 = f64::from_bits(0x3ca0_0000_0000_0000);
/// `2^−30`: below it the accurate path takes its small-argument form (§6).
const SMALL: f64 = f64::from_bits(0x3e10_0000_0000_0000);
/// The rounding test's `EPS = ε₁·(1 + 2^−50)`, `ε₁ = 2^−69` (§5).
const EPS: f64 = f64::from_bits(0x3ba0_0000_0000_0004);
/// The binary64 fraction field.
const FRACTION: u64 = (1 << 52) - 1;

/// `e^x`, correctly rounded: the binary64 number nearest to `e^x`, ties to
/// even, for every binary64 `x`, subnormal results included.
///
/// `exp(NaN)` is NaN, `exp(+∞) = +∞` and `exp(−∞) = +0`.
#[must_use]
pub fn exp(x: f64) -> f64 {
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

/// The reduction of §3: `x = k·ln 2 + j·L + r`, `L = ln 2 / 128`.
struct Reduced {
    /// `n = 128·k + j`, an integer, `|n| < 2^18`.
    n: f64,
    j: usize,
    k: i32,
    /// `r1 = x − n·L1`, exact.
    r1: f64,
    /// `n·L2 = p2 + e2`, exactly.
    p2: f64,
    e2: f64,
    /// `r` as the double-word `(r_hi, r_lo)`, within `2^−113` of `x − n·L`.
    r: DoubleWord,
}

impl Reduced {
    /// §3, steps 1–4.
    fn of(x: f64) -> Self {
        let n = (x * INV_L + SHIFTER) - SHIFTER;
        // |n| < 2^18 (§3, step 2), so the conversion is exact.
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

    /// §4 and §5: `Y ≈ 2^(j/128)·e^r` in double-word arithmetic, returned
    /// scaled by `2^k` when the rounding test proves `y_hi` is correctly
    /// rounded. Only for `k ≥ −1021`, where the result is normal (§4,
    /// decision 3).
    fn fast(&self) -> Option<f64> {
        decide_scaled(self.fast_value(), self.k)
    }

    /// §4: `Y`, within `ε₁ = 2^−69` of `2^(j/128)·e^r` (certified:
    /// `formal/exp/fast.g`).
    fn fast_value(&self) -> DoubleWord {
        fast_at(self.r, self.j)
    }

    /// §6, general case, rounded once.
    fn accurate(&self) -> f64 {
        self.accurate_value().to_f64()
    }

    /// §6, general case: `e^x` from the reduction, the series to degree 12
    /// and the product with `2^(j/128)` in `Q128`, within `2^−123.9`.
    fn accurate_value(&self) -> Q128 {
        let (p3, e3) = two_prod(self.n, L3);
        let r = [-self.p2, -self.e2, -p3, -e3, -(self.n * L4)]
            .into_iter()
            .fold(Q128::from_f64(self.r1), |sum, term| {
                sum.add(Q128::from_f64(term))
            });
        accurate_at(r, self.j, self.k)
    }
}

/// §4 at a reduced argument: `Y ≈ 2^(j/128)·e^r` for the double-word `r`,
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

/// §5: `y_hi·2^k` when the rounding test proves `y_hi` is `RN` of the value
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

/// §6 at a reduced argument: `2^k·2^(j/128)·e^r` in `Q128`, from the series to
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
/// path returns (§5, scaling).
fn scale(y: f64, k: i32) -> f64 {
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

/// §6, small arguments, `2^−54 ≤ |x| < 2^−30`: `RN(1 + x + d)` with
/// `d = e^x − 1 − x` to degree 5 in `Q128` (certified in `formal/exp/small.g`),
/// the rounding decided exactly.
fn small(x: f64) -> f64 {
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

/// `e^x = h + w` within `2^−178` (§6, small arguments): `(h, l) = two_sum(1, x)`
/// and `w = l + d`.
fn small_parts(x: f64) -> (f64, Q128) {
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
