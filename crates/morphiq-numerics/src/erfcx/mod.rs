//! Scaled complementary error function: table, reciprocal and reflection kernels.
mod accurate;
#[cfg(test)]
pub(crate) use accurate::{asym as accurate_asym, reflected_exponential as accurate_reflected_exp};
mod accurate_tables;
#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod tables;
#[cfg(test)]
pub(crate) mod tests;

use crate::eft::{fast_two_sum, two_prod, two_sum};
use crate::exp::tables::{INV_N, S_L1, S_L2, S_L3, SHIFTER};
use crate::ulp::ulp;
use tables::{CS, DEG, PA, T};

/// The greatest `x` whose erfcx rounds to `+∞` (derived by `thresholds`).
pub(super) const X_OVF: f64 = f64::from_bits(0xc03a_a0f4_d2e0_63cf);
/// `0 ≤ x ≤ ONE_POS` rounds to 1.
pub(super) const ONE_POS: f64 = f64::from_bits(0x3c8c_5bf8_91b4_ef6b);
/// `ONE_NEG ≤ x ≤ 0` rounds to 1.
pub(super) const ONE_NEG: f64 = f64::from_bits(0xbc9c_5bf8_91b4_ef69);
/// `x ≥ X_SUB` has a subnormal result, tested on the final output grid.
pub(super) const X_SUB: f64 = f64::from_bits(0x7fc2_0dd7_5042_9b6e);

/// Rounding-test bounds per region (relative error of the double-word result).
/// Provisional guards; docs/erfcx.md states the current assurance limits.
pub(super) const EPS_T: f64 = f64::from_bits(0x3bd0_0000_0000_0000);
pub(super) const EPS_Y: f64 = f64::from_bits(0x3bd0_0000_0000_0000);
pub(super) const EPS_N: f64 = f64::from_bits(0x3bd0_0000_0000_0000);

const FRACTION: u64 = (1 << 52) - 1;

/// Which region a finite, non-special argument belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Region {
    T,
    YA,
    YB,
    N,
}

pub(super) fn region(x: f64) -> Region {
    if x < -0.5 {
        Region::N
    } else if x < 16.0 {
        Region::T
    } else if x < 512.0 {
        Region::YA
    } else {
        Region::YB
    }
}

#[inline]
fn f(b: u64) -> f64 {
    f64::from_bits(b)
}

/// The scaled complementary error function, `exp(x²) erfc(x)`.
///
/// NaNs retain their payload, positive infinity returns positive zero, and
/// negative infinity returns positive infinity. Finite positive arguments
/// retain a positive result even in the subnormal tail.
///
/// This implementation is under development; see docs/erfcx.md for the
/// current assurance status before making an accuracy claim.
#[must_use]
pub fn erfcx(x: f64) -> f64 {
    if let Some(y) = special(x) {
        return y;
    }
    let fast = match region(x) {
        Region::T => fast_t(x),
        Region::YA => fast_ya(x),
        Region::YB => fast_yb(x),
        Region::N => fast_n(x),
    };
    fast.unwrap_or_else(|| accurate::accurate(x).to_f64())
}

/// NaN, ±∞, overflow and the arguments that round to 1.
#[inline]
pub(super) fn special(x: f64) -> Option<f64> {
    if x.is_nan() {
        return Some(x);
    }
    if x <= X_OVF {
        return Some(f64::INFINITY);
    }
    if x == f64::INFINITY {
        return Some(0.0);
    }
    if (ONE_NEG..=ONE_POS).contains(&x) {
        return Some(1.0);
    }
    None
}

/// The library's rounding test (`ln::decide_with`): `y_hi` when
/// `RN(|y_lo| + RN(eps·|y_hi|)) < g/2`, `g` the gap below `|y_hi|`'s
/// neighbours on the smaller side. Requires `y_hi = RN(y_hi + y_lo)`.
#[inline]
pub(super) fn decide(y_hi: f64, y_lo: f64, eps: f64) -> Option<f64> {
    let a = y_hi.abs();
    let g = if a.to_bits() & FRACTION == 0 {
        ulp(a) * 0.5
    } else {
        ulp(a)
    };
    (y_lo.abs() + eps * a < g * 0.5).then_some(y_hi)
}

fn pow2(k: i32) -> f64 {
    f64::from_bits(((k + 1023) as u64) << 52)
}

/// `RN(Y·2^k)` when the test decides on `Y` (exact scaling, normal results).
#[inline]
fn decide_scaled(y_hi: f64, y_lo: f64, eps: f64, k: i32) -> Option<f64> {
    decide(y_hi, y_lo, eps).map(|y| {
        if k > 1023 {
            y * pow2(k - 1023) * pow2(1023)
        } else if k < -1022 {
            y * pow2(k + 600) * pow2(-600)
        } else {
            y * pow2(k)
        }
    })
}

// ---------------------------------------------------------------- region T

/// Interval index, centre and `h = x − c` (exact) for `−1/2 ≤ x < 16`, and
/// the binade exponent `e` that scales the interval (`hm = 2^(e−6)`).
#[inline]
pub(super) fn t_reduce(x: f64) -> (usize, f64, f64, i32) {
    if x < 1.0 {
        // c = k/32 nearest x; |h| ≤ 1/64.
        let kk = (x * 32.0 + SHIFTER) - SHIFTER;
        let c = kk * (1.0 / 32.0);
        ((kk as i32 + 16) as usize, c, x - c, 0)
    } else {
        let b = x.to_bits();
        let e = ((b >> 52) as i32) - 1023;
        let i = ((b >> 47) & 31) as usize;
        let c = f((b & !((1u64 << 47) - 1)) | (1u64 << 46));
        (49 + 32 * e as usize + i, c, x - c, e)
    }
}

/// Split the reduced argument on the table kernel's exponent-dependent grid.
#[inline]
pub(crate) fn table_split(h: f64, e: i32) -> (f64, f64) {
    let sh = f((((1023 + 29 + e) as u64) << 52) | (1u64 << 51));
    let hi = (h + sh) - sh;
    (hi, h - hi)
}

/// Exact leading products of the table polynomial after splitting its residual.
#[inline]
pub(crate) fn table_leading(idx: usize, h: f64) -> (f64, f64, f64, f64, f64, f64, f64) {
    let a = &T[idx];
    // A1 has 35 significand bits; H has at most 18, so A1·H is exact.
    let a1h = f(a[2]);
    let a1 = f(a[2] & !((1u64 << 18) - 1));
    let b1 = (a1h - a1) + f(a[3]);
    // A2 has 17 significand bits; H² has at most 36, so A2·H² is exact.
    let a2h = f(a[4]);
    let a2 = f(a[4] & !((1u64 << 36) - 1));
    let b2 = (a2h - a2) + f(a[5]);
    let p1 = a1 * h;
    let sq = h * h;
    let p2 = a2 * sq;
    (a1, b1, a2h, b2, p1, sq, p2)
}

/// The double-word polynomial value for region T.
#[inline]
pub(super) fn t_eval(x: f64) -> (f64, f64) {
    let (idx, _c, h, e) = t_reduce(x);
    let a = &T[idx];
    // H: h on the 2^(e−23) grid, so |H| ≤ 2^17 grid steps (≤ 18 bits) and
    // H·H is exact (≤ 36 bits); L = h − H exactly, |L| ≤ 2^(e−24).
    let (hh_, l) = table_split(h, e);
    let (a1, b1, a2h, b2, p1, sq, p2) = table_leading(idx, hh_);
    // Tail: q = a3 + h·(a4 + …), Horner in binary64.
    let mut q = f(a[6 + DEG - 3]);
    for j in (6..6 + DEG - 3).rev() {
        q = f(a[j]) + h * q;
    }
    let lh = l * (h + hh_);
    let h2 = sq + lh;
    let t3 = (h2 * h) * q;
    let rest = f(a[1]) + (a1 * l + b1 * h) + (a2h * lh + b2 * sq) + t3;
    let (s, e1) = fast_two_sum(f(a[0]), p1);
    let (s2, e2) = fast_two_sum(s, p2);
    fast_two_sum(s2, (e1 + e2) + rest)
}

pub(super) fn fast_t(x: f64) -> Option<f64> {
    let (yh, yl) = t_eval(x);
    decide(yh, yl, EPS_T)
}

// ---------------------------------------------------------------- region Y

#[inline]
pub(crate) fn dw_mul(ah: f64, al: f64, bh: f64, bl: f64) -> (f64, f64) {
    let (p, e) = two_prod(ah, bh);
    fast_two_sum(p, e + (ah * bl + al * bh))
}

/// Corrected reciprocal for the middle positive region.
#[inline]
pub(crate) fn reciprocal(x: f64) -> (f64, f64) {
    // y = 1/x as a double-word: 1 − x·yh is exact (Sterbenz, after two_prod).
    let yh = 1.0 / x;
    let (p, pe) = two_prod(x, yh);
    let yl = ((1.0 - p) - pe) * yh;
    (yh, yl)
}

/// Square of the corrected reciprocal, retaining both words.
#[inline]
pub(crate) fn reciprocal_square(x: f64) -> (f64, f64, f64, f64) {
    let (yh, yl) = reciprocal(x);
    // t = y² as a double-word.
    let (th, tl0) = two_prod(yh, yh);
    let tl = tl0 + 2.0 * yh * yl;
    (yh, yl, th, tl)
}

/// Compensated middle-tail correction polynomial, given both square words.
#[inline]
pub(crate) fn middle_correction(th: f64, tl: f64) -> (f64, f64) {
    let mut pp = f(PA[PA.len() - 1]);
    for j in (0..PA.len() - 1).rev() {
        pp = f(PA[j]) + th * pp;
    }
    // W = 1 − t/2 + t²P.
    let (w, ew) = fast_two_sum(1.0, -0.5 * th);
    // t² from both words: th² alone is off by 2·tl/th ≈ 2^−51.5 relative.
    let v = (th * (th + 2.0 * tl)) * pp;
    let (w, e3) = fast_two_sum(w, v);
    let wl = e3 + (ew - 0.5 * tl);
    (w, wl)
}

/// Double-word erfcx for `16 ≤ x < 512`.
#[inline]
pub(crate) fn ya_eval(x: f64) -> (f64, f64) {
    let (yh, yl, th, tl) = reciprocal_square(x);
    let (w, wl) = middle_correction(th, tl);
    let (zh, zl) = dw_mul(f(CS.0), f(CS.1), yh, yl);
    dw_mul(zh, zl, w, wl)
}

pub(super) fn fast_ya(x: f64) -> Option<f64> {
    let (yh, yl) = ya_eval(x);
    decide(yh, yl, EPS_Y)
}

/// Corrected stored-constant quotient for a reduced positive-tail input.
#[inline]
pub(crate) fn quotient(x: f64) -> (f64, f64) {
    let (ch, cl) = (f(CS.0), f(CS.1));
    let q = ch / x;
    let (p, pe) = two_prod(q, x);
    let r = ((ch - p) - pe) + cl;
    let ql = r / x;
    (q, ql)
}

/// Cubic correction in the large positive tail, including gradual underflow.
#[inline]
pub(crate) fn tail_correction(x: f64) -> f64 {
    let y = 1.0 / x;
    let t = y * y;
    t * (-0.5 + t * (0.75 - 1.875 * t))
}

/// Double-word erfcx for finite `x ≥ 512`, as `(hi, lo, k)` with value
/// `(hi + lo)·2^k`.
#[inline]
pub(crate) fn yb_eval(x: f64) -> (f64, f64, i32) {
    let (xs, k) = if x > 1e270 {
        (x * pow2(-600), -600)
    } else {
        (x, 0)
    };
    let (q, ql) = quotient(xs);
    if k != 0 {
        // x > 1e270 implies RN((1/x)^2) = +0. Its polynomial is -0,
        // so the correction contributes nothing to this positive result.
        let (fh, fl) = fast_two_sum(q, ql);
        return (fh, fl, k);
    }
    let u = tail_correction(x);
    let (fh, fl) = fast_two_sum(q, ql + q * u);
    (fh, fl, k)
}

pub(super) fn fast_yb(x: f64) -> Option<f64> {
    let (fh, fl, k) = yb_eval(x);
    if x >= X_SUB {
        // Compare on the final subnormal grid, expressed before the exact
        // 2^-600 scale. This avoids deciding a normal rounding followed by
        // a second, subnormal rounding.
        let mut candidate = fh * pow2(k);
        let half = pow2(-1075 - k);
        let residual = (fh - candidate * pow2(-k)) + fl;
        // When the leading word lands on a subnormal midpoint, its low
        // word may put the value toward the other neighbor. Check that
        // neighbor before resorting to Q256; the same interval test follows.
        if residual > half {
            candidate = f64::from_bits(candidate.to_bits() + 1);
        } else if residual < -half {
            candidate = f64::from_bits(candidate.to_bits() - 1);
        }
        let distance = ((fh - candidate * pow2(-k)) + fl).abs();
        return (distance + EPS_Y * fh < half).then_some(candidate);
    }
    decide_scaled(fh, fl, EPS_Y, k)
}

// ---------------------------------------------------------------- region N

/// The library's fast `exp` kernel at the double-word argument `s + se`:
/// `(Y, k)` with `exp(s + se) ≈ Y·2^k` (`docs/exp.md` §3–§4; the low word
/// joins the reduction's `rr`).
#[inline]
pub(super) fn exp_dw(s: f64, se: f64) -> (f64, f64, i32) {
    // Stage B at an exact double-word square. The low input word joins
    // the residual before the shared polynomial and table reconstruction.
    let t = s * INV_N + SHIFTER;
    let n = t - SHIFTER;
    let ni = n as i32;
    let j = ni.rem_euclid(512) as usize;
    let k = ni.div_euclid(512);
    let r1 = s - n * S_L1;
    let p2 = n * S_L2;
    let r0 = r1 - p2;
    let rh = (r0 + 6144.0) - 6144.0;
    let rt = (((r1 - rh) - p2) - n * S_L3) + se;
    let (yh, yl) = crate::exp::stage_b_at(j, rh, rt);
    let (yh, yl) = fast_two_sum(yh, yl);
    (yh, yl, k)
}

/// Double-word erfcx for `X_OVF < x < −1/2`, as `(hi, lo, k)`.
#[inline]
pub(super) fn n_eval(x: f64) -> (f64, f64, i32) {
    let (s, se) = two_prod(x, x);
    let (yh, yl, k) = exp_dw(s, se);
    // 2·E − g = 2^(k+1)·(Y − g·2^−(k+1)); g/(2E) < 2^−105 once k > 104.
    if k > 104 {
        return (yh, yl, k + 1);
    }
    // k <= 104 places |x| below 9, entirely inside the table region.
    let (gh, gl) = t_eval(-x);
    let sc = pow2(-(k + 1));
    let (dh, dl) = two_sum(yh, -gh * sc);
    let (fh, fl) = fast_two_sum(dh, dl + (yl - gl * sc));
    (fh, fl, k + 1)
}

pub(super) fn fast_n(x: f64) -> Option<f64> {
    let (fh, fl, k) = n_eval(x);
    decide_scaled(fh, fl, EPS_N, k)
}

/// The fast double-word value and its scale for any non-special argument
/// (for the error measurements): `(hi, lo, k)`, value `(hi + lo)·2^k`.
#[cfg(test)]
pub(super) fn fast_value(x: f64) -> (f64, f64, i32) {
    match region(x) {
        Region::T => {
            let (h, l) = t_eval(x);
            (h, l, 0)
        }
        Region::YA => {
            let (h, l) = ya_eval(x);
            (h, l, 0)
        }
        Region::YB => yb_eval(x),
        Region::N => n_eval(x),
    }
}
