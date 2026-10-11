//! `log_sum_exp` and `log_diff_exp`: logarithms of sums and differences of
//! exponentials, without leaving log space; and `log_sum_exp_pairs`,
//! `log_sum_exp` of several pairs at once.
//!
//! The contract, the derivation and every bound are in
//! [`docs/log_space.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/log_space.md);
//! section and decision numbers below refer to it. Neither function is
//! correctly rounded (decision 2); each is within a proved bound
//! `|ŷ − y| ≤ u·|y| + β·u·|L| + η`, and both are identical on every target.

#[cfg(test)]
mod tests;

use crate::eft::two_sum;
use crate::elementary::{exp, expm1, ln, ln_1p};
#[cfg(feature = "simd")]
use crate::elementary::{exp_slice, ln_1p_slice};

/// `T = RN(−ln 2)`, the boundary between `log_diff_exp`'s regions (decision 6).
const T: f64 = f64::from_bits(0xbfe6_2e42_fefa_39ef);

/// How many terms, or pairs, are reduced before their exponentials are
/// evaluated together in lanes (decision 7). Any size gives the same bits.
#[cfg(feature = "simd")]
const CHUNK: usize = 32;

/// `ln Σᵢ e^(xᵢ)`, within `u·|y| + (3 + 2^−8)·u·L + (2k + 1)·2^−1074` of the
/// exact value `y` for up to `2^20 + 1` finite elements, where
/// `L = y − max(x) ∈ [0, ln n]` and `k + 1` elements are finite (§4).
///
/// `−∞` elements are zero mass and contribute nothing. The first NaN element
/// is returned unchanged. Otherwise any `+∞` gives `+∞`, and an empty slice or
/// one holding only `−∞` gives `−∞`. A single finite element, among any `−∞`,
/// is returned exactly, `−0` included. A finite element is never treated as
/// zero mass: `log_sum_exp(&[-800.0])` is `−800` (§1, §7).
///
/// With the `simd` feature the exponentials are evaluated in SIMD lanes,
/// which returns the same bits (decision 7).
#[must_use]
pub fn log_sum_exp(x: &[f64]) -> f64 {
    let (m, j) = match shift(x) {
        Ok(shift) => shift,
        Err(y) => return y,
    };
    let t = terms(x, m, j);
    // Step 5.
    if t == 0.0 {
        return m;
    }
    m + ln_1p(t)
}

/// `log_sum_exp` of each of `N` pairs: element `i` of the result is
/// `log_sum_exp(&x[i])`, bit for bit, on every target and with or without the
/// `simd` feature.
///
/// With the `simd` feature the pairs' exponentials, and then their
/// logarithms, are evaluated together in SIMD lanes (decision 7). Its working
/// storage is a few `[f64; N]` arrays on the stack, so `N` is meant to be
/// small: a recursion's independent pairs at one step.
#[must_use]
pub fn log_sum_exp_pairs<const N: usize>(x: &[[f64; 2]; N]) -> [f64; N] {
    #[cfg(feature = "simd")]
    {
        lane_pairs(x)
    }
    #[cfg(not(feature = "simd"))]
    {
        x.map(|pair| log_sum_exp(&pair))
    }
}

/// §3 step 1: classify, and find `m = max` and the first index `j` attaining
/// it. `Err` holds the result when there is no finite element to shift by,
/// or a NaN or `+∞` decides it.
fn shift(x: &[f64]) -> Result<(f64, usize), f64> {
    let mut positive_infinity = false;
    let mut m = f64::NEG_INFINITY;
    let mut j = usize::MAX;
    for (i, &v) in x.iter().enumerate() {
        if v.is_nan() {
            return Err(v);
        }
        if v == f64::INFINITY {
            positive_infinity = true;
        } else if v > m {
            m = v;
            j = i;
        }
    }
    if positive_infinity {
        return Err(f64::INFINITY);
    }
    if j == usize::MAX {
        return Err(f64::NEG_INFINITY);
    }
    Ok((m, j))
}

/// Steps 3–4's streaming Sum2: a running `two_sum` and a compensation
/// accumulator (decision 4).
#[derive(Default)]
struct Sum2Stream {
    pi: f64,
    sigma: f64,
}

impl Sum2Stream {
    /// One term `e^(dh + dl)` as the summands `eh = exp(dh)` and
    /// `RN(eh·dl)`. A term with `eh = 0` is skipped before `dl`, which may
    /// then be NaN, is used (decision 3).
    fn add(&mut self, eh: f64, dl: f64) {
        if eh == 0.0 {
            return;
        }
        for term in [eh, eh * dl] {
            let (s, q) = two_sum(self.pi, term);
            self.pi = s;
            self.sigma += q;
        }
    }

    fn total(&self) -> f64 {
        self.pi + self.sigma
    }
}

/// Steps 2–4: `t̂`, the sum of every other finite term `e^(xᵢ − m)`, in
/// index order.
fn scalar_terms(x: &[f64], m: f64, j: usize) -> f64 {
    let mut sum = Sum2Stream::default();
    for (i, &v) in x.iter().enumerate() {
        if i == j || v == f64::NEG_INFINITY {
            continue;
        }
        // Decision 3: exact as dh + dl wherever exp(dh) ≠ 0, operands
        // beyond 2^1020 included; elsewhere dl may be NaN and is not used.
        let (dh, dl) = two_sum(v, -m);
        sum.add(exp(dh), dl);
    }
    sum.total()
}

#[cfg(not(feature = "simd"))]
fn terms(x: &[f64], m: f64, j: usize) -> f64 {
    scalar_terms(x, m, j)
}

/// Steps 2–4 as `scalar_terms`, with the exponentials of each chunk of
/// `CHUNK` terms evaluated together by `exp_slice`, which returns `exp`'s
/// bits. Every summand then enters Sum2 in the same order (decision 7). A
/// slice of two holds at most one other term, which gains nothing from
/// lanes, so it takes `scalar_terms` and its same bits.
#[cfg(feature = "simd")]
fn terms(x: &[f64], m: f64, j: usize) -> f64 {
    if x.len() <= 2 {
        return scalar_terms(x, m, j);
    }
    let mut sum = Sum2Stream::default();
    let mut dh = [0.0; CHUNK];
    let mut dl = [0.0; CHUNK];
    let mut eh = [0.0; CHUNK];
    let mut len = 0;
    for (i, &v) in x.iter().enumerate() {
        if i == j || v == f64::NEG_INFINITY {
            continue;
        }
        (dh[len], dl[len]) = two_sum(v, -m);
        len += 1;
        if len == CHUNK {
            exp_slice(&dh, &mut eh);
            for (&eh, &dl) in eh.iter().zip(&dl) {
                sum.add(eh, dl);
            }
            len = 0;
        }
    }
    exp_slice(&dh[..len], &mut eh[..len]);
    for (&eh, &dl) in eh[..len].iter().zip(&dl[..len]) {
        sum.add(eh, dl);
    }
    sum.total()
}

/// `log_sum_exp_pairs` in lanes: each pair's steps 1–4 as `log_sum_exp`
/// takes them, with the pairs' exponentials evaluated together by
/// `exp_slice` and their `ln_1p`s by `ln_1p_slice`, which return the scalar
/// functions' bits (decision 7).
#[cfg(feature = "simd")]
fn lane_pairs<const N: usize>(x: &[[f64; 2]; N]) -> [f64; N] {
    let mut out = [0.0; N];
    let mut m = [0.0; N];
    let mut pending = [false; N];
    // A pair with no other finite term keeps dh = −∞: its exponential is
    // +0, so its term is skipped and t̂ = 0, as in `scalar_terms`.
    let mut dh = [f64::NEG_INFINITY; N];
    let mut dl = [0.0; N];
    for (i, pair) in x.iter().enumerate() {
        match shift(pair) {
            Err(y) => out[i] = y,
            Ok((top, j)) => {
                m[i] = top;
                pending[i] = true;
                let v = pair[1 - j];
                if v != f64::NEG_INFINITY {
                    (dh[i], dl[i]) = two_sum(v, -top);
                }
            }
        }
    }
    let mut eh = [0.0; N];
    exp_slice(&dh, &mut eh);
    let mut t = [0.0; N];
    for i in 0..N {
        let mut sum = Sum2Stream::default();
        sum.add(eh[i], dl[i]);
        t[i] = sum.total();
    }
    let mut l = [0.0; N];
    ln_1p_slice(&t, &mut l);
    for i in 0..N {
        if pending[i] {
            // Step 5.
            out[i] = if t[i] == 0.0 { m[i] } else { m[i] + l[i] };
        }
    }
    out
}

/// `ln(e^a − e^b)` for `a ≥ b`, within `u·|y| + 3.89·u·|L| + 5·2^−1074` of
/// the exact value `y`, where `L = y − a` (§6).
///
/// A NaN argument is returned unchanged, `a`'s first. `b > a` and
/// `a = b = +∞` give NaN: outside the domain. Equal arguments, finite or `−∞`,
/// give `−∞` exactly (zero mass); `b = −∞ < a` gives `a` exactly; and
/// `a = +∞ > b` gives `+∞` (§1, §7).
#[must_use]
pub fn log_diff_exp(a: f64, b: f64) -> f64 {
    if a.is_nan() {
        return a;
    }
    if b.is_nan() {
        return b;
    }
    if a < b {
        return f64::NAN;
    }
    if a == b {
        return if a == f64::INFINITY {
            f64::NAN
        } else {
            f64::NEG_INFINITY
        };
    }
    if b == f64::NEG_INFINITY {
        return a;
    }
    if a == f64::INFINITY {
        return f64::INFINITY;
    }
    // §5: d = b − a < 0 as dh + dl, exact wherever it is used (decision 3).
    let (dh, dl) = two_sum(b, -a);
    let big_l = if dh > T {
        // Region A: L = ln(−expm1(dh)). Dropping dl costs at most u·|L|,
        // no more than the rounding a correction would add (§6).
        ln(-expm1(dh))
    } else {
        // Region B: L = ln(1 − w), w = e^dh·e^dl ≤ 1/2·(1 + O(u)).
        let eh = exp(dh);
        if eh == 0.0 {
            // w < 2^−1075 (and dl may be NaN): y = a within η.
            return a;
        }
        ln_1p(-(eh + eh * dl))
    };
    a + big_l
}
