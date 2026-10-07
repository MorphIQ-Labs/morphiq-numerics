//! `log_sum_exp` and `log_diff_exp`: logarithms of sums and differences of
//! exponentials, without leaving log space.
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

/// `T = RN(−ln 2)`, the boundary between `log_diff_exp`'s regions (decision 6).
const T: f64 = f64::from_bits(0xbfe6_2e42_fefa_39ef);

/// `ln Σᵢ e^(xᵢ)`, within `u·|y| + (3 + 2^−8)·u·L + (2k + 1)·2^−1074` of the
/// exact value `y` for up to `2^20 + 1` finite elements, where
/// `L = y − max(x) ∈ [0, ln n]` and `k + 1` elements are finite (§4).
///
/// `−∞` elements are zero mass and contribute nothing. The first NaN element
/// is returned unchanged. Otherwise any `+∞` gives `+∞`, and an empty slice or
/// one holding only `−∞` gives `−∞`. A single finite element, among any `−∞`,
/// is returned exactly, `−0` included. A finite element is never treated as
/// zero mass: `log_sum_exp(&[-800.0])` is `−800` (§1, §7).
#[must_use]
pub fn log_sum_exp(x: &[f64]) -> f64 {
    // §3 step 1: classify, and find m = max and the first index j attaining it.
    let mut positive_infinity = false;
    let mut m = f64::NEG_INFINITY;
    let mut j = usize::MAX;
    for (i, &v) in x.iter().enumerate() {
        if v.is_nan() {
            return v;
        }
        if v == f64::INFINITY {
            positive_infinity = true;
        } else if v > m {
            m = v;
            j = i;
        }
    }
    if positive_infinity {
        return f64::INFINITY;
    }
    if j == usize::MAX {
        return f64::NEG_INFINITY;
    }

    // Steps 2–4: each other finite term e^(xᵢ − m) as the summands
    // exp(dh) and RN(exp(dh)·dl), summed by streaming Sum2 (decision 4).
    let mut pi = 0.0;
    let mut sigma = 0.0;
    for (i, &v) in x.iter().enumerate() {
        if i == j || v == f64::NEG_INFINITY {
            continue;
        }
        // Decision 3: exact as dh + dl wherever exp(dh) ≠ 0, operands
        // beyond 2^1020 included; elsewhere dl may be NaN and is not used.
        let (dh, dl) = two_sum(v, -m);
        let eh = exp(dh);
        if eh == 0.0 {
            continue;
        }
        for term in [eh, eh * dl] {
            let (s, q) = two_sum(pi, term);
            pi = s;
            sigma += q;
        }
    }
    let t = pi + sigma;

    // Step 5.
    if t == 0.0 {
        return m;
    }
    m + ln_1p(t)
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
