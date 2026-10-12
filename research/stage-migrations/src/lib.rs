//! Standalone candidates for #126, #127 and #128. No library entry point uses
//! these functions. The trial error budgets below are NOT certified bounds;
//! agreement on a corpus is evidence for investigation, not a rounding proof.
//!
//! All coefficients and tables are the repository's generated constants,
//! imported directly so the experiment cannot drift to an untracked copy.
//! No platform transcendental, FMA, new table, or external implementation.

use morphiq_numerics::{eft, elementary};

// Each generated module includes constants used only by the production
// algorithm. This experiment imports a subset; remove this exception when
// promoting a shared table API into the library.
#[allow(dead_code)]
#[path = "../../../crates/morphiq-numerics/src/exp/tables.rs"]
mod exp_table;
#[allow(dead_code)]
#[path = "../../../crates/morphiq-numerics/src/ln/stage_tables.rs"]
mod log_table;
#[allow(dead_code)]
#[path = "../../../crates/morphiq-numerics/src/exp2/tables.rs"]
mod radix_table;

/// A candidate's outcome, separate from its fallback. Instrumentation runs
/// outside the timed loop, so deciding rates do not perturb measurements.
#[derive(Clone, Copy, Debug)]
pub enum Trial {
    /// A stage proposes a value (pending certification).
    Decided(f64, u8),
    /// The argument is outside the experimental domain.
    Screened,
    /// The trial interval crosses a rounding boundary.
    Undecided,
}

const fn p2(e: i32) -> f64 {
    f64::from_bits(((1023 + e) as u64) << 52)
}

#[inline(always)]
fn test(hi: f64, lo: f64, eps: f64) -> Option<f64> {
    let lb = hi + (lo - eps);
    let ub = hi + (lo + eps);
    (lb == ub).then_some(lb)
}

/// Direct `ln` reduction over positive finite inputs, including subnormals.
/// Unlike ln_1p H, it normalizes `x` before multiplying by a reciprocal and
/// evaluates E*ln(2) instead of indexing the limited-range EL table.
#[inline]
pub fn ln_trial(x: f64) -> Trial {
    if !(x > 0.0 && x < f64::INFINITY) || x == 1.0 {
        return Trial::Screened;
    }
    let (b, correction) = if x < f64::MIN_POSITIVE {
        ((x * p2(54)).to_bits(), 54)
    } else {
        (x.to_bits(), 0)
    };
    let u = b.wrapping_sub(log_table::OFF);
    let e0 = (u as i64) >> 52;
    let i = ((u >> 43) & 511) as usize;
    let y = f64::from_bits(b.wrapping_sub((e0 as u64) << 52));
    let r = f64::from_bits(log_table::R[i]);
    let yh = f64::from_bits(y.to_bits() & !0x3ff);
    let yl = y - yh;
    // The same 10-bit split and reciprocal grid as ln_1p: z is exact.
    let z = (yh * r - 1.0) + yl * r;
    let e = (e0 - correction) as f64;
    let (th, tl) = log_table::T[i];
    let ln1 = e * log_table::L1 + th;
    let ln0 = e * log_table::L0 + tl;
    let z2 = z * z;
    let [h3, h4, h5, h6] = log_table::H;
    let t0 = z * h3 - 0.5;
    let t1 = z * h5 + h4;
    let a1 = z2 * h6 + t1;
    let q = z2 * (z2 * a1 + t0);
    let s = ln1 + z;
    let e1 = z - (s - ln1);
    let lo = (e1 + ln0) + q;
    // Trial budget: H's polynomial term, a widened E*ln(2) term, and an
    // absolute floor. Full-exponent certification is required before use.
    let eps = z2 * p2(-49) + (s.abs() * p2(-80) + p2(-100));
    match test(s, lo, eps) {
        Some(v) => Trial::Decided(v, 1),
        None => Trial::Undecided,
    }
}

#[inline]
pub fn ln(x: f64) -> f64 {
    match ln_trial(x) {
        Trial::Decided(v, _) => v,
        _ => elementary::ln(x),
    }
}

#[inline(always)]
fn table(j: usize) -> (f64, f64) {
    let (h, l) = exp_table::S_T[j];
    (f64::from_bits(h), f64::from_bits(l))
}

#[inline(always)]
fn q(r: f64) -> f64 {
    let [d3, d4, d5] = exp_table::POLY_S;
    (r * r) * (0.5 + r * (d3 + r * (d4 + r * d5)))
}

#[inline(always)]
fn a_value(j: usize, r: f64) -> (f64, f64) {
    let (th, tl) = table(j);
    (th, tl + th * (r + q(r)))
}

#[inline(always)]
fn b_value(j: usize, rh: f64, rt: f64) -> (f64, f64) {
    let r = rh + rt;
    let (th, tl) = table(j);
    let a = f64::from_bits(th.to_bits() & !((1 << 32) - 1));
    let rest = tl + (tl * r + ((th - a) * rh + th * (rt + q(r))));
    let (y, e) = eft::fast_two_sum(th, a * rh);
    (y, e + rest)
}

#[inline(always)]
fn scaled(v: f64, k: i64) -> f64 {
    // The screens keep the accepted result and this power-of-two scaling
    // normal. Multiplication also handles expm1's negative values.
    v * p2(k as i32)
}

/// exp2 with exact dyadic reduction, followed by two exponential stages.
/// Subnormal outputs and overflow remain on the production algorithm.
#[inline]
pub fn exp2_trial(x: f64) -> Trial {
    if x.to_bits() & !(1 << 63) >= 1016.0f64.to_bits() {
        return Trial::Screened;
    }
    let t = x * 512.0 + exp_table::SHIFTER;
    let n = t - exp_table::SHIFTER;
    let ni = t.to_bits() as i64 - exp_table::SHIFTER.to_bits() as i64;
    let j = (ni & 511) as usize;
    let k = ni >> 9;
    let d = x - n * (1.0 / 512.0);
    let r = d * radix_table::LN2_HI;
    let (h, l) = a_value(j, r);
    // Trial bound includes rounding ln(2) before multiplying d.
    if let Some(v) = test(h, l, p2(-59)) {
        return Trial::Decided(scaled(v, k), 1);
    }
    let (rh0, rl0) = eft::two_prod(d, radix_table::LN2_HI);
    let rl = rl0 + d * radix_table::LN2_LO;
    let rh = (rh0 + 6144.0) - 6144.0;
    let rt = (rh0 - rh) + rl;
    let (h, l) = b_value(j, rh, rt);
    match test(h, l, p2(-68)) {
        Some(v) => Trial::Decided(scaled(v, k), 2),
        None => Trial::Undecided,
    }
}

#[inline]
pub fn exp2(x: f64) -> f64 {
    match exp2_trial(x) {
        Trial::Decided(v, _) => v,
        _ => elementary::exp2(x),
    }
}

/// Subtract before rounding and scaling; never subtract from rounded exp(x).
#[inline(always)]
fn minus_one(h: f64, l: f64, eps: f64, k: i64) -> Option<f64> {
    let (s, e) = eft::two_sum(h, -p2(-k as i32));
    let lo = e + l;
    // Trial allowance for folding the subtraction residual into l, and for
    // the interval test's own rounding. It must be certified with the screen.
    let budget = eps + (e.abs() + l.abs()) * p2(-51);
    test(s, lo, budget).map(|v| scaled(v, k))
}

/// General expm1 only: its small/cancellation-sensitive path is unchanged.
#[inline]
pub fn expm1_trial(x: f64) -> Trial {
    if !(x > -37.0 && x < 704.0 && x.abs() >= p2(-5)) {
        return Trial::Screened;
    }
    let t = x * exp_table::INV_N + exp_table::SHIFTER;
    let n = t - exp_table::SHIFTER;
    let ni = t.to_bits() as i64 - exp_table::SHIFTER.to_bits() as i64;
    let j = (ni & 511) as usize;
    let k = ni >> 9;
    let r1 = x - n * exp_table::S_L1;
    let r = r1 - n * exp_table::S_L2D;
    let (h, l) = a_value(j, r);
    if let Some(v) = minus_one(h, l, p2(-59), k) {
        return Trial::Decided(v, 1);
    }
    let p2n = n * exp_table::S_L2;
    let r0 = r1 - p2n;
    let rh = (r0 + 6144.0) - 6144.0;
    let rt = ((r1 - rh) - p2n) - n * exp_table::S_L3;
    let (h, l) = b_value(j, rh, rt);
    match minus_one(h, l, p2(-68), k) {
        Some(v) => Trial::Decided(v, 2),
        None => Trial::Undecided,
    }
}

#[inline]
pub fn expm1(x: f64) -> f64 {
    match expm1_trial(x) {
        Trial::Decided(v, _) => v,
        _ => elementary::expm1(x),
    }
}
