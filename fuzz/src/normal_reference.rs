//! Independent normal-family enclosures using black-box MPFR operations.
//! The positive erfcx tail uses the signed integral remainder in DLMF 7.12.1,
//! not any coefficients, arithmetic or dispatch from the library under test.
use rug::{
    Float,
    float::{Constant, Round},
};

/// Enclose exp(x*x) erfc(x) for an exact MPFR argument, -32 <= x.
pub(super) fn erfcx(x: &Float) -> (Float, Float) {
    assert!(x.is_finite() && x >= &-32);
    let p = x.prec();
    if x >= &64 {
        return erfcx_tail(x);
    }
    // x can itself be a rounded endpoint of a composition. Its square need
    // not fit p bits, so even this multiplication must round outwards.
    let mut exp_lo = Float::with_val_round(p, x * x, Round::Down).0;
    let mut exp_hi = Float::with_val_round(p, x * x, Round::Up).0;
    exp_lo.exp_round(Round::Down);
    exp_hi.exp_round(Round::Up);
    let mut erfc_lo = x.clone();
    let mut erfc_hi = x.clone();
    erfc_lo.erfc_round(Round::Down);
    erfc_hi.erfc_round(Round::Up);
    (
        Float::with_val_round(p, &exp_lo * &erfc_lo, Round::Down).0,
        Float::with_val_round(p, &exp_hi * &erfc_hi, Round::Up).0,
    )
}

/// For x > 0, erfcx(x) = J/(x sqrt(pi)), where
/// J = integral_0^infinity exp(-u) exp(-u²/(4x²)) du.
/// Integrating Taylor's signed remainder brackets J by its odd and even
/// truncations: sum_{k=0}^n (-1)^k (2k-1)!!/(2x²)^k.
/// Use n=63 below and n=64 above. At x>=64 the first omitted term is <2^-470;
/// the actual term enclosures, not that estimate, determine every endpoint.
fn erfcx_tail(x: &Float) -> (Float, Float) {
    assert!(x >= &64 && x.is_finite());
    let p = x.prec();
    let denominator_lo = Float::with_val_round(p, x * x, Round::Down).0 << 1;
    let denominator_hi = Float::with_val_round(p, x * x, Round::Up).0 << 1;
    let mut term_lo = Float::with_val(p, 1);
    let mut term_hi = term_lo.clone();
    let mut sum_lo = term_lo.clone();
    let mut sum_hi = term_hi.clone();
    let mut lower = Float::with_val(p, 0);
    for k in 1..=64 {
        term_lo = Float::with_val_round(p, &term_lo * (2 * k - 1), Round::Down).0;
        term_hi = Float::with_val_round(p, &term_hi * (2 * k - 1), Round::Up).0;
        term_lo = Float::with_val_round(p, &term_lo / &denominator_hi, Round::Down).0;
        term_hi = Float::with_val_round(p, &term_hi / &denominator_lo, Round::Up).0;
        if k % 2 == 0 {
            sum_lo = Float::with_val_round(p, &sum_lo + &term_lo, Round::Down).0;
            sum_hi = Float::with_val_round(p, &sum_hi + &term_hi, Round::Up).0;
        } else {
            sum_lo = Float::with_val_round(p, &sum_lo - &term_hi, Round::Down).0;
            sum_hi = Float::with_val_round(p, &sum_hi - &term_lo, Round::Up).0;
        }
        if k == 63 {
            lower = sum_lo.clone();
        }
    }
    let mut pi_lo = Float::with_val_round(p, Constant::Pi, Round::Down).0;
    let mut pi_hi = Float::with_val_round(p, Constant::Pi, Round::Up).0;
    pi_lo.sqrt_round(Round::Down);
    pi_hi.sqrt_round(Round::Up);
    let scale_lo = Float::with_val_round(p, x * &pi_lo, Round::Down).0;
    let scale_hi = Float::with_val_round(p, x * &pi_hi, Round::Up).0;
    (
        Float::with_val_round(p, &lower / &scale_hi, Round::Down).0,
        Float::with_val_round(p, &sum_hi / &scale_lo, Round::Up).0,
    )
}

fn scaled_argument(x: f64, p: u32) -> (Float, Float) {
    let mut sqrt_lo = Float::with_val(p, 2);
    let mut sqrt_hi = sqrt_lo.clone();
    sqrt_lo.sqrt_round(Round::Down);
    sqrt_hi.sqrt_round(Round::Up);
    let magnitude = Float::with_val(p, x.abs());
    (
        Float::with_val_round(p, &magnitude / &sqrt_hi, Round::Down).0,
        Float::with_val_round(p, &magnitude / &sqrt_lo, Round::Up).0,
    )
}

/// Phi(-|x|). This range keeps erfc inside MPFR's default exponent range.
fn tail(x: f64, p: u32) -> (Float, Float) {
    assert!(x.is_finite() && x.abs() <= 40.0);
    let (mut hi, mut lo) = scaled_argument(x, p);
    // erfc decreases, so reverse the argument endpoints.
    lo.erfc_round(Round::Down);
    hi.erfc_round(Round::Up);
    (lo >> 1, hi >> 1)
}

pub(super) fn cdf(x: f64, p: u32) -> (Float, Float) {
    let (lo, hi) = tail(x, p);
    if x <= 0.0 {
        (lo, hi)
    } else {
        let one = Float::with_val(p, 1);
        (
            Float::with_val_round(p, &one - &hi, Round::Down).0,
            Float::with_val_round(p, &one - &lo, Round::Up).0,
        )
    }
}

pub(super) fn log_cdf(x: f64, p: u32) -> (Float, Float) {
    assert!(x.is_finite() && x <= 40.0);
    if x < -8.0 {
        let (arg_lo, arg_hi) = scaled_argument(x, p);
        // erfcx is strictly decreasing by its defining positive integral.
        let (mut lo, _) = erfcx(&arg_hi);
        let (_, mut hi) = erfcx(&arg_lo);
        lo >>= 1;
        hi >>= 1;
        lo.ln_round(Round::Down);
        hi.ln_round(Round::Up);
        let input = Float::with_val(p, x);
        // The binary64 square is exact at p>=256, including x near MAX.
        let half_square = Float::with_val(p, &input * &input) >> 1;
        return (
            Float::with_val_round(p, &lo - &half_square, Round::Down).0,
            Float::with_val_round(p, &hi - &half_square, Round::Up).0,
        );
    }
    if x > 0.0 {
        let (tail_lo, tail_hi) = tail(x, p);
        let mut lo = -tail_hi;
        let mut hi = -tail_lo;
        lo.ln_1p_round(Round::Down);
        hi.ln_1p_round(Round::Up);
        (lo, hi)
    } else {
        let (mut lo, mut hi) = cdf(x, p);
        lo.ln_round(Round::Down);
        hi.ln_round(Round::Up);
        (lo, hi)
    }
}

/// phi(x) = exp(-x²/2) / sqrt(2 pi). The binary64 square is exact at p >= 256,
/// and |x| <= 40 keeps the exponential inside MPFR's default exponent range.
pub(super) fn pdf(x: f64, p: u32) -> (Float, Float) {
    assert!(x.is_finite() && x.abs() <= 40.0);
    let input = Float::with_val(p, x);
    let half_square: Float = Float::with_val(p, &input * &input) >> 1;
    let exponent = -half_square;
    let (mut lo, mut hi) = (exponent.clone(), exponent);
    lo.exp_round(Round::Down);
    hi.exp_round(Round::Up);
    let (mut root_lo, mut root_hi) = two_pi(p);
    root_lo.sqrt_round(Round::Down);
    root_hi.sqrt_round(Round::Up);
    (
        Float::with_val_round(p, &lo / &root_hi, Round::Down).0,
        Float::with_val_round(p, &hi / &root_lo, Round::Up).0,
    )
}

/// ln phi(x) = -x²/2 - ln(2 pi)/2, for every finite x.
pub(super) fn log_pdf(x: f64, p: u32) -> (Float, Float) {
    assert!(x.is_finite());
    let input = Float::with_val(p, x);
    let half_square = Float::with_val(p, &input * &input) >> 1;
    let (mut c_lo, mut c_hi) = two_pi(p);
    c_lo.ln_round(Round::Down);
    c_hi.ln_round(Round::Up);
    c_lo >>= 1;
    c_hi >>= 1;
    let magnitude_lo = Float::with_val_round(p, &half_square + &c_lo, Round::Down).0;
    let magnitude_hi = Float::with_val_round(p, &half_square + &c_hi, Round::Up).0;
    (-magnitude_hi, -magnitude_lo)
}

/// Phi(x) - 1/2 = erf(x / sqrt 2) / 2, which is odd and increasing.
pub(super) fn centered(x: f64, p: u32) -> (Float, Float) {
    assert!(x.is_finite() && x.abs() <= 40.0);
    let (mut lo, mut hi) = scaled_argument(x, p);
    lo.erf_round(Round::Down);
    hi.erf_round(Round::Up);
    let (lo, hi): (Float, Float) = (lo >> 1, hi >> 1);
    if x.is_sign_negative() {
        (-hi, -lo)
    } else {
        (lo, hi)
    }
}

fn two_pi(p: u32) -> (Float, Float) {
    let lo = Float::with_val_round(p, Constant::Pi, Round::Down).0 << 1;
    let hi = Float::with_val_round(p, Constant::Pi, Round::Up).0 << 1;
    (lo, hi)
}
