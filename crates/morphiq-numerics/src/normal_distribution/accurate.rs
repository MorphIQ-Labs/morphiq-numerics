//! Extended-precision compositions from the original binary64 argument.
use super::{Operation, tables};
use crate::eft::two_prod;
use crate::q256::Q256;

fn q(x: f64) -> Q256 {
    Q256::from_f64(x)
}

/// exp(-x²/2), without rounding the square to one word or the result to f64.
pub(crate) fn gaussian(x: f64) -> Q256 {
    // The dispatcher limits this path to |x| < PDF_ZERO (< 38.6). Below 2^-400,
    // the omitted square is far below the Q256 significand of one.
    if x.abs() < f64::from_bits(0x26f0_0000_0000_0000) {
        return Q256::ONE;
    }
    let (h, l) = two_prod(x, -0.5 * x);
    crate::erfcx::accurate::reflected_exponential(h, l).mul_pow2(-1)
}

/// Integral from zero to x of the normal density, for |x| <= 1/2.
pub(crate) fn center(x: f64) -> Q256 {
    let x = q(x);
    let z = x.mul(x).mul_pow2(-1).neg();
    let coefficient = |n: usize| {
        let (m, e) = tables::Q_CENTER[n];
        Q256::new(false, m, e)
    };
    let mut sum = coefficient(40);
    for n in (0..40).rev() {
        sum = coefficient(n).add(z.mul(sum));
    }
    x.mul(tables::q_density()).mul(sum)
}

pub(crate) fn density(x: f64) -> Q256 {
    gaussian(x).mul(tables::q_density())
}

pub(crate) fn central_cdf(x: f64) -> Q256 {
    q(0.5).add(center(x))
}

fn tail(x: f64) -> Q256 {
    let z = q(x).mul(tables::q_inv_sqrt2());
    let scaled = crate::erfcx::accurate::positive(z);
    gaussian(x).mul(scaled).mul_pow2(-1)
}

/// ln(x) from a normalized atanh series; x stays in extended precision.
fn logarithm(x: Q256) -> Q256 {
    let e = x.top();
    let y = x.mul_pow2(-e);
    let t = y.add(Q256::ONE.neg()).mul(y.add(Q256::ONE).recip());
    let t2 = t.mul(t);
    let mut power = t;
    let mut sum = t;
    for n in 1..100 {
        power = power.mul(t2);
        let term = power.mul(q(f64::from(2 * n + 1)).recip());
        sum = sum.add(term);
        if term.top() < sum.top() - 270 {
            break;
        }
    }
    sum.mul_pow2(1).add(q(f64::from(e)).mul(tables::q_ln2()))
}

/// ln(1-x) for 0 < x <= 1/2, without first rounding 1-x.
fn log_complement(x: Q256) -> Q256 {
    let mut power = x;
    let mut sum = x;
    for n in 2..300 {
        power = power.mul(x);
        let term = power.mul(q(f64::from(n)).recip());
        sum = sum.add(term);
        if term.top() < sum.top() - 270 {
            break;
        }
    }
    sum.neg()
}

pub(super) fn evaluate(op: Operation, x: f64) -> f64 {
    let a = x.abs();
    let result = match op {
        Operation::Pdf => density(a),
        Operation::Centered if a <= 0.5 => center(x),
        Operation::Centered => {
            let positive = q(0.5).add(tail(a).neg());
            if x.is_sign_negative() {
                positive.neg()
            } else {
                positive
            }
        }
        Operation::Cdf if a <= 0.5 => central_cdf(x),
        Operation::Cdf if x < 0.0 => tail(a),
        Operation::Cdf => Q256::ONE.add(tail(a).neg()),
        Operation::LogCdf if a <= 0.5 => logarithm(central_cdf(x)),
        Operation::LogCdf if x > 0.0 => log_complement(tail(a)),
        Operation::LogCdf => {
            // This path never constructs the exponentially small probability.
            // Q256's integer exponent also avoids an overflowing binary64 square.
            let z = q(a).mul(tables::q_inv_sqrt2());
            let scaled = crate::erfcx::accurate::positive(z).mul_pow2(-1);
            q(a).mul(q(a)).mul_pow2(-1).neg().add(logarithm(scaled))
        }
    };
    let y = result.to_f64();
    if matches!(op, Operation::Centered) && y == 0.0 {
        0.0_f64.copysign(x)
    } else if matches!(op, Operation::LogCdf) && y == 0.0 {
        -0.0
    } else {
        y
    }
}
