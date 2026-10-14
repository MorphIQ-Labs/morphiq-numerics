//! Standard normal density and distribution compositions.
pub(crate) mod accurate;
#[cfg(all(test, feature = "simd"))]
mod bench;
#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod tables;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord as Dw;
use crate::eft::two_prod;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Operation {
    Pdf,
    Cdf,
    Centered,
    LogCdf,
}

// A conservative candidate guard. Its complete analytic/IEEE certificate is
// required before these experimental kernels become public APIs.
const GUARD: f64 = f64::from_bits(0x3bf0_0000_0000_0000); // 2^-64
// ln's double-word approximation has an absolute, not relative, bound.
// The central log-CDF can have magnitude below one.
const LOG_GUARD: f64 = f64::from_bits(0x3c10_0000_0000_0000); // 2^-62
const SMALL: f64 = f64::from_bits(0x3de0_0000_0000_0000); // 2^-33
const TINY: f64 = f64::from_bits(0x23d0_0000_0000_0000); // 2^-450

fn dw(x: (f64, f64)) -> Dw {
    Dw::sum(x.0, x.1)
}

fn guard(op: Operation) -> f64 {
    if matches!(op, Operation::LogCdf) {
        LOG_GUARD
    } else {
        GUARD
    }
}

fn pow2(k: i32) -> f64 {
    f64::from_bits(((k + 1023) as u64) << 52)
}

/// The centered Gaussian series, without subtracting a rounded probability.
fn center(x: f64) -> Dw {
    let density = dw(tables::DENSITY);
    if x.abs() < SMALL {
        return density.mul_f64(x);
    }
    let z = Dw::product(x, x);
    let mut tail = tables::CENTER[12].0;
    for n in (4..12).rev() {
        tail = tables::CENTER[n].0 + z.hi() * tail;
    }
    let mut p = dw(tables::CENTER[3]).add(z.mul_f64(tail));
    for n in (0..3).rev() {
        p = dw(tables::CENTER[n]).add(z.mul(p));
    }
    density.mul_f64(x).mul(p)
}

/// exp(-x²/2) as a double-word mantissa and an external binary exponent.
pub(crate) fn gaussian(x: f64) -> (Dw, i32) {
    let (h, l) = if x < SMALL {
        (0.0, 0.0)
    } else {
        two_prod(x, -0.5 * x)
    };
    let (yh, yl, k) = crate::exp::stage_b_double_word(h, l);
    (Dw::sum(yh, yl), k)
}

fn scaled_erfcx(x: f64) -> Dw {
    let z = dw(tables::INV_SQRT2).mul_f64(x);
    let (fh, fl) = if z.hi() < 16.0 {
        crate::erfcx::t_eval(z.hi())
    } else {
        crate::erfcx::ya_eval(z.hi())
    };
    // F'(z)=2z F(z)-2/sqrt(pi). The correction is evaluated before the
    // final rounding; its second-order remainder enters the composition guard.
    let derivative = (2.0 * z.hi()) * fh - tables::TWO_INV_SQRT_PI.0;
    Dw::sum(fh, fl + z.lo() * derivative)
}

fn tail(x: f64) -> (Dw, i32) {
    let (g, k) = gaussian(x);
    (g.mul(scaled_erfcx(x)), k - 1)
}

fn scaled(y: Dw, k: i32) -> Dw {
    let scale = pow2(k);
    Dw::sum(y.hi() * scale, y.lo() * scale)
}

fn log_dw(x: Dw) -> Dw {
    crate::ln::Reduced::of(x.hi())
        .fast_value()
        .add_f64(x.lo() / x.hi())
}

fn log_complement(q: Dw) -> Dw {
    if q.hi() < f64::from_bits(0x3c90_0000_0000_0000) {
        return Dw::sum(-q.hi(), -q.lo() - (0.5 * q.hi()) * q.hi());
    }
    let (h, l, _, _) = crate::ln::stages::stage_b_parts(-q.hi());
    Dw::sum(h, l - q.lo() / (1.0 - q.hi()))
}

pub(crate) fn special(op: Operation, x: f64) -> Option<f64> {
    if x.is_nan() {
        return Some(x);
    }
    if x == 0.0 {
        return Some(match op {
            Operation::Pdf => tables::DENSITY.0,
            Operation::Cdf => 0.5,
            Operation::Centered => x,
            Operation::LogCdf => -tables::LN2.0,
        });
    }
    match op {
        Operation::Pdf if x.abs() >= tables::PDF_ZERO => Some(0.0),
        Operation::Cdf if x >= tables::CDF_ONE => Some(1.0),
        Operation::Cdf if x <= -tables::TAIL_ZERO => Some(0.0),
        Operation::Centered if x.abs() >= tables::CENTERED_HALF => Some(0.5_f64.copysign(x)),
        Operation::LogCdf if x >= tables::TAIL_ZERO => Some(-0.0),
        Operation::LogCdf if x <= -tables::LOG_OVERFLOW => Some(f64::NEG_INFINITY),
        _ => None,
    }
}

/// A candidate value and its absolute guard, before the final rounding test.
pub(crate) fn fast(op: Operation, x: f64) -> Option<(Dw, f64)> {
    let a = x.abs();
    // The centered product's cross terms must stay within the double-word
    // multiplication proof's normal-or-zero domain, also when it feeds CDF
    // or log-CDF. Q256 handles smaller inputs without an exponent limitation.
    if a > 37.0 || (!matches!(op, Operation::Pdf) && a < TINY) {
        return None;
    }
    let value = match op {
        Operation::Pdf => {
            let (g, k) = gaussian(a);
            scaled(g.mul(dw(tables::DENSITY)), k)
        }
        Operation::Centered if a <= 0.5 => center(x),
        Operation::Cdf if a <= 0.5 => center(x).add_f64(0.5),
        Operation::LogCdf if a <= 0.5 => log_dw(center(x).add_f64(0.5)),
        Operation::LogCdf if x < 0.0 => {
            let (h, l) = two_prod(a, -0.5 * a);
            let ln_scaled = log_dw(scaled_erfcx(a)).sub(dw(tables::LN2));
            Dw::sum(h, l).add(ln_scaled)
        }
        _ => {
            let (q, k) = tail(a);
            let q = scaled(q, k);
            match op {
                Operation::Cdf if x < 0.0 => q,
                Operation::Cdf => q.neg().add_f64(1.0),
                Operation::Centered => {
                    let y = q.neg().add_f64(0.5);
                    if x.is_sign_negative() { y.neg() } else { y }
                }
                Operation::LogCdf => log_complement(q),
                Operation::Pdf => unreachable!(),
            }
        }
    };
    Some((value, value.hi().abs() * guard(op)))
}

pub(crate) fn evaluate(op: Operation, x: f64) -> f64 {
    if let Some(value) = special(op, x) {
        return value;
    }
    fast_decide(op, x).unwrap_or_else(|| accurate::evaluate(op, x))
}

/// The actual fast-path decision, also transcribed for the proof cross-check.
#[inline]
pub(crate) fn fast_decide(op: Operation, x: f64) -> Option<f64> {
    if let Some((y, eps)) = fast(op, x) {
        let low = y.hi() + (y.lo() - eps);
        let high = y.hi() + (y.lo() + eps);
        if low.to_bits() == high.to_bits() {
            return Some(low);
        }
    }
    None
}
