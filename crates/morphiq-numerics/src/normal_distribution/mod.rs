//! Standard normal density and distribution compositions.
pub(crate) mod accurate;
#[cfg(all(test, feature = "simd"))]
mod bench;
pub(crate) mod finite_tail;
#[cfg(feature = "simd")]
pub(crate) mod lanes;
mod log_first_table;
pub(crate) mod log_tail;
mod tables;

/// Generated nearest-binary64 high word, shared with the bounded CDF.
pub(crate) const INV_SQRT2_HIGH: f64 = tables::INV_SQRT2.0;
#[cfg(test)]
mod tests;

use crate::double_word::DoubleWord as Dw;
use crate::eft::two_prod_d;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Operation {
    Pdf,
    Cdf,
    Centered,
    LogCdf,
}

// The complete composition and rounded-endpoint proofs certify these guards.
// See formal/normal/NormalFastDispatch.v and docs/normal.md.
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
    density.mul_f64(x).mul(center_polynomial(z))
}

#[inline]
pub(crate) fn center_polynomial(z: Dw) -> Dw {
    let tail = center_tail(z.hi());
    let mut p = dw(tables::CENTER[3]).add(z.mul_f64(tail));
    for n in (0..3).rev() {
        p = dw(tables::CENTER[n]).add(z.mul(p));
    }
    p
}

#[inline]
pub(crate) fn center_tail(z: f64) -> f64 {
    let mut tail = tables::CENTER[12].0;
    for n in (4..12).rev() {
        tail = tables::CENTER[n].0 + z * tail;
    }
    tail
}

/// exp(-x²/2) as a double-word mantissa and an external binary exponent.
pub(crate) fn gaussian(x: f64) -> (Dw, i32) {
    let (h, l) = if x < SMALL {
        (0.0, 0.0)
    } else {
        // In D: NormalGaussianKernel.normal_half_square_exact.
        two_prod_d(x, -0.5 * x)
    };
    let (yh, yl, k) = crate::exp::stage_b_double_word(h, l);
    (Dw::sum(yh, yl), k)
}

#[inline]
pub(crate) fn scaled_argument(x: f64) -> Dw {
    // In D: NormalFastScaledArgument.
    dw(tables::INV_SQRT2).mul_f64_d(x)
}

pub(crate) fn scaled_erfcx(x: f64) -> Dw {
    let z = scaled_argument(x);
    let (fh, fl) = if z.hi() < 16.0 {
        crate::erfcx::t_eval(z.hi())
    } else {
        crate::erfcx::ya_eval(z.hi())
    };
    // F'(z)=2z F(z)-2/sqrt(pi). The correction is evaluated before the
    // final rounding; its second-order remainder enters the composition guard.
    let derivative = (2.0 * z.hi()) * fh - tables::TWO_INV_SQRT_PI.0;
    // |fh| dominates: erfcx's value against its low word and the correction.
    Dw::fast_sum(fh, fl + z.lo() * derivative)
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

#[inline]
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
        Operation::Pdf if x.abs() < SMALL => Some(tables::DENSITY.0),
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
#[inline]
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
            // In D: NormalGaussianKernel.normal_half_square_exact.
            let (h, l) = two_prod_d(a, -0.5 * a);
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

/// The central first stage's guard on `C(x) = Φ(x) − 1/2`: its relative
/// error bound `3.2·2^−60`, rounded up to `2^−58` (docs/normal.md, the CDF
/// family's central first stage; formal/normal/NormalCenterFirst.v).
const E_CENTER_FIRST: f64 = f64::from_bits(0x3c50_0000_0000_0000);

/// The CDF family's first stage on the centre, `2^−33 <= |x| <= 1/2`:
/// `C(x) = φ(0)·x·P(x²)` with the exact square, `φ(0)·x` and `c1·x²` carried
/// as double words and the rest of `P` in binary64, then `C` or `1/2 + C`
/// and a rounding test. `None` sends the argument to the fast dispatch.
#[inline]
pub(crate) fn center_first(op: Operation, x: f64) -> Option<f64> {
    let (ch, cl) = center_first_parts(x);
    let e = ch.abs() * E_CENTER_FIRST;
    let (y, w) = match op {
        Operation::Centered => (ch, cl),
        Operation::Cdf => {
            // |ch| <= 0.21, so 1/2 + ch is a Fast2Sum.
            let (u, v) = crate::eft::fast_two_sum(0.5, ch);
            (u, v + cl)
        }
        _ => return None,
    };
    let low = y + (w - e);
    let high = y + (w + e);
    (low.to_bits() == high.to_bits()).then_some(low)
}

/// The central first stage's words `(ch, cl)`, also for the cross-check.
#[inline]
pub(crate) fn center_first_parts(x: f64) -> (f64, f64) {
    // zh + zl = x² exactly; e1h + e1l ≈ c1·x², e2 the rest of P − 1.
    // In D: NormalCenterFirst.center_first_poly.
    let (zh, zl) = two_prod_d(x, x);
    let c1 = tables::CENTER[1];
    let (e1h, e1p) = two_prod_d(c1.0, zh);
    let e1l = e1p + (c1.0 * zl + c1.1 * zh);
    let t3 = tables::CENTER[3].0 + zh * center_tail(zh);
    let e2 = (zh * zh) * (tables::CENTER[2].0 + zh * t3);
    // dh + dl ≈ φ(0)·x; dh·e1h exactly; the cross terms in binary64.
    // In D: NormalCenterFirst.normal_center_first_parts_ok.
    let (dh, dp) = two_prod_d(tables::DENSITY.0, x);
    let dl = dp + tables::DENSITY.1 * x;
    let (ph, pp) = two_prod_d(dh, e1h);
    let rest = dl + (pp + (dh * e1l + dl * e1h + dh * e2));
    let (s, t) = crate::eft::fast_two_sum(dh, ph);
    crate::eft::fast_two_sum(s, t + rest)
}

/// The CDF family's first-stage guard on the tail probability `q`: its
/// relative error bound, rounded up to `2^−58` (docs/normal.md, the CDF
/// family's tail first stage; formal/normal/NormalTailFirst.v).
const E_TAIL_FIRST: f64 = f64::from_bits(0x3c50_0000_0000_0000);
/// The complements' allowance for the test's own roundings near one.
const E_TAIL_FIRST_ONE: f64 = f64::from_bits(0x39b0_0000_0000_0000); // 2^−100

/// The CDF family's first stage on the tail, `1/2 < |x| <= 36`:
/// `q = Φ(−|x|) = exp(−x²/2)·erfcx(|x|/√2)/2` with the Gaussian through exp's
/// lean stage A at the exact double-word `−x²/2`, multiplied into the fast
/// scaled erfcx by one exact product, then `q`, `1 − q` or `±(1/2 − q)` and
/// a rounding test. `None` sends the argument to the double-word stage.
#[inline]
pub(crate) fn tail_first(op: Operation, x: f64) -> Option<f64> {
    let (qh, ql) = tail_first_parts(x);
    let e = qh * E_TAIL_FIRST;
    let (y, w, e) = match op {
        Operation::Cdf if x < 0.0 => (qh, ql, e),
        Operation::Cdf => {
            let (s, t) = crate::eft::fast_two_sum(1.0, -qh);
            (s, t - ql, e + E_TAIL_FIRST_ONE)
        }
        Operation::Centered => {
            let (s, t) = crate::eft::fast_two_sum(0.5, -qh);
            let (s, t) = (s, t - ql);
            let e = e + E_TAIL_FIRST_ONE;
            if x.is_sign_negative() {
                (-s, -t, e)
            } else {
                (s, t, e)
            }
        }
        _ => return None,
    };
    let low = y + (w - e);
    let high = y + (w + e);
    (low.to_bits() == high.to_bits()).then_some(low)
}

/// The first stage's tail words `(qh, ql)`, also for the cross-check.
#[inline]
pub(crate) fn tail_first_parts(x: f64) -> (f64, f64) {
    let a = x.abs();
    // In D: NormalGaussianKernel.normal_half_square_exact.
    let (h, l) = two_prod_d(a, -0.5 * a);
    let (ye, le, k) = crate::exp::stage_a_double_word(h, l);
    let f = scaled_erfcx(a);
    // ye·f.hi exactly; the cross terms in binary64.
    // In D: NormalTailFirst.normal_tail_first_parts_ok.
    let (p, pe) = two_prod_d(ye, f.hi());
    let pl = pe + (ye * f.lo() + le * f.hi());
    #[allow(clippy::cast_possible_truncation)] // |k| <= 1016
    let scale = pow2(k as i32 - 1);
    (p * scale, pl * scale)
}

#[inline]
pub(crate) fn evaluate(op: Operation, x: f64) -> f64 {
    if let Some(value) = special(op, x) {
        return value;
    }
    if x.abs() >= SMALL
        && let Some(value) = first_decide(op, x)
    {
        return value;
    }
    fast_decide(op, x).unwrap_or_else(|| accurate::evaluate(op, x))
}

/// Try the first stages in public-dispatch order. Measurements use the same
/// decision to count accurate-path calls after screening special values.
#[inline]
pub(crate) fn first_decide(op: Operation, x: f64) -> Option<f64> {
    if matches!(op, Operation::Pdf)
        && x.abs() <= 37.0
        && let Some(value) = density_first(x)
    {
        return Some(value);
    }
    if matches!(op, Operation::Cdf | Operation::Centered)
        && x.abs() >= SMALL
        && x.abs() <= 0.5
        && let Some(value) = center_first(op, x)
    {
        return Some(value);
    }
    if matches!(op, Operation::Cdf | Operation::Centered)
        && x.abs() > 0.5
        && x.abs() <= 36.0
        && let Some(value) = tail_first(op, x)
    {
        return Some(value);
    }
    None
}

/// The density's first-stage bound: `stage_a_double_word`'s `0x1.7p−61`, the
/// argument's error and the test's own rounding, rounded up to `1.75·2^−61`
/// (docs/normal.md, density first stage; formal/normal/NormalDensityFirst.v).
const E_DENSITY_FIRST: f64 = f64::from_bits(0x3c2c_0000_0000_0000);

/// The density's first stage: `RN(φ(x))` as `exp(−x²/2 − ln √(2π))`, through
/// exp's lean stage A at the exact double-word argument, when its rounding
/// test decides; `None` sends the argument to the double-word stage. For
/// `2^−33 ≤ |x| ≤ 37`.
#[inline]
pub(crate) fn density_first(x: f64) -> Option<f64> {
    let (y, l, k, _) = density_first_parts(x);
    crate::exp::decide(y, l, E_DENSITY_FIRST, k)
}

/// The first stage's words `(y, l, k, [s, se])`, also for the cross-check.
#[inline]
pub(crate) fn density_first_parts(x: f64) -> (f64, f64, i64, [f64; 2]) {
    let a = x.abs();
    // h + l = −a²/2 exactly; s + e = h − ln √(2π)'s high word exactly.
    // In D: NormalGaussianKernel.normal_half_square_exact.
    let (h, l) = two_prod_d(a, -0.5 * a);
    let (s, e) = crate::eft::two_sum(h, -tables::LN_SQRT_2PI.0);
    let se = e + (l - tables::LN_SQRT_2PI.1);
    let (y, w, k) = crate::exp::stage_a_double_word(s, se);
    (y, w, k, [s, se])
}

/// The actual fast-path decision, also transcribed for the proof cross-check.
#[inline]
pub(crate) fn fast_decide(op: Operation, x: f64) -> Option<f64> {
    let a = x.abs();
    if a > 37.0 {
        if matches!(op, Operation::LogCdf) && x < 0.0 {
            return log_tail::decide(a);
        }
        return if a < 39.0
            && (matches!(op, Operation::Pdf)
                || matches!(op, Operation::Cdf) && x < 0.0
                || matches!(op, Operation::LogCdf) && x > 0.0)
        {
            finite_tail::decide(op, a)
        } else {
            None
        };
    }
    if let Some((y, eps)) = fast(op, x) {
        let low = y.hi() + (y.lo() - eps);
        let high = y.hi() + (y.lo() + eps);
        if low.to_bits() == high.to_bits() {
            return Some(low);
        }
    }
    None
}
