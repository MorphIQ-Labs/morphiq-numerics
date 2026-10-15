//! Scalar composition sequences on all supported SIMD backends.
use morphiq_numerics_arch::Simd;

use super::{Operation, SMALL, TINY, tables};
use crate::lanes::{
    Dw, Kernel, add_dw, add_f64, fast_two_sum, lanes_mask, mask_from, two_prod, two_sum,
};

pub(crate) struct Normal<const OP: u8>;

fn operation<const OP: u8>() -> Operation {
    match OP {
        0 => Operation::Pdf,
        1 | 2 => Operation::Cdf,
        3 => Operation::Centered,
        4 => Operation::LogCdf,
        _ => unreachable!(),
    }
}

#[inline(always)]
fn constant<K: Simd>(k: K, x: (f64, f64)) -> Dw<K> {
    two_sum(k, k.splat(x.0), k.splat(x.1))
}

#[inline(always)]
fn mul<K: Simd>(k: K, a: Dw<K>, b: Dw<K>) -> Dw<K> {
    let (p, e) = two_prod(k, a.0, b.0);
    fast_two_sum(k, p, k.add(e, k.add(k.mul(a.0, b.1), k.mul(a.1, b.0))))
}

#[inline(always)]
fn mul_f64<K: Simd>(k: K, a: Dw<K>, b: K::F) -> Dw<K> {
    let (p, e) = two_prod(k, a.0, b);
    let (h, l) = fast_two_sum(k, p, k.mul(a.1, b));
    fast_two_sum(k, h, k.add(l, e))
}

#[inline(always)]
fn neg<K: Simd>(k: K, a: Dw<K>) -> Dw<K> {
    (k.neg(a.0), k.neg(a.1))
}

#[inline(always)]
fn select<K: Simd>(k: K, mask: K::M, a: Dw<K>, b: Dw<K>) -> Dw<K> {
    (k.select(mask, a.0, b.0), k.select(mask, a.1, b.1))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn center<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let density = constant(k, tables::DENSITY);
    let leading = mul_f64(k, density, x);
    let small = k.lt(k.abs(x), k.splat(SMALL));
    if k.mask_bits(small) == lanes_mask::<K>() {
        return leading;
    }
    let regular = k.select(small, k.splat(0.25), x);
    let z = two_prod(k, regular, regular);
    let mut tail = k.splat(tables::CENTER[12].0);
    for n in (4..12).rev() {
        tail = k.add(k.splat(tables::CENTER[n].0), k.mul(z.0, tail));
    }
    let mut p = add_dw(k, constant(k, tables::CENTER[3]), mul_f64(k, z, tail));
    for n in (0..3).rev() {
        p = add_dw(k, constant(k, tables::CENTER[n]), mul(k, z, p));
    }
    select(k, small, leading, mul(k, leading, p))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn gaussian<K: Simd>(k: K, x: K::F) -> (Dw<K>, K::F) {
    let x = k.select(k.lt(x, k.splat(SMALL)), k.splat(0.0), x);
    let (h, l) = two_prod(k, x, k.mul(k.splat(-0.5), x));
    let (y, n) = crate::exp::lanes::stage_b_double_word(k, h, l);
    let mut scale = K::Array::default();
    for (i, &n) in k.store(n).as_ref().iter().enumerate() {
        scale.as_mut()[i] = super::pow2((n as i32).div_euclid(512));
    }
    (two_sum(k, y.0, y.1), k.load(scale))
}

#[inline(always)]
fn scaled<K: Simd>(k: K, y: Dw<K>, scale: K::F) -> Dw<K> {
    two_sum(k, k.mul(y.0, scale), k.mul(y.1, scale))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn scaled_erfcx<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let z = mul_f64(k, constant(k, tables::INV_SQRT2), x);
    let table = k.lt(z.0, k.splat(16.0));
    let table_bits = k.mask_bits(table);
    let mut f = (k.splat(0.0), k.splat(0.0));
    if table_bits != 0 {
        f = crate::erfcx::lanes::table(k, k.select(table, z.0, k.splat(1.0)));
    }
    if table_bits != lanes_mask::<K>() {
        let a = crate::erfcx::lanes::asymptotic(k, k.select(table, k.splat(16.0), z.0));
        f = select(k, table, f, a);
    }
    let derivative = k.sub(
        k.mul(k.mul(k.splat(2.0), z.0), f.0),
        k.splat(tables::TWO_INV_SQRT_PI.0),
    );
    two_sum(k, f.0, k.add(f.1, k.mul(z.1, derivative)))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn tail<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let (g, scale) = gaussian(k, x);
    scaled(k, mul(k, g, scaled_erfcx(k, x)), k.mul(scale, k.splat(0.5)))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn log_dw<K: Simd>(k: K, x: Dw<K>) -> Dw<K> {
    add_f64(k, crate::ln::lanes::fallback::ln(k, x.0), k.div(x.1, x.0))
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn log_complement<K: Simd>(k: K, q: Dw<K>) -> Dw<K> {
    let tiny = k.lt(q.0, k.splat(f64::from_bits(0x3c90_0000_0000_0000)));
    let bits = k.mask_bits(tiny);
    let mut y = (k.splat(0.0), k.splat(0.0));
    if bits != 0 {
        y = two_sum(
            k,
            k.neg(q.0),
            k.sub(k.neg(q.1), k.mul(k.mul(k.splat(0.5), q.0), q.0)),
        );
    }
    if bits != lanes_mask::<K>() {
        let active = k.select(tiny, k.splat(0.25), q.0);
        let b = crate::ln::lanes::stage_b::value(k, k.neg(active));
        let regular = two_sum(k, b.0, k.sub(b.1, k.div(q.1, k.sub(k.splat(1.0), active))));
        y = select(k, tiny, y, regular);
    }
    y
}

/// Candidate values for finite |x| <= 37 and |x| >= TINY. The caller
/// screens special values and replaces inactive lanes before entering here.
// In debug builds, keep a call boundary so composing several kernels does
// not accumulate every intrinsic temporary in one multi-megabyte frame.
// Optimized builds inline into the backend's target-feature context.
#[cfg_attr(not(debug_assertions), inline(always))]
fn candidate<K: Simd>(k: K, op: Operation, x: K::F) -> Dw<K> {
    let a = k.abs(x);
    if matches!(op, Operation::Pdf) {
        let (g, scale) = gaussian(k, a);
        return scaled(k, mul(k, g, constant(k, tables::DENSITY)), scale);
    }
    let central = k.le(a, k.splat(0.5));
    let central_bits = k.mask_bits(central);
    let mut y = (k.splat(0.0), k.splat(0.0));
    if central_bits != 0 {
        let c = center(k, k.select(central, x, k.splat(0.25)));
        y = match op {
            Operation::Centered => c,
            Operation::Cdf => add_f64(k, c, k.splat(0.5)),
            Operation::LogCdf => log_dw(k, add_f64(k, c, k.splat(0.5))),
            Operation::Pdf => unreachable!(),
        };
    }
    if central_bits == lanes_mask::<K>() {
        return y;
    }
    let a = k.select(central, k.splat(1.0), a);
    let negative = k.lt(x, k.splat(0.0));
    let outer = if matches!(op, Operation::LogCdf) {
        let negative_bits = k.mask_bits(negative) & !central_bits;
        let positive_bits = !k.mask_bits(negative) & !central_bits & lanes_mask::<K>();
        let mut z = (k.splat(0.0), k.splat(0.0));
        if negative_bits != 0 {
            let input = k.select(mask_from(k, negative_bits), a, k.splat(1.0));
            let square = two_prod(k, input, k.mul(k.splat(-0.5), input));
            let ln = add_dw(
                k,
                log_dw(k, scaled_erfcx(k, input)),
                neg(k, constant(k, tables::LN2)),
            );
            z = add_dw(k, two_sum(k, square.0, square.1), ln);
        }
        if positive_bits != 0 {
            let input = k.select(mask_from(k, positive_bits), a, k.splat(1.0));
            z = select(k, negative, z, log_complement(k, tail(k, input)));
        }
        z
    } else {
        let q = tail(k, a);
        match op {
            Operation::Cdf => select(k, negative, q, add_f64(k, neg(k, q), k.splat(1.0))),
            Operation::Centered => {
                let z = add_f64(k, neg(k, q), k.splat(0.5));
                select(k, negative, neg(k, z), z)
            }
            _ => unreachable!(),
        }
    };
    select(k, central, y, outer)
}

impl<const OP: u8> Kernel for Normal<OP> {
    fn scalar(x: f64) -> f64 {
        if OP == 2 && !x.is_nan() {
            super::evaluate(Operation::Cdf, -x)
        } else {
            super::evaluate(operation::<OP>(), x)
        }
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        if OP != 4 {
            return Self::regular(k, input);
        }
        let x = k.load(input);
        let far = k.and_m(
            k.lt(x, k.splat(-37.0)),
            k.lt(k.splat(-tables::LOG_OVERFLOW), x),
        );
        let active = k.mask_bits(far);
        if active.count_ones() < 2 {
            return Self::regular(k, input);
        }
        let a = k.neg(k.select(far, x, k.splat(-38.0)));
        let (tail, accepted) = super::log_tail::lanes::decide(k, a);
        let mut out = if active == lanes_mask::<K>() {
            k.store(tail)
        } else {
            // Zero is a special value. It excludes far-tail lanes from the
            // ordinary polynomial while retaining SIMD for the other lanes.
            let regular = Self::regular(k, k.store(k.select(far, k.splat(0.0), x)));
            k.store(k.select(far, tail, k.load(regular)))
        };
        let pending = active & !accepted;
        if pending != 0 {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if pending >> i & 1 != 0 {
                    *value = super::accurate::evaluate(Operation::LogCdf, input.as_ref()[i]);
                }
            }
        }
        out
    }
}

impl<const OP: u8> Normal<OP> {
    #[inline(always)]
    fn regular<K: Simd>(k: K, input: K::Array) -> K::Array {
        let op = operation::<OP>();
        let xv = if OP == 2 {
            k.neg(k.load(input))
        } else {
            k.load(input)
        };
        let all = lanes_mask::<K>();
        // Saturation is itself a vector operation. Ordered comparisons keep
        // NaN payloads on the scalar special-value path.
        match op {
            Operation::Pdf if k.mask_bits(k.lt(k.abs(xv), k.splat(SMALL))) == all => {
                return k.store(k.splat(tables::DENSITY.0));
            }
            Operation::Pdf if k.mask_bits(k.le(k.splat(tables::PDF_ZERO), k.abs(xv))) == all => {
                return k.store(k.splat(0.0));
            }
            Operation::Cdf if k.mask_bits(k.le(k.splat(tables::CDF_ONE), xv)) == all => {
                return k.store(k.splat(1.0));
            }
            Operation::Cdf if k.mask_bits(k.le(xv, k.splat(-tables::TAIL_ZERO))) == all => {
                return k.store(k.splat(0.0));
            }
            Operation::Centered
                if k.mask_bits(k.le(k.splat(tables::CENTERED_HALF), k.abs(xv))) == all =>
            {
                return k.store(k.to_float(k.or_u(
                    k.splat_bits(0.5_f64.to_bits()),
                    k.and_u(k.to_bits(xv), k.splat_bits(1 << 63)),
                )));
            }
            Operation::LogCdf if k.mask_bits(k.le(k.splat(tables::TAIL_ZERO), xv)) == all => {
                return k.store(k.splat(-0.0));
            }
            Operation::LogCdf if k.mask_bits(k.le(xv, k.splat(-tables::LOG_OVERFLOW))) == all => {
                return k.store(k.splat(f64::NEG_INFINITY));
            }
            _ => {}
        }
        let mut x = input;
        let mut active = 0_u64;
        for (i, v) in x.as_mut().iter_mut().enumerate() {
            if OP == 2 && !v.is_nan() {
                *v = -*v;
            }
            if super::special(op, *v).is_none() && (TINY..=37.0).contains(&v.abs()) {
                active |= 1 << i;
            } else {
                *v = 0.25;
            }
        }
        // A saturated batch has no polynomial work. A single active lane
        // cannot amortize vector setup or region masking; evaluate it once.
        let central = k.mask_bits(k.le(k.abs(xv), k.splat(0.5))) & active;
        let negative = k.mask_bits(k.lt(xv, k.splat(0.0))) & active;
        let split_regions = K::LANES == 2
            && !matches!(op, Operation::Pdf)
            && ((central != 0 && central != active)
                || (matches!(op, Operation::LogCdf)
                    && central == 0
                    && negative != 0
                    && negative != active));
        if active.count_ones() <= 1 || split_regions {
            let mut out = input;
            for v in out.as_mut() {
                *v = Self::scalar(*v);
            }
            return out;
        }
        let y = candidate(k, op, k.load(x));
        let eps = k.mul(k.abs(y.0), k.splat(super::guard(op)));
        let low = k.add(y.0, k.sub(y.1, eps));
        let high = k.add(y.0, k.add(y.1, eps));
        let decided = k.mask_bits(k.eq_u(k.to_bits(low), k.to_bits(high))) & active;
        let mut out = k.store(low);
        if decided != lanes_mask::<K>() {
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = Self::scalar(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests;
