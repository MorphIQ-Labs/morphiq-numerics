//! Q256 fallback: Taylor coefficients from the ODE, an asymptotic series,
//! and negative reflection. Assurance limits are stated in docs/erfcx.md.
use super::accurate_tables::{C, C2, CS, F_AT_C, LN2_128, RECIP, T2};
use super::{Region, region, t_reduce};
use crate::eft::two_prod;
use crate::exp::tables::{INV_L, SHIFTER};
use crate::q256::Q256;

fn q(c: C) -> Q256 {
    Q256::new(false, c.0, c.1)
}

#[cold]
#[inline(never)]
pub(super) fn accurate(x: f64) -> Q256 {
    match region(x) {
        Region::T => taylor(x),
        Region::YA | Region::YB => asym(x),
        Region::N => neg(x),
    }
}

pub(super) fn taylor(x: f64) -> Q256 {
    let (idx, c, h, _) = t_reduce(x);
    let a0 = q(F_AT_C[idx]);
    if h == 0.0 {
        return a0;
    }
    taylor_at(idx, c, Q256::from_f64(h))
}

/// Positive erfcx at an extended argument, retaining the input's low bits.
pub(crate) fn positive(x: Q256) -> Q256 {
    if x.cmp_abs(Q256::from_f64(16.0)) != core::cmp::Ordering::Less {
        return asym_value(x);
    }
    // A rounded lookup argument may cross a cell boundary. Keep the true
    // Q256 argument inside the Taylor theorem's |h| <= 1/8 domain, including
    // values immediately below 16 that round to 16 in binary64.
    let high = x.to_f64().min(f64::from_bits(16.0_f64.to_bits() - 1));
    let (mut idx, mut c, _, _) = t_reduce(high);
    let mut h = x.add(Q256::from_f64(c).neg());
    if h.cmp_abs(Q256::from_f64(0.125)) == core::cmp::Ordering::Greater {
        (idx, c, _, _) = t_reduce(high.next_down());
        h = x.add(Q256::from_f64(c).neg());
    }
    taylor_at(idx, c, h)
}

fn taylor_at(idx: usize, c: f64, hq: Q256) -> Q256 {
    let a0 = q(F_AT_C[idx]);
    let cq = Q256::from_f64(c);
    let a1 = cq.mul(a0).add(cq.mul(a0)).add(q(C2).neg());
    let mut sum = a0.add(a1.mul(hq));
    let lim = a0.top() - 262;
    let (mut prev, mut cur, mut hp) = (a0, a1, hq);
    let mut small = 0;
    for &reciprocal in RECIP.iter().take(99).skip(1) {
        let two_c_cur = cq.mul(cur);
        let next = two_c_cur
            .add(two_c_cur)
            .add(prev.add(prev))
            .mul(q(reciprocal));
        hp = hp.mul(hq);
        let term = next.mul(hp);
        sum = sum.add(term);
        if term.top() < lim {
            small += 1;
            if small == 2 {
                break;
            }
        } else {
            small = 0;
        }
        prev = cur;
        cur = next;
    }
    sum
}

pub(crate) fn asym(x: f64) -> Q256 {
    asym_value(Q256::from_f64(x))
}

pub(crate) fn asym_value(xq: Q256) -> Q256 {
    let y = xq.recip();
    let t = y.mul(y);
    let half = Q256::from_f64(0.5);
    let t = t.mul(half);
    let mut sum = Q256::ONE;
    let mut term = Q256::ONE;
    for k in 1..400 {
        term = term.mul(t).mul(Q256::from_f64((2 * k - 1) as f64)).neg();
        if term.top() < -262 {
            break;
        }
        sum = sum.add(term);
    }
    sum.mul(y).mul(q(CS))
}

pub(super) fn neg(x: f64) -> Q256 {
    let (s, se) = two_prod(x, x);
    let big = reflected_exponential(s, se);
    let g = if -x < 16.0 { taylor(-x) } else { asym(-x) };
    big.add(g.neg())
}

/// Twice the exponential of an exact double-word square.
#[inline]
pub(crate) fn reflected_exponential(s: f64, se: f64) -> Q256 {
    let n = (s * INV_L + SHIFTER) - SHIFTER;
    let n_int = n as i32;
    let j = n_int.rem_euclid(128) as usize;
    let k = n_int.div_euclid(128);
    let r = Q256::from_f64(s)
        .add(Q256::from_f64(se))
        .add(Q256::from_f64(n).mul(q(LN2_128)).neg());
    let mut hh = Q256::ONE;
    for level in (1..=24).rev() {
        hh = Q256::ONE.add(r.mul(q(RECIP[level - 1])).mul(hh));
    }
    let big = q(T2[j]).mul(hh);
    big.mul_pow2(k + 1)
}
