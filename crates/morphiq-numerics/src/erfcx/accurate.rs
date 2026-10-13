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
    let cq = Q256::from_f64(c);
    let hq = Q256::from_f64(h);
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

pub(super) fn asym(x: f64) -> Q256 {
    let xq = Q256::from_f64(x);
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
    let big = big.mul_pow2(k + 1);
    let g = if -x < 16.0 { taylor(-x) } else { asym(-x) };
    big.add(g.neg())
}
