//! Binary exponential stages, with the scalar reduction and evaluation order.

use morphiq_numerics_arch::Simd;

use super::exp2;
use super::stages::{E_A, E_B, FLOOR, LIMIT, SHIFTER};
use super::tables::{LN2_HI, LN2_LO};
use crate::exp::lanes::{Table, decide, stage_a_at, stage_b_at, table};
use crate::lanes::{Dw, Kernel, lanes_mask, mask_from, two_prod};

pub(crate) struct Exp2;

impl Kernel for Exp2 {
    fn scalar(x: f64) -> f64 {
        exp2(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let r = reduce(k, &x);
        let open = lanes_mask::<K>() & !r.screened;
        let (mut low, a) = decide(k, stage_a(k, &r), E_A);
        let mut decided = a & open;
        if open & !decided != 0 {
            let (b, accepted) = decide(k, stage_b(k, &r), E_B);
            let take = open & !decided & accepted;
            low = k.select(mask_from(k, take), b, low);
            decided |= take;
        }
        let mut out = k.store(k.mul(low, r.table.scale));
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if decided >> i & 1 == 0 {
                *o = exp2(x.as_ref()[i]);
            }
        }
        out
    }
}

struct Reduced<K: Simd> {
    d: K::F,
    table: Table<K>,
    screened: u64,
}

#[inline(always)]
fn reduce<K: Simd>(k: K, x: &K::Array) -> Reduced<K> {
    let x = k.load(*x);
    let active = k.and_m(
        k.le(k.splat(f64::from_bits(FLOOR)), k.abs(x)),
        k.lt(k.abs(x), k.splat(f64::from_bits(LIMIT))),
    );
    // Every evaluated lane must meet two_prod's hypotheses, even if ignored.
    let x = k.select(active, x, k.splat(0.0));
    let screened = !k.mask_bits(active) & lanes_mask::<K>();
    let t = k.add(k.mul(x, k.splat(512.0)), k.splat(SHIFTER));
    let n = k.sub(t, k.splat(SHIFTER));
    Reduced {
        d: k.sub(x, k.mul(n, k.splat(1.0 / 512.0))),
        table: table(k, t, screened),
        screened,
    }
}

#[inline(always)]
fn stage_a<K: Simd>(k: K, r: &Reduced<K>) -> Dw<K> {
    stage_a_at(k, &r.table, k.mul(r.d, k.splat(LN2_HI)))
}

#[inline(always)]
fn stage_b<K: Simd>(k: K, r: &Reduced<K>) -> Dw<K> {
    // d is zero or |d| >= 2^-62, and |d| <= 2^-10; LN2_HI is in (1/2, 1).
    // Thus the exact product is zero or >= 2^-63, within two_prod's domain.
    let (p, e) = two_prod(k, r.d, k.splat(LN2_HI));
    let rl = k.add(e, k.mul(r.d, k.splat(LN2_LO)));
    let rh = k.sub(k.add(p, k.splat(6144.0)), k.splat(6144.0));
    let rt = k.add(k.sub(p, rh), rl);
    stage_b_at(k, &r.table, rh, rt)
}

#[cfg(test)]
mod tests;
