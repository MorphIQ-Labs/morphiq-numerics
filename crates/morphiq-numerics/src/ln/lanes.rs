//! `ln` and `ln_1p` on lanes ([`docs/lanes.md`] §5): their screens,
//! `Reduced::of` per lane, `ln_1p_double_word`, `fast_value` and `decide`,
//! operation for operation, with the scalar function on every lane they don't
//! decide.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{LN2_HI, LN2_LO, NEG_LN_R_BITS, POLY};
use super::{EPS, Reduced, TWO_53, TWO_M7, TWO_M54, ln, ln_1p};
use crate::lanes::{Dw, Kernel, decide, dw_add, dw_add_f64, two_prod, two_sum};

/// `ln` as a lane kernel.
pub(crate) struct Ln;

/// `ln_1p` as a lane kernel.
pub(crate) struct Ln1p;

/// `Reduced::of` on each lane of `x` whose bit in `skip` is clear, gathered
/// into lanes: `(y, R[i], E, −ln R[i] as a double-word)`. A skipped lane gets
/// the reduction of 1, and is discarded.
#[inline(always)]
fn reduce<K: Simd>(k: K, x: &K::Array, skip: u64) -> (K::F, K::F, K::F, Dw<K>) {
    let (mut y, mut r, mut e, mut n_hi, mut n_lo) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for i in 0..K::LANES {
        let xi = if skip >> i & 1 == 0 {
            x.as_ref()[i]
        } else {
            1.0
        };
        let reduced = Reduced::of(xi);
        y.as_mut()[i] = reduced.y;
        r.as_mut()[i] = reduced.r;
        e.as_mut()[i] = f64::from(reduced.e);
        let (hi, lo) = NEG_LN_R_BITS[reduced.i];
        n_hi.as_mut()[i] = f64::from_bits(hi);
        n_lo.as_mut()[i] = f64::from_bits(lo);
    }
    (
        k.load(y),
        k.load(r),
        k.load(e),
        (k.load(n_hi), k.load(n_lo)),
    )
}

/// `Reduced::fast_value` from the gathered reduction: `ln_y_fast`, then the
/// `E·ln 2` term.
#[inline(always)]
fn fast_value<K: Simd>(k: K, (y, r, e, neg_ln_r): (K::F, K::F, K::F, Dw<K>)) -> Dw<K> {
    // ln_y_fast: z = y·R[i] − 1 exactly, as a double-word.
    let (p, q) = two_prod(k, y, r);
    let ln_1p_z = ln_1p_double_word(k, two_sum(k, k.sub(p, k.splat(1.0)), q));
    let ln_y = dw_add(k, two_sum(k, neg_ln_r.0, neg_ln_r.1), ln_1p_z);
    let e_ln2 = two_sum(k, k.mul(e, k.splat(LN2_HI)), k.mul(e, k.splat(LN2_LO)));
    dw_add(k, e_ln2, ln_y)
}

/// `ln_1p_double_word`, operation for operation.
#[inline(always)]
fn ln_1p_double_word<K: Simd>(k: K, z: Dw<K>) -> Dw<K> {
    let (z_hi, z_lo) = z;
    let [c3, c4, c5, c6, c7, c8, c9] = POLY;
    let w8 = k.add(k.splat(c8), k.mul(z_hi, k.splat(c9)));
    let w7 = k.add(k.splat(c7), k.mul(z_hi, w8));
    let w6 = k.add(k.splat(c6), k.mul(z_hi, w7));
    let w5 = k.add(k.splat(c5), k.mul(z_hi, w6));
    let w4 = k.add(k.splat(c4), k.mul(z_hi, w5));
    let w = k.add(k.splat(c3), k.mul(z_hi, w4));
    let (s_hi, s_lo) = two_prod(k, z_hi, z_hi);
    let t = k.mul(k.mul(z_hi, s_hi), w);
    let b = two_sum(k, k.mul(k.splat(-0.5), s_hi), k.mul(k.splat(-0.5), s_lo));
    let v = k.sub(t, k.mul(z_hi, z_lo));
    dw_add_f64(k, dw_add(k, z, b), v)
}

/// `y_hi` on each lane `decide` accepts and outside `scalar_lanes`, `scalar`
/// on every other.
#[inline(always)]
fn finish<K: Simd>(
    k: K,
    x: &K::Array,
    y: Dw<K>,
    scalar_lanes: u64,
    scalar: fn(f64) -> f64,
) -> K::Array {
    let decided = k.mask_bits(decide(k, y, EPS)) & !scalar_lanes;
    let mut out = k.store(y.0);
    for (i, o) in out.as_mut().iter_mut().enumerate() {
        if decided >> i & 1 == 0 {
            *o = scalar(x.as_ref()[i]);
        }
    }
    out
}

impl Kernel for Ln {
    fn scalar(x: f64) -> f64 {
        ln(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        // ln's screen: NaN, x < 0, ±0, +∞ and 1 are returned by `ln` itself.
        let (y, scalar_lanes) = fast_ln(k, &x);
        finish(k, &x, y, scalar_lanes, ln)
    }
}

/// `ln`'s fast value on every lane, `Reduced::fast_value`, and the lanes (bit
/// `i` set) that `ln` screens out: NaN, `x ≤ 0`, `+∞` and 1.
#[inline(always)]
pub(super) fn fast_ln<K: Simd>(k: K, x: &K::Array) -> (Dw<K>, u64) {
    let mut scalar_lanes = 0_u64;
    for (i, &xi) in x.as_ref().iter().enumerate() {
        if !(xi > 0.0 && xi < f64::INFINITY) || xi == 1.0 {
            scalar_lanes |= 1 << i;
        }
    }
    (fast_value(k, reduce(k, x, scalar_lanes)), scalar_lanes)
}

impl Kernel for Ln1p {
    fn scalar(x: f64) -> f64 {
        ln_1p(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let (y, scalar_lanes, _) = fast_ln_1p(k, &x);
        finish(k, &x, y, scalar_lanes, ln_1p)
    }
}

/// `ln_1p`'s fast value on every lane: case A's `ln_1p_double_word(x)`, or
/// case B's `fast_value` at `h` plus `l/h`; the lanes (bit `i` set) that
/// `ln_1p` screens out, and the case-A lanes.
#[inline(always)]
pub(super) fn fast_ln_1p<K: Simd>(k: K, x: &K::Array) -> (Dw<K>, u64, u64) {
    // ln_1p's screen: NaN, x ≤ −1, +∞ and |x| < 2^−54 are returned by
    // `ln_1p` itself. Below 2^−7 is case A (z = x), from it case B.
    let (mut scalar_lanes, mut case_a) = (0_u64, 0_u64);
    for (i, &xi) in x.as_ref().iter().enumerate() {
        if !(xi > -1.0 && xi < f64::INFINITY) || xi.abs() < TWO_M54 {
            scalar_lanes |= 1 << i;
        }
        if xi.abs() < TWO_M7 {
            case_a |= 1 << i;
        }
    }
    let xv = k.load(*x);
    // Case B: split, 1 + x = h + l exactly.
    let (sum_hi, sum_lo) = two_sum(k, k.splat(1.0), xv);
    let below = k.lt(xv, k.splat(TWO_53));
    let h = k.select(below, sum_hi, xv);
    let l = k.select(below, sum_lo, k.splat(1.0));
    let (y, r, e, neg_ln_r) = reduce(k, &k.store(h), scalar_lanes | case_a);
    let (p, q) = two_prod(k, y, r);
    let z_b = two_sum(k, k.sub(p, k.splat(1.0)), q);
    // Case A takes z = x exactly: the same ln_1p_double_word, on (x, 0).
    let a = case_a_mask(k, case_a);
    let z = (k.select(a, xv, z_b.0), k.select(a, k.splat(0.0), z_b.1));
    let ln_1p_z = ln_1p_double_word(k, z);
    // Case B continues as fast_value, then adds l/h.
    let ln_y = dw_add(k, two_sum(k, neg_ln_r.0, neg_ln_r.1), ln_1p_z);
    let e_ln2 = two_sum(k, k.mul(e, k.splat(LN2_HI)), k.mul(e, k.splat(LN2_LO)));
    let y_b = dw_add_f64(k, dw_add(k, e_ln2, ln_y), k.div(l, h));
    let y = (k.select(a, ln_1p_z.0, y_b.0), k.select(a, ln_1p_z.1, y_b.1));
    (y, scalar_lanes, case_a)
}

/// The lanes whose bit in `bits` is set, as a lane mask.
#[inline(always)]
fn case_a_mask<K: Simd>(k: K, bits: u64) -> K::M {
    let mut words = K::Words::default();
    for (i, w) in words.as_mut().iter_mut().enumerate() {
        *w = bits >> i & 1;
    }
    k.eq_u(k.load_bits(words), k.splat_bits(1))
}

#[cfg(test)]
mod tests;
