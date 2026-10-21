//! `asin` on lanes ([`docs/lanes.md`] §5): `asin`'s screen, `Reduced::of`,
//! `series`, the fast path and its rounding test, operation for operation,
//! with the scalar function for every lane the screen or the test sends
//! elsewhere.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{HALF_PI, POLY0, SEGMENTS};
use super::{ASIN_IS_X, EPS, SHIFTER, SPLIT, asin};
use crate::exact::sqrt;
use crate::lanes::{
    Dw, Kernel, add_dw, add_f64, decide_relative, fast_two_sum, lanes_mask, two_prod, two_sum,
};

/// `asin` as a lane kernel.
pub(crate) struct Asin;

/// `Reduced::of` on every lane of `a`, which holds `x` in `[ASIN_IS_X, 1)` on
/// the live lanes: the double-word `z` of `Reduced::Direct` or
/// `Reduced::Complement`, by `comp`. The square root is the scalar function,
/// per lane, exactly as `Reduced::of` calls it; dead lanes carry a harmless
/// finite argument.
#[inline(always)]
fn reduce<K: Simd>(k: K, a: K::F, comp: K::M) -> Dw<K> {
    let u = k.mul(k.sub(k.splat(1.0), a), k.splat(0.5));
    let comp_bits = k.mask_bits(comp);
    let s = if comp_bits == 0 {
        k.splat(1.0)
    } else {
        // The root only on the complement's lanes; the others carry 1.
        let mut roots = k.store(u);
        for (lane, r) in roots.as_mut().iter_mut().enumerate() {
            *r = if comp_bits >> lane & 1 == 1 {
                sqrt(*r)
            } else {
                1.0
            };
        }
        k.load(roots)
    };
    let (square, square_error) = two_prod(k, s, s);
    let residual = k.sub(k.sub(u, square), square_error);
    let (hi, lo) = two_sum(k, s, k.div(residual, k.mul(k.splat(2.0), s)));
    (k.select(comp, hi, a), k.select(comp, lo, k.splat(0.0)))
}

/// `series` on every lane of the double-word `(z_hi, z_lo)`: both branches in
/// lanes, selected by whether `i` is zero.
#[inline(always)]
fn series<K: Simd>(k: K, (z_hi, z_lo): Dw<K>) -> Dw<K> {
    let i = k.sub(
        k.add(k.mul(z_hi, k.splat(64.0)), k.splat(SHIFTER)),
        k.splat(SHIFTER),
    );
    // i is an integer, so i == 0 exactly when i < 1/2.
    let below = k.lt(i, k.splat(0.5));
    let below_bits = k.mask_bits(below);
    // The series below 1/128, only if some lane is there.
    let small = if below_bits == 0 {
        (z_hi, z_lo)
    } else {
        let z2 = k.mul(z_hi, z_hi);
        let [p0, p1, p2, p3] = POLY0;
        let p = k.add(
            k.splat(p0),
            k.mul(
                z2,
                k.add(
                    k.splat(p1),
                    k.mul(z2, k.add(k.splat(p2), k.mul(z2, k.splat(p3)))),
                ),
            ),
        );
        add_f64(k, (z_hi, z_lo), k.mul(k.mul(z_hi, z2), p))
    };
    if below_bits == lanes_mask::<K>() {
        return small;
    }
    // The table rows, a lane at a time; a lane with i = 0 reads row 1 and is
    // discarded.
    let mut rows = [K::Array::default(); 13];
    for (lane, index) in k.store(i).as_ref().iter().enumerate() {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 0 <= i <= 45
        let row = SEGMENTS[(*index as usize).max(1) - 1];
        for (column, word) in rows.iter_mut().zip(row) {
            column.as_mut()[lane] = word;
        }
    }
    let [y_hi, y_lo, c_hi, c_lo, g0, g1, g2, g3, g4, g5, g6, g7, g8] = rows.map(|a| k.load(a));
    // t = z - i/64, with z_hi - i/64 exact for i >= 1.
    let (t_hi, t_lo) = two_sum(k, k.sub(z_hi, k.mul(i, k.splat(0.015_625))), z_lo);
    let horner = |c: K::F, rest: K::F| k.add(c, k.mul(t_hi, rest));
    let g = horner(
        g0,
        horner(
            g1,
            horner(
                g2,
                horner(g3, horner(g4, horner(g5, horner(g6, horner(g7, g8))))),
            ),
        ),
    );
    let (p_hi, p_lo) = two_prod(k, t_hi, c_hi);
    let tail = k.add(
        k.add(p_lo, k.add(k.mul(t_hi, c_lo), k.mul(t_lo, c_hi))),
        k.mul(k.mul(t_hi, t_hi), g),
    );
    let table = add_dw(k, two_sum(k, y_hi, y_lo), fast_two_sum(k, p_hi, tail));
    (
        k.select(below, small.0, table.0),
        k.select(below, small.1, table.1),
    )
}

/// `Reduced::fast`'s `y` on every lane.
#[inline(always)]
fn fast<K: Simd>(k: K, z: Dw<K>, comp: K::M) -> Dw<K> {
    let s = series(k, z);
    if k.mask_bits(comp) == 0 {
        return s;
    }
    // delta = series(z) * 2, as DoubleWord::mul_f64 rounds it.
    let (c_hi, c_lo1) = two_prod(k, s.0, k.splat(2.0));
    let (t_hi, t_lo1) = fast_two_sum(k, c_hi, k.mul(s.1, k.splat(2.0)));
    let delta = fast_two_sum(k, t_hi, k.add(t_lo1, c_lo1));
    let half_pi = two_sum(k, k.splat(HALF_PI.0), k.splat(HALF_PI.1));
    let y = add_dw(k, half_pi, (k.neg(delta.0), k.neg(delta.1)));
    (k.select(comp, y.0, s.0), k.select(comp, y.1, s.1))
}

impl Kernel for Asin {
    fn scalar(x: f64) -> f64 {
        asin(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let x = k.load(x);
        let a = k.abs(x);
        // asin's own screen: a NaN, |x| >= 1 and |x| < ASIN_IS_X are the
        // scalar function's. NaN fails both comparisons below.
        let live = k.and_m(k.lt(a, k.splat(1.0)), k.not_m(k.lt(a, k.splat(ASIN_IS_X))));
        let live_bits = k.mask_bits(live);
        let a = k.select(live, a, k.splat(0.5));
        let comp = k.lt(k.splat(SPLIT), a);
        let y = fast(k, reduce(k, a, comp), comp);
        let decided = decide_relative(k, y, EPS) & live_bits;
        let sign = k.and_u(k.to_bits(x), k.splat_bits(1 << 63));
        let mut out = k.store(k.to_float(k.or_u(k.to_bits(y.0), sign)));
        if decided != lanes_mask::<K>() {
            let xs = k.store(x);
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = asin(xs.as_ref()[i]);
                }
            }
        }
        out
    }
}
