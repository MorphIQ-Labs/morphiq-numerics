//! `atan2` on lanes ([`docs/lanes.md`] §5): `atan2`'s screen, the scaled
//! double-word ratio, `atan t`'s table and series, the four forms and the
//! rounding test, operation for operation, with the scalar function for every
//! lane the screen or the test doesn't settle.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{HALF_PI, POLY0, SEGMENTS};
use super::{EPS, SHIFTER, TINY, atan2};
use crate::lanes::{
    Dw, Kernel2, add_dw, add_f64, decide_relative, fast_two_sum, lanes_mask, two_prod, two_sum,
};

/// `atan2` as a lane kernel.
pub(crate) struct Atan2;

/// `2^900` and `2^-900`: the lanes served here have `d` between them, where
/// the scale `2^-e` and its inverse are normal binary64 numbers.
const TWO_900: f64 = f64::from_bits(0x7830_0000_0000_0000);
const TWO_M900: f64 = f64::from_bits(0x07b0_0000_0000_0000);

/// `series` on every lane of the double-word `(t_hi, t_lo)`, `t` in `(0, 1]`.
#[inline(always)]
fn series<K: Simd>(k: K, (t_hi, t_lo): Dw<K>) -> Dw<K> {
    let i = k.sub(
        k.add(k.mul(t_hi, k.splat(64.0)), k.splat(SHIFTER)),
        k.splat(SHIFTER),
    );
    // i is an integer, so i == 0 exactly when i < 1/2.
    let below = k.lt(i, k.splat(0.5));
    let t2 = k.mul(t_hi, t_hi);
    let [p0, p1, p2, p3] = POLY0;
    let p = k.add(
        k.splat(p0),
        k.mul(
            t2,
            k.add(
                k.splat(p1),
                k.mul(t2, k.add(k.splat(p2), k.mul(t2, k.splat(p3)))),
            ),
        ),
    );
    let small = add_f64(k, (t_hi, t_lo), k.mul(k.mul(t_hi, t2), p));
    // The table rows, a lane at a time; a lane with i = 0 reads row 1 and is
    // discarded.
    let mut rows = [K::Array::default(); 13];
    for (lane, index) in k.store(i).as_ref().iter().enumerate() {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 0 <= i <= 64
        let row = SEGMENTS[(*index as usize).clamp(1, 64) - 1];
        for (column, word) in rows.iter_mut().zip(row) {
            column.as_mut()[lane] = word;
        }
    }
    let [y_hi, y_lo, c_hi, c_lo, g0, g1, g2, g3, g4, g5, g6, g7, g8] = rows.map(|a| k.load(a));
    let (s_hi, s_lo) = two_sum(k, k.sub(t_hi, k.mul(i, k.splat(0.015_625))), t_lo);
    let horner = |c: K::F, rest: K::F| k.add(c, k.mul(s_hi, rest));
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
    let (p_hi, p_lo) = two_prod(k, s_hi, c_hi);
    let tail = k.add(
        k.add(p_lo, k.add(k.mul(s_hi, c_lo), k.mul(s_lo, c_hi))),
        k.mul(k.mul(s_hi, s_hi), g),
    );
    let table = add_dw(k, two_sum(k, y_hi, y_lo), fast_two_sum(k, p_hi, tail));
    (
        k.select(below, small.0, table.0),
        k.select(below, small.1, table.1),
    )
}

impl Kernel2 for Atan2 {
    fn scalar(y: f64, x: f64) -> f64 {
        atan2(y, x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, y: K::Array, x: K::Array) -> K::Array {
        let (y, x) = (k.load(y), k.load(x));
        let (a, b) = (k.abs(y), k.abs(x));
        let swap = k.lt(b, a);
        let n = k.select(swap, b, a);
        let d = k.select(swap, a, b);
        // atan2's own screen: NaNs, zeros and infinities, and the pairs whose
        // scale or ratio is outside the lanes' range, are the scalar function's.
        let live = k.and_m(
            k.and_m(k.le(k.splat(TWO_M900), d), k.le(d, k.splat(TWO_900))),
            k.le(k.mul(d, k.splat(TINY)), n),
        );
        let live = k.and_m(live, k.le(n, d));
        let live_bits = k.mask_bits(live);
        let one = k.splat(1.0);
        let (n, d) = (k.select(live, n, one), k.select(live, d, one));
        // 2^-e, exact, from d's exponent field: d' = d·2^-e ∈ [1, 2).
        let scale = k.to_float(k.sub_u(
            k.splat_bits(2046 << 52),
            k.and_u(k.to_bits(d), k.splat_bits(0x7ff0_0000_0000_0000)),
        ));
        let (ns, ds) = (k.mul(n, scale), k.mul(d, scale));
        let q = k.div(ns, ds);
        let (p, p_error) = two_prod(k, q, ds);
        let residual = k.sub(k.sub(ns, p), p_error);
        let t = fast_two_sum(k, q, k.div(residual, ds));
        let phi = series(k, t);
        let sign_bit = k.splat_bits(1 << 63);
        let negative = k.eq_u(k.and_u(k.to_bits(x), sign_bit), sign_bit);
        // Each form only if some lane takes it.
        let (minus_lanes, plus_lanes, pi_lanes) = (
            k.and_m(swap, k.not_m(negative)),
            k.and_m(swap, negative),
            k.and_m(k.not_m(swap), negative),
        );
        let (mut hi, mut lo) = phi;
        let half_pi = two_sum(k, k.splat(HALF_PI.0), k.splat(HALF_PI.1));
        if k.mask_bits(minus_lanes) != 0 {
            let minus = add_dw(k, half_pi, (k.neg(phi.0), k.neg(phi.1)));
            hi = k.select(minus_lanes, minus.0, hi);
            lo = k.select(minus_lanes, minus.1, lo);
        }
        if k.mask_bits(plus_lanes) != 0 {
            let plus = add_dw(k, half_pi, phi);
            hi = k.select(plus_lanes, plus.0, hi);
            lo = k.select(plus_lanes, plus.1, lo);
        }
        if k.mask_bits(pi_lanes) != 0 {
            // pi = half_pi.mul_f64(2.0), as DoubleWord::mul_f64 rounds it.
            let (c_hi, c_lo1) = two_prod(k, half_pi.0, k.splat(2.0));
            let (t_hi, t_lo1) = fast_two_sum(k, c_hi, k.mul(half_pi.1, k.splat(2.0)));
            let pi = fast_two_sum(k, t_hi, k.add(t_lo1, c_lo1));
            let pi_minus = add_dw(k, pi, (k.neg(phi.0), k.neg(phi.1)));
            hi = k.select(pi_lanes, pi_minus.0, hi);
            lo = k.select(pi_lanes, pi_minus.1, lo);
        }
        let angle = (hi, lo);
        let decided = decide_relative(k, angle, EPS) & live_bits;
        let sign = k.and_u(k.to_bits(y), sign_bit);
        let mut out = k.store(k.to_float(k.or_u(k.to_bits(angle.0), sign)));
        if decided != lanes_mask::<K>() {
            let (ys, xs) = (k.store(y), k.store(x));
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = atan2(ys.as_ref()[i], xs.as_ref()[i]);
                }
            }
        }
        out
    }
}
