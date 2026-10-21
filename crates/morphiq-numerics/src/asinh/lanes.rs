//! `asinh` on lanes ([`docs/lanes.md`] §5): `asinh`'s screen, the series, the
//! logarithm of `x + √(x² + 1)`, the large form and the rounding test,
//! operation for operation, with the scalar function for every lane the
//! screen or the test doesn't settle.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::tables::{LN2, POLY0};
use super::{ASINH_IS_X, EPS, TWO_28, TWO_M7, asinh};
use crate::lanes::{Dw, Kernel, add_dw, add_f64, decide_relative, lanes_mask, two_prod, two_sum};
use crate::ln::lanes::fallback;
use crate::sqrt::sqrt;

/// `asinh` as a lane kernel.
pub(crate) struct Asinh;

/// `series` on every lane of `a`.
#[inline(always)]
fn series<K: Simd>(k: K, a: K::F) -> Dw<K> {
    let a2 = k.mul(a, a);
    let [p0, p1, p2, p3] = POLY0;
    let p = k.add(
        k.splat(p0),
        k.mul(
            a2,
            k.add(
                k.splat(p1),
                k.mul(a2, k.add(k.splat(p2), k.mul(a2, k.splat(p3)))),
            ),
        ),
    );
    add_f64(k, (a, k.splat(0.0)), k.mul(k.mul(a, a2), p))
}

/// `logarithm` on every lane of `a`, which holds `x` in `[2^-7, 2^28)` on the
/// lanes that count and a harmless value elsewhere. The square root is the
/// scalar function, per lane, as `logarithm` calls it.
#[inline(always)]
fn logarithm<K: Simd>(k: K, a: K::F) -> Dw<K> {
    let (square, square_error) = two_prod(k, a, a);
    let u = add_f64(k, two_sum(k, k.splat(1.0), square), square_error);
    let mut roots = k.store(u.0);
    for r in roots.as_mut() {
        *r = sqrt(*r);
    }
    let root = k.load(roots);
    let (root_square, root_square_error) = two_prod(k, root, root);
    let residual = k.add(k.sub(k.sub(u.0, root_square), root_square_error), u.1);
    let s = two_sum(k, root, k.div(residual, k.mul(k.splat(2.0), root)));
    let v = add_f64(k, two_sum(k, a, s.0), s.1);
    add_f64(k, fallback::ln(k, v.0), k.div(v.1, v.0))
}

/// `large` on every lane of `a`, `x ≥ 2^28` on the lanes that count.
#[inline(always)]
fn large<K: Simd>(k: K, a: K::F) -> Dw<K> {
    let ln_2x = add_dw(
        k,
        fallback::ln(k, a),
        two_sum(k, k.splat(LN2.0), k.splat(LN2.1)),
    );
    add_f64(k, ln_2x, k.div(k.div(k.splat(0.25), a), a))
}

impl Kernel for Asinh {
    fn scalar(x: f64) -> f64 {
        asinh(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let x = k.load(x);
        let a = k.abs(x);
        // asinh's own screen: a NaN, ±0, ±∞ and |x| up to the threshold are the
        // scalar function's. NaN fails both comparisons.
        let live = k.and_m(
            k.lt(k.splat(ASINH_IS_X), a),
            k.lt(a, k.splat(f64::INFINITY)),
        );
        let live_bits = k.mask_bits(live);
        let small = k.and_m(live, k.lt(a, k.splat(TWO_M7)));
        let big = k.and_m(live, k.le(k.splat(TWO_28), a));
        let middle = k.and_m(live, k.not_m(k.or_m(small, big)));
        let (small_bits, middle_bits, big_bits) =
            (k.mask_bits(small), k.mask_bits(middle), k.mask_bits(big));
        let mut y = (k.splat(1.0), k.splat(0.0));
        if small_bits != 0 {
            let s = series(k, k.select(small, a, k.splat(1.0)));
            y = (k.select(small, s.0, y.0), k.select(small, s.1, y.1));
        }
        if middle_bits != 0 {
            let m = logarithm(k, k.select(middle, a, k.splat(1.0)));
            y = (k.select(middle, m.0, y.0), k.select(middle, m.1, y.1));
        }
        if big_bits != 0 {
            let b = large(
                k,
                k.select(big, a, k.splat(f64::from_bits(0x41d0_0000_0000_0000))),
            );
            y = (k.select(big, b.0, y.0), k.select(big, b.1, y.1));
        }
        let decided = decide_relative(k, y, EPS) & live_bits;
        let sign = k.and_u(k.to_bits(x), k.splat_bits(1 << 63));
        let mut out = k.store(k.to_float(k.or_u(k.to_bits(y.0), sign)));
        if decided != lanes_mask::<K>() {
            let xs = k.store(x);
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    *o = asinh(xs.as_ref()[i]);
                }
            }
        }
        out
    }
}
