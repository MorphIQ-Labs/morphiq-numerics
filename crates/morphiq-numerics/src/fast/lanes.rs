//! Scalar operation sequences through the library's existing SIMD dispatch.
use crate::lanes::{Kernel, lanes_mask};
use morphiq_numerics_arch::Simd;

/// The public bounded erfcx on lanes: the table polynomial where the scalar
/// screen accepts, the strong owner for every other lane.
pub(crate) struct Erfcx;

impl Kernel for Erfcx {
    fn scalar(x: f64) -> f64 {
        super::normal::erfcx(x)
    }
    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let x = k.load(input);
        // The scalar screen's comparisons; a NaN lane fails them.
        let active = k.and_m(
            k.and_m(k.le(k.splat(-0.5), x), k.lt(x, k.splat(16.0))),
            k.le(k.splat(super::normal::MIN_MAGNITUDE), k.abs(x)),
        );
        let active_bits = k.mask_bits(active);
        let mut out = K::Array::default();
        if active_bits != 0 {
            // Inactive lanes evaluate the table at 1, inside its domain.
            let safe = k.select(active, x, k.splat(1.0));
            out = k.store(crate::erfcx::bounded::lanes(k, safe));
        }
        if active_bits != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::erfcx(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

pub(crate) struct Cdf;

impl Kernel for Cdf {
    fn scalar(x: f64) -> f64 {
        super::normal::norm_cdf(x)
    }
    #[inline(always)]
    fn lanes<K: Simd>(k: K, input: K::Array) -> K::Array {
        let x = k.load(input);
        let a = k.abs(x);
        let active = k.and_m(
            k.le(k.splat(super::normal::MIN_MAGNITUDE), a),
            k.le(a, k.splat(8.0)),
        );
        let central = k.and_m(active, k.le(a, k.splat(1.0)));
        let tail = k.and_m(active, k.not_m(central));
        let mut y = k.splat(0.0);
        if k.mask_bits(central) != 0 {
            y = center(k, k.select(central, x, k.splat(0.0)));
        }
        if k.mask_bits(tail) != 0 {
            let safe = k.select(tail, a, k.splat(1.0));
            // Active magnitudes are at most 8; other lanes use 1. Thus every
            // rounded exponent is in [-32, 0] (fast_normal_exponent_ok).
            let exponential =
                crate::exp::bounded::in_domain_lanes(k, k.mul(k.mul(k.splat(-0.5), safe), safe));
            let scaled = k.mul(safe, k.splat(crate::normal_distribution::INV_SQRT2_HIGH));
            let lower = k.mul(
                k.mul(k.splat(0.5), exponential),
                crate::erfcx::bounded::lanes(k, scaled),
            );
            let value = k.select(k.lt(x, k.splat(0.0)), lower, k.sub(k.splat(1.0), lower));
            y = k.select(tail, value, y);
        }
        let mut out = k.store(y);
        let active_bits = k.mask_bits(active);
        if active_bits != lanes_mask::<K>() {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if active_bits >> i & 1 == 0 {
                    *value = crate::normal::norm_cdf(input.as_ref()[i]);
                }
            }
        }
        out
    }
}

#[inline(always)]
fn center<K: Simd>(k: K, x: K::F) -> K::F {
    use crate::normal_distribution::{CENTER_HIGH as A, DENSITY_HIGH};
    let z = k.mul(x, x);
    let zz = k.mul(z, z);
    let pair = |j: usize| k.add(k.splat(A[j]), k.mul(z, k.splat(A[j + 1])));
    let p0 = pair(0);
    let p1 = pair(2);
    let p2 = pair(4);
    let p3 = pair(6);
    let p4 = pair(8);
    let p5 = pair(10);
    let mut p = k.add(p5, k.mul(zz, k.splat(A[12])));
    for q in [p4, p3, p2, p1, p0] {
        p = k.add(q, k.mul(zz, p));
    }
    k.add(k.splat(0.5), k.mul(k.mul(x, k.splat(DENSITY_HIGH)), p))
}
