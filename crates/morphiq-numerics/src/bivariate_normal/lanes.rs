//! The bivariate normal distribution function on lanes ([`docs/lanes.md`] §5):
//! the low-correlation quadrature, operation for operation, with the scalar
//! evaluator for every lane the screen doesn't admit (the closed-form and
//! high-correlation regimes, NaN and saturated pairs).
//!
//! The lanes use the library's own lane `exp` and `norm_cdf`, which return
//! the scalar functions' bits, so every lane's expression is the scalar
//! expression with the same grouping and the quadrature nodes accumulated in
//! node order.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{
    BivariateNormal, PRODUCT_EXACT_FLOOR, Regime, SATURATED_THRESHOLD, bivariate_norm_cdf,
};
use crate::exp::lanes::Exp;
use crate::lanes::{Kernel, mask_from, two_prod, two_sum};
use crate::normal_distribution::lanes::Normal;

/// The widest backend's lane count: the tables a chunk reads.
const MAX_LANES: usize = 8;

/// Where a batch's tables come from.
#[derive(Clone, Copy)]
pub(super) enum Correlations<'a> {
    /// Every pair at one table.
    One(&'a BivariateNormal),
    /// Pair `i` at correlation `rho[i]`; an invalid one gives NaN.
    Each(&'a [f64]),
}

impl Correlations<'_> {
    /// The scalar value of pair `(x, y)` at index `i`.
    fn scalar(self, i: usize, x: f64, y: f64) -> f64 {
        match self {
            Correlations::One(table) => table.cdf(x, y),
            Correlations::Each(rho) => bivariate_norm_cdf(x, y, rho[i]),
        }
    }
}

#[inline(always)]
fn exp_lanes<K: Simd>(k: K, v: K::F) -> K::F {
    k.load(Exp::lanes(k, k.store(v)))
}

#[inline(always)]
fn norm_cdf_lanes<K: Simd>(k: K, v: K::F) -> K::F {
    k.load(Normal::<1>::lanes(k, k.store(v)))
}

/// `clamp_to_probability` on every lane: NaN passes through.
#[inline(always)]
fn clamp_lanes<K: Simd>(k: K, v: K::F) -> K::F {
    let below = k.lt(v, k.splat(0.0));
    let above = k.lt(k.splat(1.0), v);
    k.select(below, k.splat(0.0), k.select(above, k.splat(1.0), v))
}

/// `v` on the lanes of `live`, else `0`: a dead lane carries a harmless
/// argument and is discarded.
#[inline(always)]
fn live_or_zero<K: Simd>(k: K, live: K::M, v: K::F) -> K::F {
    k.select(live, v, k.splat(0.0))
}

/// [`BivariateNormal::low`] on every lane of `live`, which is a subset of
/// the lanes whose table is in the low-correlation regime, with `x <= y`.
#[inline(always)]
fn low<K: Simd>(
    k: K,
    live_bits: u64,
    x: K::F,
    y: K::F,
    tables: &[&BivariateNormal; MAX_LANES],
) -> K::F {
    let live = mask_from(k, live_bits);
    let (x, y) = (live_or_zero(k, live, x), live_or_zero(k, live, y));
    let e1 = k.sub(x, y);
    let d = k.mul(e1, e1);
    let e2 = k.add(x, y);
    let m = k.mul(e2, e2);
    let widest = (0..K::LANES)
        .filter(|&lane| live_bits >> lane & 1 == 1)
        .map(|lane| tables[lane].nodes)
        .max()
        .unwrap_or(0);
    let (mut high, mut low) = (k.splat(0.0), k.splat(0.0));
    for node in 0..widest {
        let (mut kw, mut p, mut q) = (
            K::Array::default(),
            K::Array::default(),
            K::Array::default(),
        );
        let mut active = 0_u64;
        for (lane, table) in tables.iter().enumerate().take(K::LANES) {
            if live_bits >> lane & 1 == 1 && node < table.nodes {
                active |= 1 << lane;
                kw.as_mut()[lane] = table.kw[node];
                p.as_mut()[lane] = table.p[node];
                q.as_mut()[lane] = table.q[node];
            }
        }
        let active = mask_from(k, active);
        let arg = k.neg(k.add(k.mul(d, k.load(p)), k.mul(m, k.load(q))));
        let term = k.mul(k.load(kw), exp_lanes(k, live_or_zero(k, active, arg)));
        let (s, e) = two_sum(k, high, term);
        high = k.select(active, s, high);
        low = k.select(active, k.add(low, e), low);
    }
    let (hi, lo) = two_prod(k, norm_cdf_lanes(k, x), norm_cdf_lanes(k, y));
    let lo = k.select(k.le(k.splat(PRODUCT_EXACT_FLOOR), hi), lo, k.splat(0.0));
    let (sum, err) = two_sum(k, hi, high);
    clamp_lanes(k, k.add(sum, k.add(err, k.add(low, lo))))
}

/// `table.cdf(x, y)` for every lane of one chunk, each lane's bits, and the
/// lanes (bit `i` set) the vector code served rather than the scalar
/// function.
#[inline(always)]
fn chunk<K: Simd>(
    k: K,
    x: K::Array,
    y: K::Array,
    tables: &[&BivariateNormal; MAX_LANES],
) -> (K::Array, u64) {
    let (xv, yv) = (k.load(x), k.load(y));
    // The scalar ordering, `x <= y`; a NaN lane is the scalar function's.
    let ordered = k.le(xv, yv);
    let (xo, yo) = (k.select(ordered, xv, yv), k.select(ordered, yv, xv));
    // Not NaN, not saturated: NaN fails both ordered comparisons.
    let live = k.mask_bits(k.and_m(
        k.lt(k.splat(-SATURATED_THRESHOLD), xo),
        k.lt(yo, k.splat(SATURATED_THRESHOLD)),
    ));
    let mut low_bits = 0_u64;
    for (lane, table) in tables.iter().enumerate().take(K::LANES) {
        if live >> lane & 1 == 1 && table.regime == Regime::Low {
            low_bits |= 1 << lane;
        }
    }
    let mut result = k.splat(0.0);
    if low_bits != 0 {
        result = k.select(
            mask_from(k, low_bits),
            low(k, low_bits, xo, yo, tables),
            result,
        );
    }
    let mut out = k.store(result);
    // A NaN would come out of the scalar function with its own bits.
    let done = k.mask_bits(k.le(result, result)) & low_bits;
    for (lane, o) in out.as_mut().iter_mut().enumerate() {
        if done >> lane & 1 == 0 {
            *o = tables[lane].cdf(x.as_ref()[lane], y.as_ref()[lane]);
        }
    }
    (out, done)
}

/// Every whole chunk of backend `k`'s width at the start of the pairs.
struct Chunks<'a> {
    x: &'a [f64],
    y: &'a [f64],
    correlations: Correlations<'a>,
    out: &'a mut [f64],
}

impl WithSimd for Chunks<'_> {
    type Output = usize;
    #[inline(always)]
    fn with<K: Simd>(self, k: K) -> usize {
        if K::LANES == 1 {
            return 0;
        }
        let covered = self.x.len() - self.x.len() % K::LANES;
        // Any table serves a lane that is NaN or invalid: it is the scalar's.
        let independent = match BivariateNormal::new(0.0) {
            Ok(table) => table,
            Err(_) => unreachable!("0 is a valid correlation"),
        };
        for start in (0..covered).step_by(K::LANES) {
            let end = start + K::LANES;
            let (mut ax, mut ay) = (K::Array::default(), K::Array::default());
            ax.as_mut().copy_from_slice(&self.x[start..end]);
            ay.as_mut().copy_from_slice(&self.y[start..end]);
            let mut owned = [independent; MAX_LANES];
            let mut invalid = 0_u64;
            let tables: [&BivariateNormal; MAX_LANES] = match self.correlations {
                Correlations::One(table) => [table; MAX_LANES],
                Correlations::Each(rho) => {
                    for lane in 0..K::LANES {
                        let r = rho[start + lane];
                        if lane > 0 && r.to_bits() == rho[start + lane - 1].to_bits() {
                            owned[lane] = owned[lane - 1];
                            invalid |= (invalid >> (lane - 1) & 1) << lane;
                        } else if let Ok(table) = BivariateNormal::new(r) {
                            owned[lane] = table;
                        } else {
                            invalid |= 1 << lane;
                        }
                    }
                    core::array::from_fn(|lane| &owned[lane])
                }
            };
            let (mut values, _) = chunk(k, ax, ay, &tables);
            for (lane, v) in values.as_mut().iter_mut().enumerate() {
                if invalid >> lane & 1 == 1 {
                    *v = f64::NAN;
                }
            }
            self.out[start..end].copy_from_slice(values.as_ref());
        }
        covered
    }
}

/// The chunks of backend `k` over the start of the pairs; how many pairs
/// that covered.
pub(crate) fn chunks<K: Simd>(
    k: K,
    x: &[f64],
    y: &[f64],
    correlations: Correlations<'_>,
    out: &mut [f64],
) -> usize {
    k.vectorize(Chunks {
        x,
        y,
        correlations,
        out,
    })
}

/// `out[i]` is the scalar function's value for pair `i`, through the cascade
/// of backends this CPU has, widest first, as `crate::lanes::map` does; a
/// last single pair is the scalar function's.
pub(super) fn map(x: &[f64], y: &[f64], correlations: Correlations<'_>, out: &mut [f64]) {
    #[cfg(any(
        all(target_arch = "x86_64", target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    ))]
    let mut done = 0;
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    )))]
    let done = chunks(
        morphiq_numerics_arch::Scalar::new(),
        x,
        y,
        correlations,
        out,
    );
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        let rest = |done: usize| match correlations {
            Correlations::One(table) => Correlations::One(table),
            Correlations::Each(rho) => Correlations::Each(&rho[done..]),
        };
        if x.len() - done >= Avx512::LANES
            && let Some(k) = Avx512::try_new()
        {
            done += chunks(k, &x[done..], &y[done..], rest(done), &mut out[done..]);
        }
        if x.len() - done >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            done += chunks(k, &x[done..], &y[done..], rest(done), &mut out[done..]);
        }
        if x.len() - done >= Sse2::LANES {
            done += chunks(
                Sse2::new(),
                &x[done..],
                &y[done..],
                rest(done),
                &mut out[done..],
            );
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        use morphiq_numerics_arch::Neon;
        if x.len() >= Neon::LANES {
            done += chunks(Neon::new(), x, y, correlations, out);
        }
    }
    for i in done..x.len() {
        out[i] = correlations.scalar(i, x[i], y[i]);
    }
}

#[cfg(test)]
mod tests;
