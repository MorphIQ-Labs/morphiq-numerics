//! The bivariate normal distribution function on lanes ([`docs/lanes.md`] §5):
//! the low-correlation quadrature and Genz's high-correlation series,
//! operation for operation, with the scalar evaluator for every lane the
//! screen doesn't admit.
//!
//! The lanes use the library's own lane `exp` and `norm_cdf`, which return
//! the scalar functions' bits, and the scalar `sqrt` per lane, so every
//! lane's expression is the scalar expression with the same grouping and the
//! quadrature nodes summed in node order.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use core::f64::consts::TAU;

use morphiq_numerics_arch::{Simd, WithSimd};

use super::tables::{GL20_W, GL20_X};
use super::{BivariateNormal, Regime, SATURATED_THRESHOLD, SQRT_TAU, bivariate_norm_cdf};
use crate::elementary::sqrt;
use crate::exp::lanes::Exp;
use crate::lanes::{Kernel, mask_from};
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

/// The scalar `sqrt` on every lane, as `asin`'s reduction takes it.
#[inline(always)]
fn sqrt_lanes<K: Simd>(k: K, v: K::F) -> K::F {
    let mut a = k.store(v);
    for lane in a.as_mut() {
        *lane = sqrt(*lane);
    }
    k.load(a)
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
    let hs = k.div(k.add(k.mul(x, x), k.mul(y, y)), k.splat(2.0));
    let xy = k.mul(x, y);
    let widest = (0..K::LANES)
        .filter(|&lane| live_bits >> lane & 1 == 1)
        .map(|lane| tables[lane].nodes)
        .max()
        .unwrap_or(0);
    let mut sum = k.splat(0.0);
    for node in 0..widest {
        let (mut weight, mut sn, mut den) = (
            K::Array::default(),
            K::Array::default(),
            K::Array::default(),
        );
        let mut active = 0_u64;
        for lane in 0..K::LANES {
            let table = tables[lane];
            if live_bits >> lane & 1 == 1 && node < table.nodes {
                active |= 1 << lane;
                weight.as_mut()[lane] = table.weight[node];
                sn.as_mut()[lane] = table.sn[node];
                den.as_mut()[lane] = table.den[node];
            } else {
                den.as_mut()[lane] = 1.0;
            }
        }
        let active = mask_from(k, active);
        let arg = k.div(k.sub(k.mul(k.load(sn), xy), hs), k.load(den));
        let term = k.mul(k.load(weight), exp_lanes(k, live_or_zero(k, active, arg)));
        sum = k.select(active, k.add(sum, term), sum);
    }
    let mut asr = K::Array::default();
    for lane in 0..K::LANES {
        if live_bits >> lane & 1 == 1 {
            asr.as_mut()[lane] = tables[lane].asr;
        }
    }
    let sum = k.mul(sum, k.div(k.load(asr), k.splat(2.0 * TAU)));
    clamp_lanes(
        k,
        k.add(sum, k.mul(norm_cdf_lanes(k, x), norm_cdf_lanes(k, y))),
    )
}

/// `high_correlation(dh, dk, rho)` on every lane of `live`, with the scalar
/// function's grouping; the scalar function's branches are masks.
#[inline(always)]
fn high<K: Simd>(
    k: K,
    live_bits: u64,
    x: K::F,
    y: K::F,
    tables: &[&BivariateNormal; MAX_LANES],
) -> K::F {
    let live = mask_from(k, live_bits);
    let dh = k.neg(live_or_zero(k, live, x));
    let dk = k.neg(live_or_zero(k, live, y));
    let mut rho = K::Array::default();
    for lane in 0..K::LANES {
        // A dead lane takes a correlation in the regime so its divisions are
        // finite.
        rho.as_mut()[lane] = if live_bits >> lane & 1 == 1 {
            tables[lane].rho
        } else {
            0.95
        };
    }
    let rho = k.load(rho);
    let negative = k.lt(rho, k.splat(0.0));
    let positive = k.lt(k.splat(0.0), rho);
    let product = k.mul(dh, dk);
    let kk = k.select(negative, k.neg(dk), dk);
    let hk = k.select(negative, k.neg(product), product);
    let rho_abs = k.abs(rho);
    let ass = k.mul(k.sub(k.splat(1.0), rho_abs), k.add(k.splat(1.0), rho_abs));
    let a = sqrt_lanes(k, ass);
    let diff = k.sub(dh, kk);
    let bs = k.mul(diff, diff);
    let c = k.div(k.sub(k.splat(4.0), hk), k.splat(8.0));
    let d = k.div(k.sub(k.splat(12.0), hk), k.splat(16.0));
    let asr = k.div(k.neg(k.add(k.div(bs, ass), hk)), k.splat(2.0));

    // The leading term, if asr > -100.
    let lead = k.and_m(live, k.lt(k.splat(-100.0), asr));
    let correction = k.add(
        k.sub(
            k.splat(1.0),
            k.div(
                k.mul(
                    k.mul(c, k.sub(bs, ass)),
                    k.sub(k.splat(1.0), k.div(k.mul(d, bs), k.splat(5.0))),
                ),
                k.splat(3.0),
            ),
        ),
        k.div(k.mul(k.mul(k.mul(c, d), ass), ass), k.splat(5.0)),
    );
    let leading = k.mul(
        k.mul(a, exp_lanes(k, live_or_zero(k, lead, asr))),
        correction,
    );
    let mut bvn = live_or_zero(k, lead, leading);

    // The cdf term, if -hk < 100.
    let cdf_term = k.and_m(live, k.lt(k.neg(hk), k.splat(100.0)));
    let b = sqrt_lanes(k, bs);
    let weight = k.mul(
        k.mul(
            k.mul(
                k.mul(
                    exp_lanes(k, live_or_zero(k, cdf_term, k.div(k.neg(hk), k.splat(2.0)))),
                    k.splat(SQRT_TAU),
                ),
                norm_cdf_lanes(k, live_or_zero(k, cdf_term, k.div(k.neg(b), a))),
            ),
            b,
        ),
        k.sub(
            k.splat(1.0),
            k.div(
                k.mul(
                    k.mul(c, bs),
                    k.sub(k.splat(1.0), k.div(k.mul(d, bs), k.splat(5.0))),
                ),
                k.splat(3.0),
            ),
        ),
    );
    bvn = k.select(cdf_term, k.sub(bvn, weight), bvn);

    // The quadrature over the 20-point rule, each node's pair in the scalar
    // order (+ then -).
    let a = k.div(a, k.splat(2.0));
    for i in 0..GL20_X.len() {
        for sign in [1.0_f64, -1.0] {
            let xn = k.mul(a, k.splat(sign * GL20_X[i] + 1.0));
            let xs = k.mul(xn, xn);
            let asr = k.div(k.neg(k.add(k.div(bs, xs), hk)), k.splat(2.0));
            let node = k.and_m(live, k.lt(k.splat(-100.0), asr));
            if k.mask_bits(node) == 0 {
                continue;
            }
            let rs = sqrt_lanes(k, k.sub(k.splat(1.0), xs));
            let one_plus_rs = k.add(k.splat(1.0), rs);
            let inner = k.sub(
                k.div(
                    exp_lanes(
                        k,
                        live_or_zero(
                            k,
                            node,
                            k.div(
                                k.mul(k.neg(hk), xs),
                                k.mul(k.mul(k.splat(2.0), one_plus_rs), one_plus_rs),
                            ),
                        ),
                    ),
                    rs,
                ),
                k.add(
                    k.splat(1.0),
                    k.mul(k.mul(c, xs), k.add(k.splat(1.0), k.mul(d, xs))),
                ),
            );
            let term = k.mul(
                k.mul(
                    k.mul(a, k.splat(GL20_W[i])),
                    exp_lanes(k, live_or_zero(k, node, asr)),
                ),
                inner,
            );
            bvn = k.select(node, k.add(bvn, term), bvn);
        }
    }

    bvn = k.div(k.neg(bvn), k.splat(TAU));
    // The reflection of the scalar result: only the lanes that need each
    // normal CDF evaluate it.
    let upper = k.select(k.lt(dh, dk), dk, dh);
    let positive_live = k.and_m(live, positive);
    let negative_live = k.and_m(live, negative);
    let tail = norm_cdf_lanes(k, live_or_zero(k, positive_live, k.neg(upper)));
    let first = norm_cdf_lanes(k, live_or_zero(k, negative_live, k.neg(dh)));
    let second = norm_cdf_lanes(k, live_or_zero(k, negative_live, dk));
    let gap = k.sub(first, second);
    let gap = k.select(k.lt(k.splat(0.0), gap), gap, k.splat(0.0));
    let result = k.select(positive, k.add(bvn, tail), k.add(k.neg(bvn), gap));
    clamp_lanes(k, result)
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
    let (mut low_bits, mut high_bits) = (0_u64, 0_u64);
    for lane in 0..K::LANES {
        if live >> lane & 1 == 1 {
            match tables[lane].regime {
                Regime::Low => low_bits |= 1 << lane,
                Regime::High => high_bits |= 1 << lane,
                _ => {}
            }
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
    if high_bits != 0 {
        result = k.select(
            mask_from(k, high_bits),
            high(k, high_bits, xo, yo, tables),
            result,
        );
    }
    let mut out = k.store(result);
    // A NaN would come out of the scalar function with its own bits.
    let done = k.mask_bits(k.le(result, result)) & (low_bits | high_bits);
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
