//! Lane evaluation: a scalar function's fast path, operation for operation, on
//! every lane of a SIMD backend, with the scalar function itself for every lane
//! the fast path doesn't decide. So each lane returns the scalar function's
//! bits.
//!
//! The argument, and what each kernel transcribes, are in
//! [`docs/lanes.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md);
//! section numbers below refer to it. The backends, and the only `unsafe`
//! code involved, are in the `morphiq-numerics-arch` crate
//! ([`docs/arch.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/arch.md)).

use core::marker::PhantomData;

use morphiq_numerics_arch::{Simd, WithSimd};

/// Veltkamp's splitting constant `2^27 + 1`, as in `eft.rs` (Dekker 1971,
/// (6.2)); the lane split is checked against `eft::two_prod` bit for bit.
const SPLITTER: f64 = 134_217_729.0;
/// The binary64 exponent field.
const EXPONENT: u64 = 0x7ff << 52;
/// The binary64 fraction field.
const FRACTION: u64 = (1 << 52) - 1;
/// `2^−969`: from it up, `ulp` of a binary64 number is `2^(biased − 1075)`
/// and half of it is normal, so the rounding test's gap is computed from the
/// exponent field alone (§3).
const GAP_FLOOR: f64 = f64::from_bits(54 << 52);

/// A function evaluated on lanes: its scalar form, and its fast path on one
/// backend's lanes, which returns the scalar function's bits on every lane.
pub(crate) trait Kernel {
    /// The scalar function.
    fn scalar(x: f64) -> f64;
    /// `scalar` on every lane of `x`.
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array;
}

/// `out[i] = G::scalar(xs[i])` for every `i`, in a cascade of the backends
/// this CPU has, widest first (§1): each takes as many whole chunks of its
/// own width as remain, so a slice, or a remainder, of at least two elements
/// still runs in lanes. Only a last single element is left to the scalar
/// function. On x86-64 the cascade is AVX-512F, AVX2, SSE2; on aarch64 NEON.
/// Every backend returns the scalar bits, so the cascade does too.
pub(crate) fn map<G: Kernel>(xs: &[f64], out: &mut [f64]) {
    let mut done = 0;
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        if xs.len() - done >= Avx512::LANES
            && let Some(k) = Avx512::try_new()
        {
            done += chunks::<G, _>(k, &xs[done..], &mut out[done..]);
        }
        if xs.len() - done >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            done += chunks::<G, _>(k, &xs[done..], &mut out[done..]);
        }
        if xs.len() - done >= Sse2::LANES {
            done += chunks::<G, _>(Sse2::new(), &xs[done..], &mut out[done..]);
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        use morphiq_numerics_arch::Neon;
        if xs.len() >= Neon::LANES {
            done += chunks::<G, _>(Neon::new(), xs, out);
        }
    }
    for (o, &x) in out[done..].iter_mut().zip(&xs[done..]) {
        *o = G::scalar(x);
    }
}

/// `G`'s lanes on every whole chunk of backend `k`'s width at the start of
/// `xs`, inside `k`'s feature-enabled wrapper; returns how many elements
/// that covered.
pub(crate) fn chunks<G: Kernel, K: Simd>(k: K, xs: &[f64], out: &mut [f64]) -> usize {
    k.vectorize(Chunks::<G> {
        xs,
        out,
        kernel: PhantomData,
    })
}

struct Chunks<'a, G> {
    xs: &'a [f64],
    out: &'a mut [f64],
    kernel: PhantomData<G>,
}

impl<G: Kernel> WithSimd for Chunks<'_, G> {
    type Output = usize;
    #[inline(always)]
    fn with<K: Simd>(self, k: K) -> usize {
        whole_chunks::<G, K>(k, self.xs, self.out)
    }
}

/// `out[i] = G::scalar(xs[i])` on backend `k`'s lanes for every whole chunk;
/// returns the number of elements covered, a multiple of `K::LANES`.
#[inline(always)]
fn whole_chunks<G: Kernel, K: Simd>(k: K, xs: &[f64], out: &mut [f64]) -> usize {
    debug_assert_eq!(xs.len(), out.len());
    if K::LANES == 1 {
        return 0;
    }
    let chunks = xs.chunks_exact(K::LANES);
    let covered = xs.len() - chunks.remainder().len();
    for (x, o) in chunks.zip(out.chunks_exact_mut(K::LANES)) {
        let mut a = K::Array::default();
        a.as_mut().copy_from_slice(x);
        o.copy_from_slice(G::lanes(k, a).as_ref());
    }
    covered
}

/// `out[i] = G::scalar(xs[i])` on backend `k`'s lanes alone, the last
/// `xs.len() mod LANES` elements by the scalar function.
#[cfg(test)]
#[inline(always)]
pub(crate) fn run<G: Kernel, K: Simd>(k: K, xs: &[f64], out: &mut [f64]) {
    let done = whole_chunks::<G, K>(k, xs, out);
    for (o, &x) in out[done..].iter_mut().zip(&xs[done..]) {
        *o = G::scalar(x);
    }
}

/// A double-word number on lanes: `(hi, lo)` per lane.
pub(crate) type Dw<K> = (<K as Simd>::F, <K as Simd>::F);

/// `eft::two_sum`, operation for operation.
#[inline(always)]
pub(crate) fn two_sum<K: Simd>(k: K, a: K::F, b: K::F) -> Dw<K> {
    let s = k.add(a, b);
    let a_prime = k.sub(s, b);
    let b_prime = k.sub(s, a_prime);
    let delta_a = k.sub(a, a_prime);
    let delta_b = k.sub(b, b_prime);
    (s, k.add(delta_a, delta_b))
}

/// `eft::fast_two_sum`, operation for operation.
#[inline(always)]
pub(crate) fn fast_two_sum<K: Simd>(k: K, a: K::F, b: K::F) -> Dw<K> {
    let s = k.add(a, b);
    let z = k.sub(s, a);
    (s, k.sub(b, z))
}

/// `(p, e)` with `p = RN(a·b)` and, on `eft::two_prod`'s domain, `e` its exact
/// error: by one fused multiply-add on a backend with hardware FMA, else by
/// `eft::two_prod`'s Dekker product, operation for operation. On that domain
/// both return the same bits (§2).
#[inline(always)]
pub(crate) fn two_prod<K: Simd>(k: K, a: K::F, b: K::F) -> Dw<K> {
    let p = k.mul(a, b);
    if let Some(e) = k.mul_add(a, b, k.neg(p)) {
        return (p, e);
    }
    let (a_head, a_tail) = split(k, a);
    let (b_head, b_tail) = split(k, b);
    let e = k.add(
        k.add(
            k.add(k.sub(k.mul(a_head, b_head), p), k.mul(a_head, b_tail)),
            k.mul(a_tail, b_head),
        ),
        k.mul(a_tail, b_tail),
    );
    (p, e)
}

/// `eft::split`, operation for operation.
#[inline(always)]
fn split<K: Simd>(k: K, x: K::F) -> Dw<K> {
    let p = k.mul(x, k.splat(SPLITTER));
    let q = k.sub(x, p);
    let head = k.add(q, p);
    (head, k.sub(x, head))
}

/// `DoubleWord::add_f64`, operation for operation.
#[inline(always)]
pub(crate) fn dw_add_f64<K: Simd>(k: K, x: Dw<K>, y: K::F) -> Dw<K> {
    let (s_hi, s_lo) = two_sum(k, x.0, y);
    let v = k.add(x.1, s_lo);
    fast_two_sum(k, s_hi, v)
}

/// `DoubleWord::add`, operation for operation.
#[inline(always)]
pub(crate) fn dw_add<K: Simd>(k: K, x: Dw<K>, y: Dw<K>) -> Dw<K> {
    let (s_hi, s_lo) = two_sum(k, x.0, y.0);
    let (t_hi, t_lo) = two_sum(k, x.1, y.1);
    let c = k.add(s_lo, t_hi);
    let (v_hi, v_lo) = fast_two_sum(k, s_hi, c);
    let w = k.add(t_lo, v_lo);
    fast_two_sum(k, v_hi, w)
}

/// `ln::decide_with`'s test on lanes: true where it returns `y_hi`, for
/// `|y_hi| ≥ 2^−969`, and false below, where the scalar function decides
/// instead (§3).
#[inline(always)]
pub(crate) fn decide<K: Simd>(k: K, y: Dw<K>, eps: f64) -> K::M {
    let magnitude = k.abs(y.0);
    let bits = k.to_bits(magnitude);
    let exponent = k.and_u(bits, k.splat_bits(EXPONENT));
    // ulp(magnitude) = 2^(biased − 1075), and half of it 2^(biased − 1076).
    let ulp = k.to_float(k.sub_u(exponent, k.splat_bits(52 << 52)));
    let half_ulp = k.to_float(k.sub_u(exponent, k.splat_bits(53 << 52)));
    let power_of_two = k.eq_u(k.and_u(bits, k.splat_bits(FRACTION)), k.splat_bits(0));
    let g = k.select(power_of_two, half_ulp, ulp);
    let error = k.add(k.abs(y.1), k.mul(k.splat(eps), magnitude));
    k.and_m(
        k.le(k.splat(GAP_FLOOR), magnitude),
        k.lt(error, k.mul(g, k.splat(0.5))),
    )
}

#[cfg(test)]
pub(crate) mod tests;
