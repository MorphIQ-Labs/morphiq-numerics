//! Bounded natural logarithm; the reciprocal stage's rounded approximation.
//! See `docs/fast_ln.md` and `formal/fast/FastLn.v`.

/// The strong entry owns specials; every positive finite nonunit input uses
/// one reciprocal stage, without a rounding test or precision escalation.
#[inline]
pub(crate) fn ln(x: f64) -> f64 {
    if !(x > 0.0 && x < f64::INFINITY) || x == 1.0 {
        return super::ln(x);
    }
    let reduced = super::Reduced::of(x);
    let (s, lo, _, _) = super::stage::parts(reduced.e, reduced.y);
    s + lo
}

#[cfg(feature = "simd")]
#[cold]
#[inline(never)]
fn scalar_packet(input: &[f64], output: &mut [f64]) {
    for (&x, y) in input.iter().zip(output) {
        *y = ln(x);
    }
}

#[cfg(feature = "simd")]
#[inline(always)]
fn evaluate<K: morphiq_numerics_arch::Simd>(k: K, input: &[f64], output: &mut [f64]) {
    let mut packet = K::Array::default();
    // Padding is a supported positive finite input and is never stored.
    packet.as_mut().fill(2.0);
    packet.as_mut()[..input.len()].copy_from_slice(input);
    let x = k.load(packet);
    let regular = k.and_m(k.lt(k.splat(0.0), x), k.lt(x, k.splat(f64::INFINITY)));
    if k.mask_bits(regular) != (1 << K::LANES) - 1 {
        return scalar_packet(input, output);
    }
    k.store_partial(super::lanes::bounded_positive(k, x), output);
}

#[cfg(feature = "simd")]
struct Slice<'a> {
    input: &'a [f64],
    output: &'a mut [f64],
}

#[cfg(feature = "simd")]
impl morphiq_numerics_arch::WithSimd for Slice<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: morphiq_numerics_arch::Simd>(self, k: K) {
        let size = 2 * K::LANES;
        let bulk = self.input.len() / size * size;
        let (input, rest) = self.input.split_at(bulk);
        let (output, rest_out) = self.output.split_at_mut(bulk);
        for (input, output) in input.chunks_exact(size).zip(output.chunks_exact_mut(size)) {
            for i in 0..2 {
                let start = i * K::LANES;
                evaluate(
                    k,
                    &input[start..start + K::LANES],
                    &mut output[start..start + K::LANES],
                );
            }
        }
        for (input, output) in rest.chunks(K::LANES).zip(rest_out.chunks_mut(K::LANES)) {
            evaluate(k, input, output);
        }
    }
}

#[cfg(feature = "simd")]
pub(crate) fn slice(input: &[f64], output: &mut [f64]) {
    use morphiq_numerics_arch::Simd;
    if input.len() < 2 {
        for (&x, y) in input.iter().zip(output) {
            *y = ln(x);
        }
        return;
    }
    let work = Slice { input, output };
    #[cfg(target_arch = "x86_64")]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        if input.len() >= Avx512::LANES
            && let Some(k) = Avx512::try_new()
        {
            return k.vectorize(work);
        }
        if input.len() >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            return k.vectorize(work);
        }
        Sse2::new().vectorize(work)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        morphiq_numerics_arch::Neon::new().vectorize(work)
    }
    #[cfg(not(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "neon")
    )))]
    morphiq_numerics_arch::Scalar::new().vectorize(work);
}

#[cfg(all(test, feature = "simd"))]
mod tests {
    use super::*;
    use crate::lanes::tests::{backends, ln_corpus};

    #[test]
    fn fast_ln_slices_match_scalar_on_every_backend_and_remainder() {
        let xs = ln_corpus();
        for backend in backends() {
            for len in (0..=17).chain([31, 32, 33, 51, 52, 53, xs.len()]) {
                let mut output = std::vec![0.0; len];
                backend.vectorize(Slice {
                    input: &xs[..len],
                    output: &mut output,
                });
                for (&x, &y) in xs[..len].iter().zip(&output) {
                    assert_eq!(y.to_bits(), ln(x).to_bits(), "{} at {x:?}", backend.name());
                }
            }
        }
    }
}
