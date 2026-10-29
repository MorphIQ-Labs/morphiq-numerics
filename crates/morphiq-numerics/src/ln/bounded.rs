//! Bounded natural logarithm; the reciprocal stage's rounded approximation.
//! See `docs/fast_ln.md` and `formal/fast/FastLn.v`.

/// The strong entry owns specials; every positive finite nonunit input uses
/// one reciprocal stage, without a rounding test or precision escalation.
#[inline]
pub(crate) fn ln(x: f64) -> f64 {
    let bits = x.to_bits();
    // Positive finite encodings are precisely 1..INFINITY.to_bits().
    // Wrapping subtraction excludes zero and every sign-bit encoding too.
    if bits.wrapping_sub(1) >= f64::INFINITY.to_bits() - 1 || x == 1.0 {
        return super::ln(x);
    }
    let reduced = super::Reduced::of(x);
    let (s, lo, _, _) = super::stage::normalized_parts(&reduced);
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
        let size = K::LANES;
        let bulk = self.input.len() / size * size;
        let (input, rest) = self.input.split_at(bulk);
        let (output, rest_out) = self.output.split_at_mut(bulk);
        for (input, output) in input.chunks_exact(size).zip(output.chunks_exact_mut(size)) {
            evaluate(k, input, output);
        }
        if !rest.is_empty() {
            evaluate(k, rest, rest_out);
        }
    }
}

// Fixed packets avoid the bulk loop's stack frame and partial-array copies
// on short calls. This is the same dispatch structure used by bounded exp.
#[cfg(feature = "simd")]
struct Packet<'a, const N: usize> {
    input: &'a [f64; N],
    output: &'a mut [f64; N],
}

#[cfg(feature = "simd")]
impl<const N: usize> morphiq_numerics_arch::WithSimd for Packet<'_, N> {
    type Output = ();
    #[inline(always)]
    fn with<K: morphiq_numerics_arch::Simd>(self, k: K) {
        assert!(N >= K::LANES && N.is_multiple_of(K::LANES));
        for (input, output) in self
            .input
            .chunks_exact(K::LANES)
            .zip(self.output.chunks_exact_mut(K::LANES))
        {
            evaluate(k, input, output);
        }
    }
}

#[cfg(feature = "simd")]
#[cfg_attr(
    any(target_feature = "avx2", target_feature = "avx512f"),
    inline(never)
)]
#[cfg_attr(
    not(any(target_feature = "avx2", target_feature = "avx512f")),
    inline(always)
)]
fn fixed<K: morphiq_numerics_arch::Simd, const N: usize>(
    k: K,
    input: &[f64; N],
    output: &mut [f64; N],
) {
    k.vectorize(Packet { input, output });
}

#[cfg(feature = "simd")]
#[inline(never)]
fn packet<K: morphiq_numerics_arch::Simd, const N: usize>(k: K, work: Slice<'_>) {
    let (input, tail) = work.input.split_at(N);
    let (output, rest) = work.output.split_at_mut(N);
    for (&x, y) in tail.iter().zip(rest) {
        *y = ln(x);
    }
    fixed::<K, N>(
        k,
        input.try_into().expect("fixed packet"),
        output.try_into().expect("fixed packet"),
    );
}

#[cfg(feature = "simd")]
#[inline(always)]
fn run<K: morphiq_numerics_arch::Simd>(k: K, work: Slice<'_>) {
    let n = work.input.len();
    if n >= K::LANES && n <= 8 * K::LANES && n.is_power_of_two() {
        macro_rules! fixed {
            ($n:literal) => {
                fixed::<K, $n>(
                    k,
                    work.input.try_into().expect("fixed packet"),
                    work.output.try_into().expect("fixed packet"),
                )
            };
        }
        return match n {
            2 => fixed!(2),
            4 => fixed!(4),
            8 => fixed!(8),
            16 => fixed!(16),
            32 => fixed!(32),
            64 => fixed!(64),
            _ => k.vectorize(work),
        };
    }
    if n > K::LANES && n <= 8 * K::LANES + 2 {
        match n {
            3 => return packet::<K, 2>(k, work),
            5 | 6 => return packet::<K, 4>(k, work),
            9 | 10 => return packet::<K, 8>(k, work),
            17 | 18 => return packet::<K, 16>(k, work),
            33 | 34 => return packet::<K, 32>(k, work),
            65 | 66 => return packet::<K, 64>(k, work),
            _ => (),
        }
    }
    k.vectorize(work);
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
            return run(k, work);
        }
        if input.len() >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            return run(k, work);
        }
        run(Sse2::new(), work)
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        run(morphiq_numerics_arch::Neon::new(), work)
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

    struct Dispatched<'a>(Slice<'a>);
    impl morphiq_numerics_arch::WithSimd for Dispatched<'_> {
        type Output = ();
        fn with<K: morphiq_numerics_arch::Simd>(self, k: K) {
            run(k, self.0);
        }
    }

    #[test]
    fn fast_ln_slices_match_scalar_on_every_backend_and_remainder() {
        let xs = ln_corpus();
        for backend in backends() {
            for len in (0..=66).chain([256, 4096, xs.len()]) {
                let mut output = std::vec![0.0; len];
                backend.vectorize(Dispatched(Slice {
                    input: &xs[..len],
                    output: &mut output,
                }));
                for (&x, &y) in xs[..len].iter().zip(&output) {
                    assert_eq!(y.to_bits(), ln(x).to_bits(), "{} at {x:?}", backend.name());
                }
            }
        }
    }
}
