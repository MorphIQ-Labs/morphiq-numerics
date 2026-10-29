//! Bounded natural logarithm; the reciprocal stage's rounded approximation.
//! See `docs/fast_ln.md` and `formal/fast/FastLn.v`.

/// The strong entry owns specials; every positive finite nonunit input uses
/// one reciprocal stage, without a rounding test or precision escalation.
#[inline]
pub(crate) fn ln(x: f64) -> f64 {
    let bits = x.to_bits();
    // One encoding interval screens normal positive finite arguments.
    if bits.wrapping_sub(f64::MIN_POSITIVE.to_bits())
        >= f64::INFINITY.to_bits() - f64::MIN_POSITIVE.to_bits()
    {
        return unusual(x);
    }
    if super::stage::unit_cell(bits) {
        let (s, lo, _, _) = super::stage::unit_parts(x);
        return s + lo;
    }
    let reduced = super::Reduced::normal_bits(bits, 0);
    let (s, lo, _, _) = super::stage::normalized_parts(&reduced);
    s + lo
}

// Return the final scalar value here, so the hot caller need not reserve
// stack space for the subnormal normalizer's reduction record.
#[cold]
#[inline(never)]
fn unusual(x: f64) -> f64 {
    if x > 0.0 && x < f64::MIN_POSITIVE {
        let reduced = super::Reduced::normal_bits((x * super::TWO_54).to_bits(), 54);
        let (s, lo, _, _) = super::stage::normalized_parts(&reduced);
        s + lo
    } else {
        super::ln(x)
    }
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
fn evaluate_general<K: morphiq_numerics_arch::Simd>(k: K, input: &[f64], output: &mut [f64]) {
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
#[inline(always)]
fn evaluate<K: morphiq_numerics_arch::Simd>(k: K, input: &[f64], output: &mut [f64]) {
    if K::LANES != 8 {
        return evaluate_general(k, input, output);
    }
    let mut packet = K::Array::default();
    packet.as_mut().fill(2.0);
    packet.as_mut()[..input.len()].copy_from_slice(input);
    let x = k.load(packet);
    let normal = k.and_m(
        k.le(k.splat(f64::MIN_POSITIVE), x),
        k.lt(x, k.splat(f64::INFINITY)),
    );
    if k.mask_bits(normal) != (1 << K::LANES) - 1 {
        return general_packets(k, input, output);
    }
    k.store_partial(super::lanes::bounded_normal(k, x), output);
}

#[cfg(feature = "simd")]
#[inline(always)]
fn evaluate_pair<K: morphiq_numerics_arch::Simd>(k: K, input: &[f64], output: &mut [f64]) {
    let mut a = K::Array::default();
    let mut b = K::Array::default();
    a.as_mut().copy_from_slice(&input[..K::LANES]);
    b.as_mut().copy_from_slice(&input[K::LANES..]);
    let a = k.load(a);
    let b = k.load(b);
    let normal_a = k.and_m(
        k.le(k.splat(f64::MIN_POSITIVE), a),
        k.lt(a, k.splat(f64::INFINITY)),
    );
    let normal_b = k.and_m(
        k.le(k.splat(f64::MIN_POSITIVE), b),
        k.lt(b, k.splat(f64::INFINITY)),
    );
    if k.mask_bits(k.and_m(normal_a, normal_b)) != (1 << K::LANES) - 1 {
        return general_packets(k, input, output);
    }
    let (out_a, out_b) = output.split_at_mut(K::LANES);
    let (a, b) = super::lanes::bounded_normal_pair(k, a, b);
    k.store_partial(a, out_a);
    k.store_partial(b, out_b);
}

// Keep subnormal scaling and mixed-special handling off the normal path.
// The general loop preserves each packet's scalar/SIMD selection, and
// vectorize keeps every lane operation inside its backend's feature boundary.
#[cfg(feature = "simd")]
#[cold]
#[inline(never)]
fn general_packets<K: morphiq_numerics_arch::Simd>(k: K, input: &[f64], output: &mut [f64]) {
    k.vectorize(Slice::<false> { input, output });
}

#[cfg(feature = "simd")]
struct Slice<'a, const SPECIALIZE_NORMAL: bool = true> {
    input: &'a [f64],
    output: &'a mut [f64],
}

#[cfg(feature = "simd")]
impl<const SPECIALIZE_NORMAL: bool> morphiq_numerics_arch::WithSimd
    for Slice<'_, SPECIALIZE_NORMAL>
{
    type Output = ();
    #[inline(always)]
    fn with<K: morphiq_numerics_arch::Simd>(self, k: K) {
        let size = K::LANES;
        let bulk = self.input.len() / size * size;
        let (input, rest) = self.input.split_at(bulk);
        let (output, rest_out) = self.output.split_at_mut(bulk);
        if SPECIALIZE_NORMAL && K::LANES == 8 {
            let mut inputs = input.chunks_exact(2 * size);
            let mut outputs = output.chunks_exact_mut(2 * size);
            for (input, output) in inputs.by_ref().zip(outputs.by_ref()) {
                evaluate_pair(k, input, output);
            }
            if !inputs.remainder().is_empty() {
                evaluate(k, inputs.remainder(), outputs.into_remainder());
            }
        } else {
            for (input, output) in input.chunks_exact(size).zip(output.chunks_exact_mut(size)) {
                evaluate_general(k, input, output);
            }
        }
        if !rest.is_empty() {
            if SPECIALIZE_NORMAL {
                evaluate(k, rest, rest_out);
            } else {
                evaluate_general(k, rest, rest_out);
            }
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
        assert!(N.is_power_of_two() && N <= 64);
        if K::LANES == 8 && N.is_multiple_of(2 * K::LANES) {
            // These are the existing fixed 16/32/64-value calls. Explicit
            // pairs avoid a tiny loop hoisting every stage constant at entry.
            evaluate_pair(k, &self.input[..16], &mut self.output[..16]);
            if N >= 32 {
                evaluate_pair(k, &self.input[16..32], &mut self.output[16..32]);
            }
            if N >= 64 {
                evaluate_pair(k, &self.input[32..48], &mut self.output[32..48]);
                evaluate_pair(k, &self.input[48..64], &mut self.output[48..64]);
            }
        } else {
            for (input, output) in self
                .input
                .chunks_exact(K::LANES)
                .zip(self.output.chunks_exact_mut(K::LANES))
            {
                evaluate(k, input, output);
            }
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
