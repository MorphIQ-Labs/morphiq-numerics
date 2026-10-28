//! Explicit bounded exponential: high-word table and quartic local polynomial.
//! The strong exponential retains its own compensated evaluator.
use super::tables::{INV_N, POLY_S, S_L1, S_L2D, S_T, SHIFTER};

// Project the generated high words and pre-subtract the low index bits.
// The full shifted reduction encoding restores them in the scale addition.
const HIGH: [u64; 512] = {
    let mut high = [0; 512];
    let mut i = 0;
    while i < 512 {
        high[i] = S_T[i].0.wrapping_sub((i as u64) << 43);
        i += 1;
    }
    high
};

#[inline]
pub(crate) fn exp(x: f64) -> f64 {
    let active = x.abs() < 704.0; // NaNs belong to the strong owner too.
    if !active {
        return super::exp(x);
    }
    let t = x * INV_N + SHIFTER;
    let n = t - SHIFTER;
    let bits = t.to_bits();
    #[allow(clippy::cast_possible_truncation)] // masked index is at most 511
    let index = (bits & 511) as usize;
    // The index contribution in bits 0..8 cancels the table bias exactly.
    // Bits 9..20 then supply the normal exponent scale, modulo 2^64.
    let high = f64::from_bits(HIGH[index].wrapping_add(bits << 43));
    let r = (x - n * S_L1) - n * S_L2D;
    let [d3, d4, _] = POLY_S;
    let r2 = r * r;
    let left = r + 0.5 * r2;
    let p = d3 + r * d4;
    let u = left + (r2 * r) * p;
    high * (1.0 + u)
}

#[cfg(feature = "simd")]
#[inline(always)]
fn kernel<K: morphiq_numerics_arch::Simd>(k: K, x: K::F) -> K::F {
    let t = k.add(k.mul(x, k.splat(INV_N)), k.splat(SHIFTER));
    let n = k.sub(t, k.splat(SHIFTER));
    let bits = k.to_bits(t);
    let high = k.gather_wrapped(&HIGH, bits);
    let scale = k.shl_u(bits, 43);
    let high = k.to_float(k.add_u(k.to_bits(high), scale));
    let r = k.sub(k.sub(x, k.mul(n, k.splat(S_L1))), k.mul(n, k.splat(S_L2D)));
    let [d3, d4, _] = POLY_S;
    let r2 = k.mul(r, r);
    let left = k.add(r, k.mul(k.splat(0.5), r2));
    let p = k.add(k.splat(d3), k.mul(r, k.splat(d4)));
    let u = k.add(left, k.mul(k.mul(r2, r), p));
    k.mul(high, k.add(k.splat(1.0), u))
}

#[cfg(feature = "simd")]
#[inline(always)]
fn all_active<K: morphiq_numerics_arch::Simd>(k: K, input: K::F) -> bool {
    k.mask_bits(k.lt(k.abs(input), k.splat(704.0))) == (1 << K::LANES) - 1
}

#[cfg(feature = "simd")]
#[inline(always)]
pub(crate) fn lanes<K: morphiq_numerics_arch::Simd>(k: K, input: K::F) -> K::F {
    if all_active(k, input) {
        return kernel(k, input);
    }
    crate::lanes::cold(k, FinishAll, input, k.splat(0.0))
}

#[cfg(feature = "simd")]
struct FinishAll;
#[cfg(feature = "simd")]
impl crate::lanes::Cold for FinishAll {
    #[inline(always)]
    fn run<K: morphiq_numerics_arch::Simd>(
        self,
        _: K,
        input: K::Array,
        mut out: K::Array,
    ) -> K::Array {
        for (y, &x) in out.as_mut().iter_mut().zip(input.as_ref()) {
            *y = exp(x);
        }
        out
    }
}

#[cfg(feature = "simd")]
#[cold]
#[inline(never)]
fn scalar_packet(input: &[f64], output: &mut [f64]) {
    for (&x, y) in input.iter().zip(output) {
        *y = exp(x);
    }
}

#[cfg(feature = "simd")]
#[inline(always)]
// Cold packets finish through scalar owners by reference; the hot path needs
// neither a masked dependency on the screen nor a returned lane-array spill.
fn evaluate<K: morphiq_numerics_arch::Simd>(k: K, x: K::F, input: &[f64], output: &mut [f64]) {
    if !all_active(k, x) {
        return scalar_packet(input, output);
    }
    k.store_partial(kernel(k, x), output);
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
        assert_eq!(self.input.len(), self.output.len());
        // Two independent vectors expose work across table loads without
        // changing the operation order within a lane.
        let bulk_len = self.input.len() / (2 * K::LANES) * (2 * K::LANES);
        let (bulk, rest) = self.input.split_at(bulk_len);
        let (bulk_out, rest_out) = self.output.split_at_mut(bulk_len);
        for (input, output) in bulk
            .chunks_exact(2 * K::LANES)
            .zip(bulk_out.chunks_exact_mut(2 * K::LANES))
        {
            for i in 0..2 {
                let start = i * K::LANES;
                let input = &input[start..start + K::LANES];
                let output = &mut output[start..start + K::LANES];
                let mut x = K::Array::default();
                x.as_mut().copy_from_slice(input);
                evaluate(k, k.load(x), input, output);
            }
        }
        let inputs = rest.chunks_exact(K::LANES);
        let tail = inputs.remainder();
        let mut outputs = rest_out.chunks_exact_mut(K::LANES);
        for (input, output) in inputs.zip(outputs.by_ref()) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(input);
            evaluate(k, k.load(x), input, output);
        }
        if !tail.is_empty() {
            let output = outputs.into_remainder();
            if K::LANES <= 4 || tail.len() <= 2 {
                for (&x, y) in tail.iter().zip(output) {
                    *y = exp(x);
                }
            } else {
                evaluate(k, k.load_partial(tail), tail, output);
            }
        }
    }
}

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
        assert_eq!(N, K::LANES);
        let mut x = K::Array::default();
        x.as_mut().copy_from_slice(self.input);
        evaluate(k, k.load(x), self.input, self.output);
    }
}
#[cfg(feature = "simd")]
#[inline(always)]
fn packet<K: morphiq_numerics_arch::Simd, const N: usize>(k: K, op: Slice<'_>) {
    let (input, tail) = op.input.split_at(N);
    let (output, rest) = op.output.split_at_mut(N);
    let packet = Packet::<N> {
        input: input.try_into().expect("fixed packet"),
        output: output.try_into().expect("fixed packet"),
    };
    if tail.is_empty() {
        return k.vectorize(packet);
    }
    k.vectorize(packet);
    for (&x, y) in tail.iter().zip(rest) {
        *y = exp(x);
    }
}
#[cfg(feature = "simd")]
#[inline(always)]
fn run<K: morphiq_numerics_arch::Simd>(k: K, op: Slice<'_>) {
    if op.input.len() < 2 * K::LANES && op.input.len() <= K::LANES + 2 {
        match K::LANES {
            2 => return packet::<K, 2>(k, op),
            4 => return packet::<K, 4>(k, op),
            8 => return packet::<K, 8>(k, op),
            _ => (),
        }
    }
    k.vectorize(op);
}

#[cfg(feature = "simd")]
#[inline]
pub(crate) fn slice(input: &[f64], output: &mut [f64]) {
    if input.len() <= 1 {
        if let Some(&x) = input.first() {
            output[0] = exp(x);
        }
        return;
    }
    let op = Slice { input, output };
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        if input.len() >= 8
            && let Some(k) = Avx512::try_new()
        {
            return run(k, op);
        }
        if input.len() >= 4
            && let Some(k) = Avx2::try_new()
        {
            return run(k, op);
        }
        run(Sse2::new(), op);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "sse2")))]
    morphiq_numerics_arch::dispatch(op);
}
