//! Explicit bounded exponential: high-word table and quartic local polynomial.
//! The strong exponential retains its own compensated evaluator.
use super::tables::{INV_N, POLY_S, S_L1, S_L2D, S_T, SHIFTER};

// A layout projection of the existing generated table, not new coefficients.
const HIGH: [u64; 512] = {
    let mut high = [0; 512];
    let mut i = 0;
    while i < 512 {
        high[i] = S_T[i].0;
        i += 1;
    }
    high
};

#[inline]
pub(crate) fn exp(x: f64) -> f64 {
    if !(x.abs() < 704.0) {
        return super::exp(x);
    }
    let t = x * INV_N + SHIFTER;
    let n = t - SHIFTER;
    let bits = t.to_bits();
    #[allow(clippy::cast_possible_truncation)] // masked index is at most 511
    let index = (bits & 511) as usize;
    // Bits 9..20 encode the signed scale modulo 4096. Adding this field to
    // the normal table word is exact for this screened exponent domain.
    let high = f64::from_bits(HIGH[index].wrapping_add((bits >> 9) << 52));
    let r = (x - n * S_L1) - n * S_L2D;
    let [d3, d4, _] = POLY_S;
    let r2 = r * r;
    let left = r + 0.5 * r2;
    let p = d3 + r * d4;
    let u = left + (r2 * r) * p;
    high + high * u
}

#[cfg(feature = "simd")]
#[inline(always)]
fn screened<K: morphiq_numerics_arch::Simd>(k: K, input: K::F) -> (K::F, u64) {
    let active = k.lt(k.abs(input), k.splat(704.0));
    let x = k.select(active, input, k.splat(0.0));
    let t = k.add(k.mul(x, k.splat(INV_N)), k.splat(SHIFTER));
    let n = k.sub(t, k.splat(SHIFTER));
    let bits = k.to_bits(t);
    let high = k.gather_wrapped(&HIGH, bits);
    let scale = k.shl_u(k.shr_u(bits, 9), 52);
    let high = k.to_float(k.add_u(k.to_bits(high), scale));
    let r = k.sub(k.sub(x, k.mul(n, k.splat(S_L1))), k.mul(n, k.splat(S_L2D)));
    let [d3, d4, _] = POLY_S;
    let r2 = k.mul(r, r);
    let left = k.add(r, k.mul(k.splat(0.5), r2));
    let p = k.add(k.splat(d3), k.mul(r, k.splat(d4)));
    let u = k.add(left, k.mul(k.mul(r2, r), p));
    let result = k.add(high, k.mul(high, u));
    (result, k.mask_bits(active))
}

#[cfg(feature = "simd")]
#[inline(always)]
pub(crate) fn lanes<K: morphiq_numerics_arch::Simd>(k: K, input: K::F) -> K::F {
    let (result, active) = screened(k, input);
    if active == (1 << K::LANES) - 1 {
        return result;
    }
    crate::lanes::cold(k, Finish { active }, input, result)
}

#[cfg(feature = "simd")]
struct Finish {
    active: u64,
}
#[cfg(feature = "simd")]
impl crate::lanes::Cold for Finish {
    #[inline(always)]
    fn run<K: morphiq_numerics_arch::Simd>(
        self,
        _: K,
        input: K::Array,
        mut out: K::Array,
    ) -> K::Array {
        for (i, (y, &x)) in out.as_mut().iter_mut().zip(input.as_ref()).enumerate() {
            if self.active >> i & 1 == 0 {
                *y = super::exp(x);
            }
        }
        out
    }
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
        let mut active = (1 << K::LANES) - 1;
        let inputs = self.input.chunks_exact(K::LANES);
        let tail = inputs.remainder();
        let mut outputs = self.output.chunks_exact_mut(K::LANES);
        for (input, output) in inputs.zip(outputs.by_ref()) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(input);
            let (y, mask) = screened(k, k.load(x));
            active &= mask;
            output.copy_from_slice(k.store(y).as_ref());
        }
        if !tail.is_empty() {
            let (y, mask) = screened(k, k.load_partial(tail));
            active &= mask;
            k.store_partial(y, outputs.into_remainder());
        }
        // One cold branch per slice. Screened lanes use benign zero above;
        // repair only those lanes with the strong owner after the vector pass.
        if active != (1 << K::LANES) - 1 {
            repair(self.input, self.output);
        }
    }
}

#[cfg(feature = "simd")]
#[cold]
#[inline(never)]
fn repair(input: &[f64], output: &mut [f64]) {
    for (&x, y) in input.iter().zip(output) {
        if !(x.abs() < 704.0) {
            *y = super::exp(x);
        }
    }
}

#[cfg(feature = "simd")]
#[inline]
pub(crate) fn slice(input: &[f64], output: &mut [f64]) {
    use morphiq_numerics_arch::Simd;
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
            return k.vectorize(op);
        }
        if input.len() >= 4
            && let Some(k) = Avx2::try_new()
        {
            return k.vectorize(op);
        }
        Sse2::new().vectorize(op);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "sse2")))]
    morphiq_numerics_arch::dispatch(op);
}
