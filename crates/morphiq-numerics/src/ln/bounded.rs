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
pub(crate) struct Ln;

#[cfg(feature = "simd")]
impl crate::lanes::Kernel for Ln {
    fn scalar(x: f64) -> f64 {
        ln(x)
    }

    #[inline(always)]
    fn lanes<K: morphiq_numerics_arch::Simd>(k: K, input: K::Array) -> K::Array {
        let ((s, lo, _), special) = super::lanes::fast_ln(k, &input);
        let mut out = k.store(k.add(s, lo));
        if special != 0 {
            for (i, value) in out.as_mut().iter_mut().enumerate() {
                if special >> i & 1 != 0 {
                    *value = super::ln(input.as_ref()[i]);
                }
            }
        }
        out
    }
}
