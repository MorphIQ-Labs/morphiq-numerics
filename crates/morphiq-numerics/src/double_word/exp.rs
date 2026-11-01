//! The double-word exponential, `exp(x) = value · 2^n` for a double-word `x`.
//!
//! The derivation, its bound and its domain are in
//! [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md#exponential).
//! In outline: `n = round(x · 1024/ln 2)`; a three-part Cody–Waite reduction
//! gives `r = x - n·ln(2)/1024` with `|r| <= ln(2)/2048` (plus rounding); a
//! degree-7 double-word Horner evaluation gives `exp(r)`, each step one
//! DWTimesDW1 product and DWPlusFP additions of the coefficient's words; and the generated
//! double-word table entry `exp(j·ln(2)/1024)`, `j = n mod 1024`, scales it,
//! leaving the binary exponent `floor(n/1024)` to the caller.
//!
//! Every product is one of the published double-word algorithms, operation
//! for operation; only the source of each exact product varies by target, and
//! every source returns the same words (ADR 0002): a fused multiply-add's error
//! term equals Dekker's on [`two_prod`](crate::eft::two_prod)'s proved domain.

use super::DoubleWord;
use super::exp_tables::{
    INV, L1, L2, L3, LIMIT, LOW_FLOOR, R_FLOOR, SHIFTER, TABLE, TAYLOR, TINY, V_FLOOR,
};

// Generated thresholds (`exp_tables.rs`), shared with the Coq transcription:
// - `SHIFTER = 1.5 · 2^52`: adding and subtracting it rounds to the nearest
//   integer for arguments below `2^51` in magnitude;
// - `LIMIT = 1455`: inputs at or above it return `None`; it keeps `|n| < 2^22`,
//   so `n·L1` and `n·L2` are exact, and the binary exponent within `±2099`;
// - `TINY = 2^-60`: below it `exp(x) = 1 + x` within `x²`, under the bound;
// - `LOW_FLOOR = 1e-300`, `R_FLOOR = 1e-271`, `V_FLOOR = 1e-60`: a reduced
//   argument's trailing word, a reduced argument, and a Horner value's trailing
//   word below these are dropped, so every product of a leading and a trailing
//   word is zero or normal as the double-word multiplication bound requires; the
//   effects are below `2^-990`, `2^-900` and `2^-187` relative.

/// The source of an exact product `(RN(a·b), a·b - RN(a·b))`.
pub(super) trait ExactProduct {
    fn two_prod(&self, a: f64, b: f64) -> (f64, f64);
}

/// [`crate::eft::two_prod_d`]: a hardware fused multiply-add in builds that
/// target one, Dekker's product otherwise; the same words either way.
struct Separate;
impl ExactProduct for Separate {
    #[inline(always)]
    fn two_prod(&self, a: f64, b: f64) -> (f64, f64) {
        crate::eft::two_prod_d(a, b)
    }
}

#[inline(always)]
fn word(pair: [u64; 2]) -> DoubleWord {
    DoubleWord::from_words(f64::from_bits(pair[0]), f64::from_bits(pair[1]))
}

/// The kernel, generic over the exact-product source so one operation
/// sequence serves every target.
#[inline(always)]
fn kernel<P: ExactProduct>(x: DoubleWord, p: &P) -> Option<(DoubleWord, i32)> {
    let hi = x.hi;
    if hi.is_nan() || hi.abs() >= LIMIT {
        return None;
    }
    if hi.abs() < TINY {
        return Some((x.add_f64(1.0), 0));
    }
    let t = hi * INV + SHIFTER;
    let n = t - SHIFTER;
    #[allow(clippy::cast_possible_truncation)] // |n| < 2^22, an exact integer
    let index = n as i64;
    #[allow(clippy::cast_sign_loss)] // masked to 0..1024
    let j = (index & 1023) as usize;
    #[allow(clippy::cast_possible_truncation)] // |index >> 10| <= 2099
    let exponent = (index >> 10) as i32;
    // n·L1 and n·L2 are exact; n·L3 is taken exactly and subtracted word by
    // word. Every step is DWPlusFP, whose output is proved a double word.
    let (q_hi, q_lo) = p.two_prod(n, L3);
    let r = x
        .add_f64(-(n * L1))
        .add_f64(-(n * L2))
        .add_f64(-q_lo)
        .add_f64(-q_hi);
    if r.hi.abs() < R_FLOOR {
        // exp(r) = 1 within 2^-900: the table entry itself, the same words the
        // Horner steps and final product would give for r = 0.
        return Some((word(TABLE[j]), exponent));
    }
    let r = if r.lo.abs() < LOW_FLOOR {
        DoubleWord::from_f64(r.hi)
    } else {
        r
    };
    // Horner steps add each coefficient's low then high word by DWPlusFP; the
    // low words of 1/0!, 1/1! and 1/2! are zero.
    let mut v = word(TAYLOR[7]);
    for k in (0..7).rev() {
        let [high, low] = TAYLOR[k];
        v = v.mul_with(r, p);
        if k >= 3 {
            v = v.add_f64(f64::from_bits(low));
        }
        v = v.add_f64(f64::from_bits(high));
        if v.lo.abs() < V_FLOOR {
            v = DoubleWord::from_f64(v.hi);
        }
    }
    Some((word(TABLE[j]).mul_with(v, p), exponent))
}

impl DoubleWord {
    /// `exp(self)` as `(value, n)` with `exp(self) ≈ value · 2^n`, or `None`
    /// when `|self.hi()| >= 1455` or `self` is not finite.
    ///
    /// `value` is a double-word number in `[0.9996, 2.0008)`, with relative
    /// error as stated in [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md#exponential);
    /// `n` is in `[-2099, 2099]`. The scale is left to the caller, so
    /// `value · 2^n` may lie outside binary64's range: a caller multiplying it
    /// into a quantity of opposite scale keeps the product finite.
    ///
    /// Every exact product inside comes from a hardware fused multiply-add
    /// where the build or the processor has one, and from Dekker's product
    /// elsewhere; the result is the same on every target.
    #[must_use]
    #[inline]
    pub fn exp_split(self) -> Option<(Self, i32)> {
        #[cfg(all(
            feature = "simd",
            feature = "std",
            target_arch = "x86_64",
            not(target_feature = "fma")
        ))]
        {
            use morphiq_numerics_arch::Simd;
            match BACKEND.get() {
                Some(Some(k)) => k.vectorize(Fused(self)),
                Some(None) => kernel(self, &Separate),
                None => initialize(self),
            }
        }
        #[cfg(not(all(
            feature = "simd",
            feature = "std",
            target_arch = "x86_64",
            not(target_feature = "fma")
        )))]
        {
            kernel(self, &Separate)
        }
    }
}

/// On x86-64 without a target FMA, one runtime dispatch per call runs the
/// whole kernel in an FMA-enabled body, as the bounded `ln` does for its
/// residual.
#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
static BACKEND: std::sync::OnceLock<Option<morphiq_numerics_arch::Avx2>> =
    std::sync::OnceLock::new();

#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
#[cold]
#[inline(never)]
fn initialize(x: DoubleWord) -> Option<(DoubleWord, i32)> {
    use morphiq_numerics_arch::Simd;
    match *BACKEND.get_or_init(morphiq_numerics_arch::Avx2::try_new) {
        Some(k) => k.vectorize(Fused(x)),
        None => kernel(x, &Separate),
    }
}

#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
struct Fused(DoubleWord);

/// A hardware fused multiply-add's error term inside the FMA-enabled body.
#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
struct LaneProduct<K>(K);

#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
impl<K: morphiq_numerics_arch::Simd> ExactProduct for LaneProduct<K> {
    #[inline(always)]
    fn two_prod(&self, a: f64, b: f64) -> (f64, f64) {
        let k = self.0;
        let product = a * b;
        match k.mul_add(k.splat(a), k.splat(b), k.splat(-product)) {
            Some(error) => (product, k.store(error).as_ref()[0]),
            None => crate::eft::two_prod(a, b),
        }
    }
}

#[cfg(all(
    feature = "simd",
    feature = "std",
    target_arch = "x86_64",
    not(target_feature = "fma")
))]
impl morphiq_numerics_arch::WithSimd for Fused {
    type Output = Option<(DoubleWord, i32)>;
    #[inline(always)]
    fn with<K: morphiq_numerics_arch::Simd>(self, k: K) -> Self::Output {
        kernel(self.0, &LaneProduct(k))
    }
}

#[cfg(test)]
mod tests {
    use super::{DoubleWord, ExactProduct, Separate, kernel};

    /// Dekker's product, always: the reference the other sources must match.
    struct Dekker;
    impl ExactProduct for Dekker {
        fn two_prod(&self, a: f64, b: f64) -> (f64, f64) {
            crate::eft::two_prod(a, b)
        }
    }

    fn inputs() -> impl Iterator<Item = DoubleWord> {
        let mut word = 0x2660_0001_dead_beef_u64;
        core::iter::from_fn(move || {
            word ^= word << 13;
            word ^= word >> 7;
            word ^= word << 17;
            #[allow(clippy::cast_precision_loss)]
            let unit = (word >> 11) as f64 / (1u64 << 53) as f64;
            let hi = unit * 2900.0 - 1450.0;
            #[allow(clippy::cast_precision_loss)]
            let tail = ((word & 0xffff) as f64 / 65536.0 - 0.5) * hi.abs() * 2e-16;
            Some(DoubleWord::sum(hi, tail))
        })
    }

    #[test]
    fn every_product_source_returns_the_same_words() {
        for x in inputs().take(100_000) {
            let reference = kernel(x, &Dekker).unwrap();
            assert_eq!(kernel(x, &Separate), Some(reference), "{x:?}");
            assert_eq!(x.exp_split(), Some(reference), "{x:?}");
        }
    }

    #[test]
    fn the_domain_and_its_edges_are_explicit() {
        assert_eq!(DoubleWord::from_f64(1455.0).exp_split(), None);
        assert_eq!(DoubleWord::from_f64(-1455.0).exp_split(), None);
        assert_eq!(DoubleWord::from_f64(f64::NAN).exp_split(), None);
        assert_eq!(DoubleWord::from_f64(f64::INFINITY).exp_split(), None);
        assert!(DoubleWord::from_f64(1454.999).exp_split().is_some());
        let (one, zero) = DoubleWord::from_f64(0.0).exp_split().unwrap();
        assert_eq!((one.hi(), one.lo(), zero), (1.0, 0.0, 0));
        let (value, n) = DoubleWord::from_f64(-0.0).exp_split().unwrap();
        assert_eq!((value.hi(), n), (1.0, 0));
    }

    #[test]
    fn values_and_exponents_stay_in_their_stated_ranges() {
        for x in inputs().take(100_000) {
            let (value, n) = x.exp_split().unwrap();
            assert!((0.9996..2.0008).contains(&value.hi()), "{x:?} -> {value:?}");
            assert!((-2099..=2099).contains(&n), "{x:?} -> {n}");
        }
    }
}
