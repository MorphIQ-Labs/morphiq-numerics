//! Elementary functions, correctly rounded: each returns the binary64 number
//! nearest to the exact result, ties to even, on every target.
//!
//! Each function's derivation, with its certificates, is in `docs/`:
//! [`exp`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp.md),
//! [`exp2`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/exp2.md),
//! [`expm1`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/expm1.md),
//! [`ln` and `ln_1p`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/ln.md),
//! [`log2` and `log10`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/log2.md),
//! [`sin`, `cos`, `sincos` and `tan`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sin_cos.md),
//! [`sqrt`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/sqrt.md).
//!
//! [`exp_slice`], [`exp2_slice`], [`expm1_slice`], [`ln_slice`] and [`ln_1p_slice`] apply a function to every
//! element of a slice and return its bits exactly. With the `simd` feature they
//! evaluate several elements at once in SIMD lanes
//! ([`lanes`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md)),
//! which changes speed, never a result.

pub use crate::asin::asin;
pub use crate::asinh::asinh;
pub use crate::atan2::atan2;
pub use crate::exp::exp;
pub use crate::exp2::exp2;
pub use crate::expm1::expm1;
pub use crate::ln::{ln, ln_1p};
pub use crate::log2::{log2, log10};
pub use crate::sqrt::sqrt;
pub use crate::trig::{cos, sin, sincos, tan};

/// Batched entry points: `$name(x, out)` sets `out[i] = $scalar(x[i])`, bit for
/// bit, on every target and with or without the `simd` feature.
macro_rules! batched {
    ($(#[$doc:meta])* $name:ident, $scalar:ident, $kernel:path) => {
        $(#[$doc])*
        ///
        /// # Panics
        ///
        /// If `x` and `out` have different lengths.
        pub fn $name(x: &[f64], out: &mut [f64]) {
            assert_eq!(
                x.len(),
                out.len(),
                concat!(stringify!($name), ": slices of different lengths")
            );
            #[cfg(feature = "simd")]
            crate::lanes::map::<$kernel>(x, out);
            #[cfg(not(feature = "simd"))]
            for (o, &x) in out.iter_mut().zip(x) {
                *o = $scalar(x);
            }
        }
    };
}

batched!(
    /// [`exp`] of every element of `x`, written to `out`: `out[i]` is
    /// `exp(x[i])`, bit for bit.
    ///
    /// With the `simd` feature the elements are evaluated in SIMD lanes, each
    /// lane performing `exp`'s fast path operation for operation; a lane the
    /// fast path doesn't decide calls `exp` itself
    /// ([docs/lanes.md](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md)).
    exp_slice,
    exp,
    crate::exp::lanes::Exp
);

batched!(
    /// [`ln`] of every element of `x`, written to `out`: `out[i]` is
    /// `ln(x[i])`, bit for bit.
    ///
    /// With the `simd` feature the elements are evaluated in SIMD lanes, each
    /// lane performing `ln`'s fast path operation for operation; a lane the
    /// fast path doesn't decide calls `ln` itself
    /// ([docs/lanes.md](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md)).
    ln_slice,
    ln,
    crate::ln::lanes::Ln
);

batched!(
    /// [`ln_1p`] of every element of `x`, written to `out`: `out[i]` is
    /// `ln_1p(x[i])`, bit for bit.
    ///
    /// With the `simd` feature the elements are evaluated in SIMD lanes, each
    /// lane performing `ln_1p`'s fast path operation for operation; a lane the
    /// fast path doesn't decide calls `ln_1p` itself
    /// ([docs/lanes.md](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md)).
    ln_1p_slice,
    ln_1p,
    crate::ln::lanes::Ln1p
);

batched!(
    /// [`exp2`] of every element of `x`, written to `out`, bit for bit.
    /// With `simd`, stages A and B run in lanes; undecided lanes call [`exp2`].
    exp2_slice, exp2, crate::exp2::lanes::Exp2
);

batched!(
    /// [`expm1`] of every element of `x`, written to `out`, bit for bit.
    /// With `simd`, the small-argument polynomial and stages A and B run in
    /// lanes; undecided lanes call [`expm1`].
    expm1_slice, expm1, crate::expm1::lanes::Expm1
);

batched!(
    /// [`asin`] of every element of `x`, written to `out`, bit for bit.
    /// With `simd`, the reduction, the series and the rounding test run in
    /// lanes; a lane the screen or the test doesn't settle calls [`asin`].
    asin_slice, asin, crate::asin::lanes::Asin
);

batched!(
    /// [`asinh`] of every element of `x`, written to `out`, bit for bit.
    /// With `simd`, the series, the logarithm of `x + √(x² + 1)`, the large
    /// form and the rounding test run in lanes; a lane the screen or the test
    /// doesn't settle calls [`asinh`].
    asinh_slice, asinh, crate::asinh::lanes::Asinh
);

/// [`atan2`] of every pair `(y[i], x[i])`, written to `out`: `out[i]` is
/// `atan2(y[i], x[i])`, bit for bit, on every target and with or without the
/// `simd` feature.
///
/// With `simd` the pairs are evaluated in SIMD lanes, each lane performing
/// `atan2`'s fast path operation for operation; a lane the screen or the
/// rounding test doesn't settle calls [`atan2`]
/// ([docs/lanes.md](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md)).
///
/// # Panics
///
/// If `y`, `x` and `out` don't have the same length.
pub fn atan2_slice(y: &[f64], x: &[f64], out: &mut [f64]) {
    assert!(
        y.len() == x.len() && x.len() == out.len(),
        "atan2_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map2::<crate::atan2::lanes::Atan2>(y, x, out);
    #[cfg(not(feature = "simd"))]
    for ((o, &y), &x) in out.iter_mut().zip(y).zip(x) {
        *o = atan2(y, x);
    }
}
