//! The normal family: the log density and scaled complementary error function.
//! Their derivations are in `docs/log_norm_pdf.md` and `docs/erfcx.md`.

pub use crate::log_norm_pdf::log_norm_pdf;

/// The scaled complementary error function.
pub use crate::erfcx::erfcx;

/// Apply [`erfcx`] to a slice, preserving the scalar result bits.
///
/// # Panics
/// If the input and output lengths differ.
pub fn erfcx_slice(x: &[f64], out: &mut [f64]) {
    assert_eq!(
        x.len(),
        out.len(),
        "erfcx_slice: slices of different lengths"
    );
    #[cfg(feature = "simd")]
    crate::lanes::map::<crate::erfcx::lanes::Erfcx>(x, out);
    #[cfg(not(feature = "simd"))]
    for (o, &x) in out.iter_mut().zip(x) {
        *o = erfcx(x);
    }
}
