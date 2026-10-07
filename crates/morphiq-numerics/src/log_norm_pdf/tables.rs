//! Constants of `log_norm_pdf`, written by `generators/log_norm_pdf_constants.py`;
//! do not edit. `C = ln √(2π)` as the double-word `C_HI + C_LO`;
//! `docs/log_norm_pdf.md` gives the derivation.
//!
//! `|C − C_HI − C_LO| < 2^-109·C`, and `C` lies `2^-54`
//! or more below the next rounding midpoint `C_HI + 2^−54`.

/// `RN(ln √(2π))` = 0.9189385332046728.
pub(super) const C_HI: f64 = f64::from_bits(0x3fed67f1c864beb5);
/// `RN(ln √(2π) − C_HI)` = -3.8782941580672414e-17.
pub(super) const C_LO: f64 = f64::from_bits(0xbc865b5a1b7ff5df);
