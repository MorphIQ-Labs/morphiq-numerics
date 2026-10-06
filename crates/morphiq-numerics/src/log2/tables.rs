//! Constants of `log2` and `log10`, written by `generators/radix_constants.py`;
//! do not edit. `docs/log2.md` gives the derivation.

/// `1 / ln 2` as a double-word `INV_LN2_HI + INV_LN2_LO`; relative error below
/// 2^-110.1.
pub(super) const INV_LN2_HI: f64 = f64::from_bits(0x3ff71547652b82fe);
pub(super) const INV_LN2_LO: f64 = f64::from_bits(0x3c7777d0ffda0d24);
/// `1 / ln 2` as `m * 2^-127`; relative error below 2^-131.2.
pub(super) const INV_LN2_Q128: (u128, i32) = (0xb8aa3b295c17f0bbbe87fed0691d3e89, -127);

/// `1 / ln 10` as a double-word `INV_LN10_HI + INV_LN10_LO`; relative error below
/// 2^-109.8.
pub(super) const INV_LN10_HI: f64 = f64::from_bits(0x3fdbcb7b1526e50e);
pub(super) const INV_LN10_LO: f64 = f64::from_bits(0x3c695355baaafad3);
/// `1 / ln 10` as `m * 2^-129`; relative error below 2^-129.8.
pub(super) const INV_LN10_Q128: (u128, i32) = (0xde5bd8a937287195355baaafad33dc32, -129);
