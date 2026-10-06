//! Constants of `exp2`, written by `generators/radix_constants.py`; do not
//! edit. `docs/exp2.md` gives the derivation.

/// `RN(ln 2)` and `RN(ln 2 - LN2_HI)`: together within 2^-109.9 relative of `ln 2`.
pub(super) const LN2_HI: f64 = f64::from_bits(0x3fe62e42fefa39ef);
pub(super) const LN2_LO: f64 = f64::from_bits(0x3c7abc9e3b39803f);
/// `ln 2` as `m * 2^-128`; relative error below 2^-129.4.
pub(super) const LN2_Q128: (u128, i32) = (0xb17217f7d1cf79abc9e3b39803f2f6af, -128);
