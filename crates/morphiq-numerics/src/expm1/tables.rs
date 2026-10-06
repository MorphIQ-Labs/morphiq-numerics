//! Constants of `expm1`, written by `generators/expm1_constants.py`; do not
//! edit. `docs/expm1.md` gives the derivation.

/// The small-argument polynomial's tail (`generators/expm1_poly.sollya`): `c3..c9`
/// with relative error at most 0x1.0012p-54 on `2^-55 <= |x| <= 0.0312501`.
pub(super) const POLY: [f64; 7] = [
    f64::from_bits(0x3fc5555555555555),
    f64::from_bits(0x3fa5555555555559),
    f64::from_bits(0x3f8111111111bbb8),
    f64::from_bits(0x3f56c16c16b1d8ab),
    f64::from_bits(0x3f2a019ec4b15b40),
    f64::from_bits(0x3efa01c0085130cc),
    f64::from_bits(0x3ec7e0fb35411f23),
];
/// `1/m`, `m = 2..=16`, as `(m, e)` with value `m * 2^e`; relative error below
/// 2^-128.2.
pub(super) const RECIPROCALS: [(u128, i32); 15] = [
    (0x80000000000000000000000000000000, -128),
    (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab, -129),
    (0x80000000000000000000000000000000, -129),
    (0xcccccccccccccccccccccccccccccccd, -130),
    (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab, -130),
    (0x92492492492492492492492492492492, -130),
    (0x80000000000000000000000000000000, -130),
    (0xe38e38e38e38e38e38e38e38e38e38e4, -131),
    (0xcccccccccccccccccccccccccccccccd, -131),
    (0xba2e8ba2e8ba2e8ba2e8ba2e8ba2e8ba, -131),
    (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab, -131),
    (0x9d89d89d89d89d89d89d89d89d89d89e, -131),
    (0x92492492492492492492492492492492, -131),
    (0x88888888888888888888888888888889, -131),
    (0x80000000000000000000000000000000, -131),
];
