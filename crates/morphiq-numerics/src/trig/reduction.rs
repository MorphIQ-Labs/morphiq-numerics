//! Payne-Hanek's constants for `sin` and `cos`, written by
//! `generators/trig_reduction.py`; do not edit. `docs/sin_cos.md` §3 gives the
//! derivation.

/// Every binary64 `x >= pi/4` has `|x (2/pi) - k| >= 2^-61.54` for every integer `k`:
/// the least, at `x = 6381956970095103 2^797`, by continued fractions.
pub(super) const FRACTION_BITS: u32 = 315;
/// `2/pi` to `1408` bits: `TWO_OVER_PI[i]` holds the weights
/// `2^-(64 i + 1)` to `2^-(64 i + 64)`, most significant first.
pub(super) const TWO_OVER_PI: [u64; 22] = [
    0xa2f9836e4e441529,
    0xfc2757d1f534ddc0,
    0xdb6295993c439041,
    0xfe5163abdebbc561,
    0xb7246e3a424dd2e0,
    0x06492eea09d1921c,
    0xfe1deb1cb129a73e,
    0xe88235f52ebb4484,
    0xe99c7026b45f7e41,
    0x3991d639835339f4,
    0x9c845f8bbdf9283b,
    0x1ff897ffde05980f,
    0xef2f118b5a0a6d1f,
    0x6d367ecf27cb09b7,
    0x4f463f669e5fea2d,
    0x7527bac7ebe5f17b,
    0x3d0739f78a5292ea,
    0x6bfb5fb11f8d5d08,
    0x56033046fc7b6bab,
    0xf0cfbc209af4361d,
    0xa9e391615ee61b08,
    0x6599855f14a06840,
];
/// `pi/2` as `m 2^-255`, `m` in four 64-bit limbs least significant first;
/// relative error below 2^-257.3.
pub(super) const HALF_PI: [u64; 4] = [
    0x020bbea63b139b22,
    0x29024e088a67cc74,
    0xc4c6628b80dc1cd1,
    0xc90fdaa22168c234,
];
pub(super) const HALF_PI_EXPONENT: i32 = -255;
