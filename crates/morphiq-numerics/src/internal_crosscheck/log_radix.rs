//! Unrounded radix-log paths: oracle fixtures, exact powers, reduction-table
//! boundaries and exponent extremes. These compare actual Rust Q128 results
//! with the extracted reconstruction; they are not independent error oracles.
use super::{String, q128};
use crate::test_exact::{entries, word};
use std::fmt::Write as _;

fn emit(out: &mut String, bits: u64) {
    let x = f64::from_bits(bits);
    assert!(x.is_finite() && x > 0.0);
    let (radix2, radix10) = crate::log2::crosscheck_accurate(x);
    writeln!(out, "log2_accurate {bits:016x} : {}", q128(radix2)).unwrap();
    writeln!(out, "log10_accurate {bits:016x} : {}", q128(radix10)).unwrap();
}

pub(super) fn write(out: &mut String) {
    const FIXTURE: &str = include_str!("../../../reference/fixtures/log2_log10.json");
    for name in ["log2", "log10"] {
        for case in entries(FIXTURE, &["precise", name]) {
            emit(out, word(case, "x").to_bits());
        }
    }
    // Every representable power of two, including all subnormal powers and
    // one (zero intermediate), exercises exact integer reconstruction.
    for exponent in 1..2047_u64 {
        emit(out, exponent << 52);
    }
    for bit in 0..52 {
        emit(out, 1_u64 << bit);
    }
    // Both sides of all table boundaries, including the y -> y/2 switch,
    // at the minimum, central and maximum normal exponent fields.
    for exponent in [1, 1022, 1023, 1024, 2046_u64] {
        for index in 0..128_u64 {
            let boundary = (exponent << 52) + (index << 45);
            for bits in [boundary - 1, boundary, boundary + 1] {
                emit(out, bits);
            }
        }
    }
    emit(out, 0x7fef_ffff_ffff_ffff);
}
