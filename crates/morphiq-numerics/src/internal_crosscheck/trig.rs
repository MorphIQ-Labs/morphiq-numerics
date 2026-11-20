//! Actual Payne–Hanek reduction results, including every binary64 binade.
//! These establish transcription agreement; error bounds are proved separately.
use super::{String, q256};
use crate::random::SplitMix64;
use crate::test_exact::{entries, word};
use std::fmt::Write as _;

fn emit(out: &mut String, bits: u64) {
    let x = f64::from_bits(bits);
    assert!(x.is_finite() && !x.is_sign_negative());
    let (quadrant, remainder) = crate::trig::reduce(x);
    writeln!(
        out,
        "trig_reduce {bits:016x} : {quadrant} {}",
        q256(remainder)
    )
    .unwrap();
}

pub(super) fn write(out: &mut String) {
    const FIXTURE: &str = include_str!("../../../reference/fixtures/sin_cos.json");
    for case in entries(FIXTURE, &["reduction"]) {
        emit(out, word(case, "x").to_bits());
    }
    for bits in [0, 1, (1_u64 << 52) - 1, 0x7fef_ffff_ffff_ffff] {
        emit(out, bits);
    }
    for bits in 0x3fe9_21fb_5444_2d10..=0x3fe9_21fb_5444_2d20 {
        emit(out, bits);
    }
    // Significand extremes at every binade.
    for exponent in 1..2047_u64 {
        for fraction in [0, 1, (1_u64 << 52) - 2, (1_u64 << 52) - 1] {
            emit(out, (exponent << 52) | fraction);
        }
    }
    // Single-bit carry boundaries at all 64 table-word alignments, including
    // the largest binade. The integer proof covers every other significand.
    for exponent in 1983..2047_u64 {
        for bit in 1..52 {
            for fraction in [(1_u64 << bit) - 1, 1_u64 << bit] {
                emit(out, (exponent << 52) | fraction);
            }
        }
    }
    // The nearest-integer witness and its adjacent binary64 inputs.
    for bits in 0x7506_ac5b_262c_a1fe..=0x7506_ac5b_262c_a200 {
        emit(out, bits);
    }
    let mut rng = SplitMix64::new(0x7472_6967_7265_6475);
    for _ in 0..4096 {
        let bits = rng.next_u64() & 0x7fff_ffff_ffff_ffff;
        if bits < 0x7ff0_0000_0000_0000 {
            emit(out, bits);
        }
    }
}
