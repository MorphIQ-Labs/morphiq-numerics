//! Actual Payne–Hanek reduction results, including every binary64 binade.
//! These establish transcription agreement; error bounds are proved separately.
use super::{String, q256};
use crate::random::SplitMix64;
use crate::test_exact::{entries, word};
use std::fmt::Write as _;

fn emit_series(out: &mut String, bits: u64) {
    let (_, remainder) = crate::trig::reduce(f64::from_bits(bits));
    // Exercise both signs of the actual full-precision reduction, including zero.
    for r in [remainder, remainder.neg()] {
        let (s, c) = crate::trig::accurate_sin_cos(r);
        writeln!(out, "trig_series {} : {} {}", q256(r), q256(s), q256(c)).unwrap();
    }
}

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

fn emit_tail(out: &mut String, bits: u64) {
    for sign in [0, 1_u64 << 63] {
        let bits = bits | sign;
        write!(out, "trig_tail {bits:016x} :").unwrap();
        for result in crate::trig::tail_crosscheck(f64::from_bits(bits)) {
            write!(out, " {result:016x}").unwrap();
        }
        writeln!(out).unwrap();
    }
}

pub(super) fn write(out: &mut String) {
    // Both signs, zero/subnormals, every residual binade, and both branch edges.
    for bits in [0, 1, (1_u64 << 52) - 1] {
        emit_tail(out, bits);
    }
    let upper = 0.007_812_6_f64.to_bits();
    for exponent in 1..=1016_u64 {
        for fraction in [0, 1, (1_u64 << 52) - 2, (1_u64 << 52) - 1] {
            let bits = (exponent << 52) | fraction;
            if bits <= upper {
                emit_tail(out, bits);
            }
        }
    }
    for edge in [(963_u64 << 52), upper] {
        for bits in edge - 2..=edge + 2 {
            if bits <= upper {
                emit_tail(out, bits);
            }
        }
    }

    for i in 0..51 {
        write!(out, "trig_table {i} :").unwrap();
        for bits in crate::trig::table_crosscheck(i) {
            write!(out, " {bits:016x}").unwrap();
        }
        writeln!(out).unwrap();
    }
    const FIXTURE: &str = include_str!("../../../reference/fixtures/sin_cos.json");
    for case in entries(FIXTURE, &["reduction"]) {
        let bits = word(case, "x").to_bits();
        emit(out, bits);
        emit_series(out, bits);
    }
    for bits in [0, 1, (1_u64 << 52) - 1, 0x7fef_ffff_ffff_ffff] {
        emit(out, bits);
        emit_series(out, bits);
    }
    for bits in 0x3fe9_21fb_5444_2d10..=0x3fe9_21fb_5444_2d20 {
        emit(out, bits);
        emit_series(out, bits);
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
        emit_series(out, bits);
    }
    write_selected(out);
    write_reciprocals(out);
    let mut rng = SplitMix64::new(0x7472_6967_7265_6475);
    for i in 0..4096 {
        let bits = rng.next_u64() & 0x7fff_ffff_ffff_ffff;
        if bits < 0x7ff0_0000_0000_0000 {
            emit(out, bits);
            if i < 256 {
                emit_series(out, bits);
            }
        }
    }
}

// Selection and final conversion are checked on every quadrant/sign/function,
// plus threshold neighbors, subnormals, extremes and seeded ordinary inputs.
fn write_selected(out: &mut String) {
    let mut inputs = std::vec![0, 1, (1_u64 << 52) - 1, 1_u64 << 52];
    for center in [
        0x3e4d_12ed_0af1_a27e, // tan(x) = x cutoff
        0x3fe9_21fb_5444_2d18, // pi/4
        0x3ff9_21fb_5444_2d18, // pi/2
        0x4009_21fb_5444_2d18, // pi
        0x4012_d97c_7f33_21d2, // 3*pi/2
        0x4019_21fb_5444_2d18, // 2*pi
        0x7506_ac5b_262c_a1ff, // near an integer multiple of pi/2
        0x7fef_ffff_ffff_fffe,
    ] {
        inputs.extend([center - 1, center, center + 1]);
    }
    let mut rng = SplitMix64::new(0x7472_6967_7365_6c65);
    for _ in 0..64 {
        let bits = rng.next_u64() & 0x7fff_ffff_ffff_ffff;
        if bits < 0x7ff0_0000_0000_0000 {
            inputs.push(bits);
        }
    }
    let mut covered = [[[false; 2]; 2]; 4];
    for bits in inputs {
        for signed in [bits, bits | (1_u64 << 63)] {
            let x = f64::from_bits(signed);
            let negative = x < 0.0;
            let (num, den, negate, tan) = crate::trig::tan_accurate_crosscheck(x);
            writeln!(
                out,
                "trig_tan_parts {bits:016x} {} : {} {} {}",
                u8::from(negative),
                q256(num),
                q256(den),
                u8::from(negate)
            )
            .unwrap();
            writeln!(
                out,
                "trig_tan_accurate {bits:016x} {} : {} {:016x}",
                u8::from(negative),
                q256(tan),
                tan.to_f64().to_bits()
            )
            .unwrap();
            for cosine in [false, true] {
                let (k, use_cos, negate, y) = crate::trig::accurate_crosscheck(x, cosine);
                covered[k as usize][usize::from(negative)][usize::from(cosine)] = true;
                writeln!(
                    out,
                    "trig_select {k} {} {} : {} {}",
                    u8::from(negative),
                    u8::from(cosine),
                    u8::from(use_cos),
                    u8::from(negate)
                )
                .unwrap();
                writeln!(
                    out,
                    "trig_accurate {bits:016x} {} {} : {} {:016x}",
                    u8::from(negative),
                    u8::from(cosine),
                    q256(y),
                    y.to_f64().to_bits()
                )
                .unwrap();
            }
        }
    }
    assert!(covered.into_iter().flatten().flatten().all(|hit| hit));
}

// Reuse the existing q_recip extraction entry: the shared Rust operation has
// the same full-domain contract whichever kernel calls it. Every sampled
// significand is normalized, and no unsupported reciprocal is evaluated.
fn write_reciprocals(out: &mut String) {
    use crate::q256::Q256;
    let emit = |out: &mut String, c: Q256| {
        assert!(c.to_f64().is_finite());
        writeln!(out, "asin_recip {} : {}", q256(c), q256(c.recip())).unwrap();
    };
    // Input minimum, the trig/asin denominator scales, ordinary binades,
    // normal/subnormal seed transition and finite-conversion limit.
    for top in [
        -1022, -1021, -1000, -65, -64, -63, -28, -1, 0, 1, 500, 1020, 1021, 1022, 1023,
    ] {
        let upper = if top == 1023 {
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX - (1 << 10)]
        } else {
            [u64::MAX; 4]
        };
        for m in [
            [0, 0, 0, 1 << 63],
            [1, 0, 0, 1 << 63],
            [0, 0, 0, (1 << 63) | (1 << 10)], // binary64 rounding tie
            [1, 0, 0, (1 << 63) | (1 << 10)], // just above the tie
            upper,
        ] {
            for negative in [false, true] {
                emit(out, Q256::new(negative, m, top - 255));
            }
        }
    }
    let mut rng = SplitMix64::new(0x7472_6967_7265_6369);
    for _ in 0..64 {
        let m = [
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64() | (1 << 63),
        ];
        let top = i32::try_from(rng.next_u64() % 2046).unwrap() - 1022;
        for negative in [false, true] {
            let c = Q256::new(negative, m, top - 255);
            if c.to_f64().is_finite() {
                emit(out, c);
            }
        }
    }
}
