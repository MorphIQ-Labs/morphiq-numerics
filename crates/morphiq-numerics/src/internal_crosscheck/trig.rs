//! Actual Payne–Hanek reduction results, including every binary64 binade.
//! These establish transcription agreement; error bounds are proved separately.
use super::{String, q256};
use crate::q256::Q256;
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

fn emit_residual(out: &mut String, head: f64, low: f64) {
    let t = crate::double_word::DoubleWord::sum(head, low);
    write!(
        out,
        "trig_residual {:016x} {:016x} :",
        t.hi().to_bits(),
        t.lo().to_bits()
    )
    .unwrap();
    for result in crate::trig::residual_crosscheck(t) {
        write!(out, " {result:016x}").unwrap();
    }
    writeln!(out).unwrap();
}

fn emit_input(out: &mut String, r: Q256) {
    for signed in [r, r.neg()] {
        write!(out, "trig_input {} :", q256(signed)).unwrap();
        for result in crate::trig::input_crosscheck(signed) {
            write!(out, " {result:016x}").unwrap();
        }
        writeln!(out).unwrap();
    }
}

fn emit_mul(out: &mut String, xh: f64, xl: f64, yh: f64, yl: f64) {
    use crate::double_word::DoubleWord;
    let x = DoubleWord::sum(xh, xl);
    let y = DoubleWord::sum(yh, yl);
    let z = x.mul(y);
    writeln!(
        out,
        "trig_mul {:016x} {:016x} {:016x} {:016x} : {:016x} {:016x}",
        x.hi().to_bits(),
        x.lo().to_bits(),
        y.hi().to_bits(),
        y.lo().to_bits(),
        z.hi().to_bits(),
        z.lo().to_bits()
    )
    .unwrap();
}

fn write_multiply(out: &mut String) {
    // Actual table/residual products, including r = 1/64 + 2^-255:
    // S.hi * CM.lo is then nonzero and subnormal. Both residual signs,
    // table row zero, and fine low words are retained.
    for i in [0, 1, 25, 50] {
        let table = crate::trig::table_crosscheck(i).map(f64::from_bits);
        for exponent in [-320, -300, -270, -260, -255, -250, -200, -100, -60, -7] {
            let head = f64::from_bits(((exponent + 1023) as u64) << 52);
            for sign in [1.0, -1.0] {
                let t = crate::double_word::DoubleWord::sum(sign * head, 0.0);
                let residual = crate::trig::residual_crosscheck(t).map(f64::from_bits);
                for a in [4, 6] {
                    for b in [4, 6] {
                        emit_mul(out, table[a], table[a + 1], residual[b], residual[b + 1]);
                    }
                }
            }
        }
    }
    // The theorem's head-product floor, normal/subnormal cross products,
    // both signs, exact zeros and halfway normalization boundaries.
    for exponent in [-900, -899, -640, -450, -1, 0, 508] {
        let head = f64::from_bits(((exponent + 1023) as u64) << 52);
        let half_ulp = f64::from_bits(((exponent - 53 + 1023) as u64) << 52);
        for low in [0.0, half_ulp, -half_ulp] {
            for tiny in [0, 1, (1_u64 << 52) - 1, 1_u64 << 52, 970_u64 << 52] {
                let tiny = f64::from_bits(tiny);
                for sign in [1.0, -1.0] {
                    emit_mul(out, sign * head, low, 1.0, tiny);
                    emit_mul(out, 1.0, tiny, sign * head, low);
                }
            }
        }
    }
    for zero in [0.0, -0.0] {
        emit_mul(out, zero, zero, 1.0, f64::from_bits(1));
        emit_mul(out, 1.0, f64::from_bits(1), zero, zero);
    }
}

pub(super) fn write(out: &mut String) {
    write_multiply(out);
    // Table points, halfway index ties and their binary64 neighbours. The
    // fine Q256 offsets exercise a nonzero low word when the head is exact.
    for k in 0..=100 {
        let point = f64::from(k) * 0.007_812_5;
        let bits = point.to_bits();
        for nearby in bits.saturating_sub(2)..=bits + 2 {
            emit_input(out, Q256::from_f64(f64::from_bits(nearby)));
        }
        for exponent in [-60, -64, -100, -200, -255] {
            let delta = Q256::from_f64(f64::from_bits(((exponent + 1023) as u64) << 52));
            let base = Q256::from_f64(point);
            emit_input(out, base.add(delta));
            emit_input(out, base.add(delta.neg()));
        }
    }
    // Every input binade in the proved split domain, with retained Q256
    // low bits and with near-rounding-boundary significands.
    for exponent in -319..=-256 {
        for limbs in [[1, 0, 0, 1 << 63], [u64::MAX; 4]] {
            emit_input(out, Q256::new(false, limbs, exponent));
        }
    }
    // Actual Payne–Hanek inputs cover all normal binary64 exponent fields.
    for exponent in 1023..2047_u64 {
        let (_, r) = crate::trig::reduce(f64::from_bits((exponent << 52) | 0x0005_a37c_19d2_ef04));
        emit_input(out, r);
    }
    // Regular residuals with normalized low words of either sign, including
    // half-ulp ties; tiny residuals have a zero low word at the table point.
    for exponent in 963..=1016_u64 {
        for fraction in [0, 1, (1_u64 << 52) - 2, (1_u64 << 52) - 1] {
            let head = f64::from_bits((exponent << 52) | fraction);
            if head <= 0.007_812_6 {
                let half_ulp = f64::from_bits((exponent - 53) << 52);
                for low in [0.0, half_ulp, -half_ulp, 0.5 * half_ulp, -0.5 * half_ulp] {
                    emit_residual(out, head, low);
                    emit_residual(out, -head, -low);
                }
            }
        }
    }
    for exponent in 703..963_u64 {
        for fraction in [0, (1_u64 << 52) - 1] {
            let head = f64::from_bits((exponent << 52) | fraction);
            emit_residual(out, head, 0.0);
            emit_residual(out, -head, -0.0);
        }
    }
    // Dense significands in the binades where the cosine tail crosses zero,
    // subnormal and normal rounding regions. Inputs are seeded, not outputs.
    let mut tiny_rng = SplitMix64::new(0x7472_6967_7469_6e79);
    for exponent in 753..=770_u64 {
        for _ in 0..32 {
            let fraction = tiny_rng.next_u64() & ((1_u64 << 52) - 1);
            let head = f64::from_bits((exponent << 52) | fraction);
            emit_residual(out, head, 0.0);
            emit_residual(out, -head, -0.0);
        }
    }
    for head in [0.0, -0.0, 0.007_812_6, -0.007_812_6] {
        emit_residual(out, head, 0.0);
    }

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
