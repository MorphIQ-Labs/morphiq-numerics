//! Compare the actual checked-division scan and word exponents with Coq.
use super::{DoubleWord, SplitMix64, String};
use std::fmt::Write as _;

fn emit(out: &mut String, bits: [u64; 4]) {
    let (accepted, exponents) = DoubleWord::crosscheck_quotient_range(bits.map(f64::from_bits));
    write!(out, "quotient_range").unwrap();
    for b in bits {
        write!(out, " {b:016x}").unwrap();
    }
    write!(out, " : {}", u8::from(accepted)).unwrap();
    for e in exponents {
        write!(out, " {e}").unwrap();
    }
    writeln!(out).unwrap();
    emit_div(out, bits);
}

fn emit_div(out: &mut String, bits: [u64; 4]) {
    write!(out, "checked_div").unwrap();
    for b in bits {
        write!(out, " {b:016x}").unwrap();
    }
    match DoubleWord::crosscheck_division(bits.map(f64::from_bits)) {
        Some((h, l)) => writeln!(out, " : {h:016x} {l:016x}").unwrap(),
        None => writeln!(out, " : none").unwrap(),
    }
}

pub(super) fn write(out: &mut String) {
    // Every normal binade, its neighbours, and both signs. Place each word
    // in every slot to exercise the accumulation independently of order.
    for field in 1_u64..2047 {
        for bits in [(field << 52) - 1, field << 52, (field << 52) + 1] {
            for sign in [0, 1_u64 << 63] {
                for slot in 0..4 {
                    let mut words = [0, 1_u64 << 63, 1.0_f64.to_bits(), 0];
                    words[slot] = bits | sign;
                    emit(out, words);
                }
            }
        }
    }
    // All subnormal leading-bit positions, including exact powers and neighbours.
    for bit in 0..52 {
        for bits in [(1_u64 << bit) - 1, 1_u64 << bit, (1_u64 << bit) + 1] {
            emit(out, [bits, bits | (1_u64 << 63), 0, 1_u64 << 63]);
        }
    }
    // The guard is 2L+2H <= 917: both sides of the attainable boundary,
    // with different words supplying its minimum and maximum exponents.
    for l in 0_u64..=459 {
        for sum in [457_u64, 458, 459] {
            if l <= sum {
                let h = sum - l;
                let low = (1023 - l) << 52;
                let high = (1023 + h.saturating_sub(1)) << 52;
                emit(out, [low, high, low | (1_u64 << 63), high | (1_u64 << 63)]);
            }
        }
    }
    // Valid normalized operands with nonzero low words and varied signs.
    for field in 623_u64..=1423 {
        let x = (field << 52) | 0x0005_5555_5555_5555;
        let xl = (field - 60) << 52;
        let y = ((2046 - field) << 52) | 0x000a_aaaa_aaaa_aaaa;
        let yl = (2046 - field - 60) << 52;
        for sign in [0, 1_u64 << 63] {
            emit_div(out, [x | sign, xl, y, yl | sign]);
            emit_div(out, [x, xl | sign, y | sign, yl]);
            emit_div(out, [0, 1_u64 << 63, y | sign, yl]);
            emit_div(out, [x, xl, 0, 1_u64 << 63]);
        }
    }
    // Invalid operands, infinities, and both quiet and signalling NaNs.
    for special in [
        f64::INFINITY.to_bits(),
        f64::NEG_INFINITY.to_bits(),
        0x7ff8_1234_5678_9abc,
        0x7ff0_1234_5678_9abc,
    ] {
        for slot in 0..4 {
            let mut words = [1.0_f64.to_bits(), 0, 1.0_f64.to_bits(), 0];
            words[slot] = special;
            emit_div(out, words);
        }
    }
    let mut rng = SplitMix64::new(0xd171_5100_2026_1120);
    for _ in 0..4096 {
        // Clear one exponent bit so every random word is finite.
        emit(
            out,
            core::array::from_fn(|_| rng.next_u64() & !(1_u64 << 62)),
        );
    }
}
