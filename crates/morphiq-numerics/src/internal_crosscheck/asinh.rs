//! Compare `asinh`'s fast path, rounding decision, exponential, accurate path
//! and public entry with their Coq transcription (`formal/asinh/AsinhKernel.v`),
//! extracted and run by `scripts/check_formal.sh`, so a difference in an
//! operation or its order shows before rounding can hide it.
use super::{SplitMix64, q256, unit};
use crate::q256::Q256;
use std::fmt::Write as _;
use std::string::String;
use std::vec::Vec;

/// `asinh(x) = x` up to this: the least argument the algorithm serves is above it.
const ASINH_IS_X: f64 = f64::from_bits(0x3e57_1374_4912_3ef6);

fn opt(v: Option<f64>) -> String {
    super::opt(v)
}

/// An argument above `ASINH_IS_X`: every binade, around the regions' edges
/// `2^-7` and `2^28`, the exponential's reduction ties, and the large range.
fn argument(rng: &mut SplitMix64) -> f64 {
    let w = rng.next_u64();
    let x = match w % 8 {
        0 | 1 => {
            // A binade from 2^-26 to 2^28.
            let e = -26 + ((w >> 8) % 54) as i32;
            (1.0 + unit(rng)) * f64::from_bits(((1023 + i64::from(e)) as u64) << 52)
        }
        2 => {
            // Around 2^-7.
            let step = ((w >> 8) % 13) as i64 - 6;
            f64::from_bits((f64::from_bits(0x3f80_0000_0000_0000).to_bits() as i64 + step) as u64)
        }
        3 => {
            // Around 2^28.
            let step = ((w >> 8) % 13) as i64 - 6;
            f64::from_bits((f64::from_bits(0x41b0_0000_0000_0000).to_bits() as i64 + step) as u64)
        }
        4 => {
            // The large range, to the largest finite.
            let e = 28 + ((w >> 8) % 996) as i32;
            (1.0 + unit(rng)) * f64::from_bits(((1023 + i64::from(e)) as u64) << 52)
        }
        5 => {
            // Around 1.
            0.25 + 4.0 * unit(rng)
        }
        _ => f64::from_bits(0x3e57_1374_4912_3ef6 + (rng.next_u64() % 0x40a0_0000_0000_0000)),
    };
    if x.is_finite() && x > ASINH_IS_X {
        x
    } else {
        1.5
    }
}

pub(super) fn write(out: &mut String) {
    let mut rng = SplitMix64::new(0x6173_696e_6863_0001);
    // The public entry: the specials, either sign, and the algorithm's domain.
    let mut entries: Vec<f64> = Vec::new();
    for x in [
        0.0_f64,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        ASINH_IS_X.next_down(),
        ASINH_IS_X,
        ASINH_IS_X.next_up(),
        0.5,
        f64::from_bits(0x3f80_0000_0000_0000).next_down(),
        f64::from_bits(0x3f80_0000_0000_0000),
        f64::from_bits(0x41b0_0000_0000_0000).next_down(),
        f64::from_bits(0x41b0_0000_0000_0000),
        1.0,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ] {
        entries.extend([x, -x]);
    }
    for _ in 0..6000 {
        let x = argument(&mut rng);
        entries.push(if rng.next_u64() & 1 == 0 { x } else { -x });
    }
    for x in entries {
        writeln!(
            out,
            "asinh_entry {:016x} : {:016x}",
            x.to_bits(),
            crate::asinh::asinh(x).to_bits()
        )
        .unwrap();
    }
    for _ in 0..6000 {
        let x = argument(&mut rng);
        let (y, decided) = crate::asinh::crosscheck_fast(x);
        writeln!(
            out,
            "asinh_fast {:016x} : {:016x} {:016x} {}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            opt(decided)
        )
        .unwrap();
    }
    // The accurate path's exponential on its own, since Newton's correction
    // hides it, and the accurate value from the fast value.
    for _ in 0..400 {
        let x = argument(&mut rng);
        let (y, _) = crate::asinh::crosscheck_fast(x);
        let start = Q256::from_f64(y.hi()).add(Q256::from_f64(y.lo()));
        let (m, k) = crate::asinh::crosscheck_exp(start);
        writeln!(out, "asinh_exp {} : {} {k}", q256(start), q256(m)).unwrap();
    }
    for _ in 0..600 {
        let x = argument(&mut rng);
        let (y, _) = crate::asinh::crosscheck_fast(x);
        writeln!(
            out,
            "asinh_accurate {:016x} {:016x} {:016x} : {}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            q256(crate::asinh::crosscheck_accurate(x, y))
        )
        .unwrap();
    }
}
