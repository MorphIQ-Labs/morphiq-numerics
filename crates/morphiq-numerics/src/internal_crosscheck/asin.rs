//! Compare `asin`'s reduction, series, fast path, accurate path and public
//! entry with their Coq transcription (`formal/asin/AsinKernel.v`), extracted
//! and run by `scripts/check_formal.sh`, so a difference in an operation or its
//! order shows before rounding can hide it.
use super::{SplitMix64, q256, unit};
use crate::double_word::DoubleWord;
use std::fmt::Write as _;
use std::string::String;
use std::vec::Vec;

/// `asin(x) = x` below this: the least argument the algorithm serves.
const ASIN_IS_X: f64 = f64::from_bits(0x3e57_1374_4912_3ef6);
/// The largest binary64 below `√½`.
const SPLIT: f64 = f64::from_bits(0x3fe6_a09e_667f_3bcc);

fn opt(v: Option<f64>) -> String {
    super::opt(v)
}

/// An argument in `[ASIN_IS_X, 1)`: every binade, around the table's
/// boundaries `k/64` and `SPLIT`, next to 1, and across `[1/2, 1)`.
fn argument(rng: &mut SplitMix64) -> f64 {
    let w = rng.next_u64();
    let x = match w % 8 {
        0 | 1 => {
            // A binade from 2^-26 to 1.
            let e = -26 + ((w >> 8) % 26) as i32;
            (1.0 + unit(rng)) * f64::from_bits(((1023 + i64::from(e)) as u64) << 52)
        }
        2 => {
            // Next to a multiple of 1/64, either side of the rounding of 64 z.
            let k = 1 + (w >> 8) % 45;
            let a = k as f64 * 0.015_625;
            let step = ((w >> 16) % 9) as i64 - 4;
            f64::from_bits((a.to_bits() as i64 + step) as u64)
        }
        3 => {
            // Next to the midpoints between multiples of 1/64, where the index rounds.
            let k = (w >> 8) % 45;
            let a = (k as f64 + 0.5) * 0.015_625;
            let step = ((w >> 16) % 9) as i64 - 4;
            f64::from_bits((a.to_bits() as i64 + step) as u64)
        }
        4 => {
            // Around SPLIT.
            let step = ((w >> 8) % 13) as i64 - 6;
            f64::from_bits((SPLIT.to_bits() as i64 + step) as u64)
        }
        5 => {
            // Next to 1.
            1.0 - (1.0 + unit(rng))
                * f64::from_bits(((1023 - 2 - ((w >> 8) % 51) as i64) as u64) << 52)
        }
        _ => 0.5 + 0.5 * unit(rng),
    };
    if (ASIN_IS_X..1.0).contains(&x) {
        x
    } else {
        0.75
    }
}

/// A double-word `z` in `[0, SPLIT]`: a leading word anywhere in the series'
/// domain and a trailing word of up to half its ulp, with either sign.
fn series_argument(rng: &mut SplitMix64) -> DoubleWord {
    let w = rng.next_u64();
    let hi = match w % 4 {
        0 => unit(rng) * 0.0078125,
        1 => {
            let k = 1 + (w >> 8) % 45;
            let step = ((w >> 16) % 5) as i64 - 2;
            f64::from_bits(((k as f64 * 0.015_625).to_bits() as i64 + step) as u64)
        }
        _ => unit(rng) * SPLIT,
    };
    let hi = hi.min(SPLIT);
    let lo = (unit(rng) - 0.5) * crate::ulp::ulp(hi);
    DoubleWord::sum(hi, if w & 1 == 0 { lo } else { 0.0 })
}

pub(super) fn write(out: &mut String) {
    let mut rng = SplitMix64::new(0x6173_696e_6366_0001);
    // The public entry: the specials, either sign, and the algorithm's domain.
    let mut entries: Vec<f64> = Vec::new();
    for x in [
        0.0_f64,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        ASIN_IS_X.next_down(),
        ASIN_IS_X,
        ASIN_IS_X.next_up(),
        0.5,
        SPLIT,
        SPLIT.next_up(),
        1.0 - f64::EPSILON / 2.0,
        1.0,
        1.0_f64.next_up(),
        2.0,
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
            "asin_entry {:016x} : {:016x}",
            x.to_bits(),
            crate::asin::asin(x).to_bits()
        )
        .unwrap();
    }
    for _ in 0..2000 {
        let x = argument(&mut rng);
        let (direct, zh, zl) = crate::asin::crosscheck_reduced(x);
        writeln!(
            out,
            "asin_reduced {:016x} : {} {:016x} {:016x}",
            x.to_bits(),
            u8::from(direct),
            zh.to_bits(),
            zl.to_bits()
        )
        .unwrap();
    }
    for _ in 0..4000 {
        let z = series_argument(&mut rng);
        let y = crate::asin::crosscheck_series(z);
        writeln!(
            out,
            "asin_series {:016x} {:016x} : {:016x} {:016x}",
            z.hi().to_bits(),
            z.lo().to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits()
        )
        .unwrap();
    }
    for _ in 0..6000 {
        let x = argument(&mut rng);
        let (y, start, decided) = crate::asin::crosscheck_fast(x);
        writeln!(
            out,
            "asin_fast {:016x} : {:016x} {:016x} {:016x} {:016x} {}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            start.hi().to_bits(),
            start.lo().to_bits(),
            opt(decided)
        )
        .unwrap();
    }
    for _ in 0..600 {
        let x = argument(&mut rng);
        let (direct, _, _) = crate::asin::crosscheck_reduced(x);
        let (_, start, _) = crate::asin::crosscheck_fast(x);
        writeln!(
            out,
            "asin_accurate {} {:016x} {:016x} {:016x} : {}",
            u8::from(direct),
            x.to_bits(),
            start.hi().to_bits(),
            start.lo().to_bits(),
            q256(crate::asin::crosscheck_accurate(x, start))
        )
        .unwrap();
    }
    // The accurate path's `sin` and `cos` series and the reciprocals it takes of
    // them, each on its own, since the Newton step's correction hides them.
    for _ in 0..300 {
        let x = argument(&mut rng);
        let (_, start, _) = crate::asin::crosscheck_fast(x);
        let (sin, cos) = crate::asin::crosscheck_sin_cos(start);
        writeln!(
            out,
            "asin_sincos {:016x} {:016x} : {} {}",
            start.hi().to_bits(),
            start.lo().to_bits(),
            q256(sin),
            q256(cos)
        )
        .unwrap();
        for q in [sin, cos] {
            writeln!(
                out,
                "asin_recip {} : {}",
                q256(q),
                q256(crate::asin::crosscheck_recip(q))
            )
            .unwrap();
        }
    }
}
