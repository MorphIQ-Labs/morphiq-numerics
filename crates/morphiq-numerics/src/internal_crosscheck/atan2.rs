//! Compare `atan2`'s public entry, fast path, rounding decision and accurate
//! path with their Coq transcription (`formal/atan2/Atan2Kernel.v`), extracted
//! and run by `scripts/check_formal.sh`, so a difference in an operation or its
//! order shows before rounding can hide it.
use super::{SplitMix64, q256, unit};
use std::fmt::Write as _;
use std::string::String;
use std::vec::Vec;

fn opt(v: Option<f64>) -> String {
    super::opt(v)
}

/// A positive finite magnitude: a significand at a scale spanning the normal
/// range, now and then a subnormal.
fn magnitude(rng: &mut SplitMix64) -> f64 {
    let w = rng.next_u64();
    match w % 16 {
        0 => f64::from_bits(1 + rng.next_u64() % ((1 << 52) - 1)),
        1 => f64::from_bits((1 + rng.next_u64() % 0x7fe) << 52 | rng.next_u64() >> 12),
        _ => {
            let e = ((w >> 8) % 120) as i32 - 60;
            (1.0 + unit(rng)) * f64::from_bits(((1023 + i64::from(e)) as u64) << 52)
        }
    }
}

/// A pair `(y, x)` at the algorithm's structure: ratios across the unit
/// interval with either argument the larger, next to the table's `k/64` and its
/// rounding midpoints, equal magnitudes, ratios near `2^-900`, and the
/// subnormal midpoints `(2m + 1)·2^-1074 / 2`.
fn pair(rng: &mut SplitMix64) -> (f64, f64) {
    let w = rng.next_u64();
    let scale = magnitude(rng);
    let t = match w % 8 {
        0 => unit(rng),
        1 => {
            let k = (w >> 8) % 65;
            let step = ((w >> 16) % 9) as i64 - 4;
            f64::from_bits(((k as f64 * 0.015_625).to_bits() as i64 + step) as u64)
        }
        2 => {
            let k = (w >> 8) % 64;
            let step = ((w >> 16) % 9) as i64 - 4;
            f64::from_bits((((k as f64 + 0.5) * 0.015_625).to_bits() as i64 + step) as u64)
        }
        3 => 1.0,
        4 => f64::from_bits(
            0x07b0_0000_0000_0000_u64
                .wrapping_add(rng.next_u64() % 9)
                .wrapping_sub(4),
        ),
        5 => (1.0 + unit(rng)) * f64::from_bits(((1023 - 1 - ((w >> 8) % 60) as i64) as u64) << 52),
        _ => 0.25 + 0.75 * unit(rng),
    };
    let t = if t.is_finite() && t > 0.0 && t <= 1.0 {
        t
    } else {
        0.5
    };
    let sy = if w & (1 << 40) == 0 { 1.0 } else { -1.0 };
    let sx = if w & (1 << 41) == 0 { 1.0 } else { -1.0 };
    let (a, b) = (t * scale, scale);
    let (a, b) = if w & (1 << 42) == 0 { (a, b) } else { (b, a) };
    let (a, b) = if a.is_normal() && b.is_normal() {
        (a, b)
    } else {
        (scale, scale)
    };
    (sy * a, sx * b)
}

pub(super) fn write(out: &mut String) {
    let mut rng = SplitMix64::new(0x6174_616e_3263_0001);
    // The public entry: every pair of special values, then the algorithm's domain
    // and the subnormal midpoints.
    let mut entries: Vec<(f64, f64)> = Vec::new();
    let specials = [
        0.0_f64,
        -0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        1.0,
        -1.0,
        f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
    ];
    for &y in &specials {
        for &x in &specials {
            entries.push((y, x));
        }
    }
    for j in [0_u64, 1, 2, 3, 100, (1 << 51), (1 << 52) - 1] {
        let y = f64::from_bits(2 * j + 1);
        entries.extend([(y, 2.0), (-y, 2.0), (y, -2.0)]);
    }
    for _ in 0..7000 {
        entries.push(pair(&mut rng));
    }
    for (y, x) in entries {
        writeln!(
            out,
            "atan2_entry {:016x} {:016x} : {:016x}",
            y.to_bits(),
            x.to_bits(),
            crate::atan2::atan2(y, x).to_bits()
        )
        .unwrap();
    }
    // The fast path and its decision at each form.
    for _ in 0..4000 {
        let (y, x) = pair(&mut rng);
        let (a, b) = (y.abs(), x.abs());
        let (n, d) = if a > b { (b, a) } else { (a, b) };
        if n / d < f64::from_bits(0x07b0_0000_0000_0000) {
            continue;
        }
        let form = (rng.next_u64() % 4) as usize;
        let (yy, phi, decided) = crate::atan2::crosscheck_fast(n, d, form);
        writeln!(
            out,
            "atan2_fast {:016x} {:016x} {form} : {:016x} {:016x} {:016x} {:016x} {}",
            n.to_bits(),
            d.to_bits(),
            yy.hi().to_bits(),
            yy.lo().to_bits(),
            phi.hi().to_bits(),
            phi.lo().to_bits(),
            opt(decided)
        )
        .unwrap();
    }
    // The accurate value from the fast `phi`, at each form.
    for _ in 0..600 {
        let (y, x) = pair(&mut rng);
        let (a, b) = (y.abs(), x.abs());
        let (n, d) = if a > b { (b, a) } else { (a, b) };
        if n / d < f64::from_bits(0x07b0_0000_0000_0000) {
            continue;
        }
        let form = (rng.next_u64() % 4) as usize;
        let (_, phi, _) = crate::atan2::crosscheck_fast(n, d, form);
        writeln!(
            out,
            "atan2_accurate {:016x} {:016x} {form} {:016x} {:016x} : {}",
            n.to_bits(),
            d.to_bits(),
            phi.hi().to_bits(),
            phi.lo().to_bits(),
            q256(crate::atan2::crosscheck_accurate(n, d, form, phi))
        )
        .unwrap();
    }
}
