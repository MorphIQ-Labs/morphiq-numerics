//! Writes the internal cross-check corpus: `Q128` and `Q256` operations, the
//! rounding tests (`ln::decide_with`, `exp::decide_scaled`), `exp`'s reduction
//! and its fast value (`exp::fast_at`) on reproducible inputs, with this crate's
//! results. `scripts/check_formal.sh` runs the proved transcriptions
//! (`formal/q`, `formal/binary64/RoundingTest.v`, `formal/exp/ExpReduction.v`
//! and `formal/exp/ExpFast.v`, extracted by
//! `formal/extraction/InternalCrosscheck.v`) on the same inputs and requires
//! identical results, which ties the proofs to this code.
//!
//! Ignored by default; run with the output path in `MORPHIQ_INTERNAL_CORPUS`:
//! `cargo test -p morphiq-numerics --lib internal_crosscheck -- --ignored`.
//!
//! A value is written `n e k l1 .. lk`: its sign (0 or 1), its exponent in
//! decimal, its limb count and its 64-bit limbs in hex, least significant
//! first. Each line is `op args : result`.

use crate::double_word::DoubleWord;
use crate::q128::Q128;
use crate::q256::Q256;
use crate::random::SplitMix64;
use std::fmt::Write as _;
use std::string::String;

fn q128(q: Q128) -> String {
    let (n, m, e) = q.parts();
    #[allow(clippy::cast_possible_truncation)] // the low limb
    let lo = m as u64;
    std::format!("{} {e} 2 {lo:016x} {:016x}", u8::from(n), (m >> 64) as u64)
}

fn q256(q: Q256) -> String {
    let (n, m, e) = q.parts();
    std::format!(
        "{} {e} 4 {:016x} {:016x} {:016x} {:016x}",
        u8::from(n),
        m[0],
        m[1],
        m[2],
        m[3]
    )
}

/// An exponent: mostly near the operands' scale, sometimes across binary64's
/// whole range and past it, for the conversions.
fn exponent(rng: &mut SplitMix64, width: i32) -> i32 {
    let span = if rng.next_u64().is_multiple_of(4) {
        2600
    } else {
        200
    };
    i32::try_from(rng.next_u64() % span).unwrap() - i32::try_from(span / 2).unwrap() - width
}

fn r128(rng: &mut SplitMix64) -> Q128 {
    let m = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    let m = match rng.next_u64() % 8 {
        0 => 0,
        1 => m >> (rng.next_u64() % 128),
        _ => m,
    };
    Q128::new(rng.next_u64() & 1 == 1, m, exponent(rng, 127))
}

fn r256(rng: &mut SplitMix64) -> Q256 {
    let mut m = [
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
    ];
    match rng.next_u64() % 8 {
        0 => m = [0; 4],
        1 => m[usize::try_from(rng.next_u64() % 4).unwrap()] = 0,
        2 => {
            m[1] = u64::MAX;
            m[2] = u64::MAX;
        }
        _ => {}
    }
    Q256::new(rng.next_u64() & 1 == 1, m, exponent(rng, 255))
}

/// The rounding tests' `EPS` constants, `ε₁·(1 + 2^−50)` for `ε₁` = `2^−69`
/// (`exp`), `2^−63` (`ln`), `2^−62` (`expm1`, `sin`, `cos`), `2^−60` (`tan`).
const EPS: [u64; 4] = [
    0x3ba0_0000_0000_0004,
    0x3c00_0000_0000_0004,
    0x3c10_0000_0000_0004,
    0x3c30_0000_0000_0004,
];

fn opt(v: Option<f64>) -> String {
    v.map_or_else(
        || String::from("none"),
        |v| std::format!("{:016x}", v.to_bits()),
    )
}

/// A double-word at the test's threshold: a leading word `hi`, and a trailing
/// word `g/2 − eps·|hi|·(1 + s)`, `|s| ≤ 1/2`, with either sign, so both
/// outcomes occur.
fn near_threshold(rng: &mut SplitMix64, hi: f64, eps: f64) -> DoubleWord {
    let magnitude = hi.abs();
    let g = if magnitude.to_bits() & ((1 << 52) - 1) == 0 {
        crate::ulp::ulp(magnitude) * 0.5
    } else {
        crate::ulp::ulp(magnitude)
    };
    let s = unit(rng) - 0.5;
    let lo = g * 0.5 - eps * magnitude * (1.0 + s);
    let lo = if rng.next_u64() & 1 == 1 { -lo } else { lo };
    DoubleWord::sum(hi, lo)
}

fn unit(rng: &mut SplitMix64) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
    u
}

/// An argument of `exp`'s reduction: anywhere in its domain, at a tie of
/// `x/L` (where `n` turns), or tiny (`n = 0`, and `r1 = x`).
fn reduction_argument(rng: &mut SplitMix64) -> f64 {
    /// `ln 2 / 128`, near enough to place a tie within `2^−40`.
    const L: f64 = core::f64::consts::LN_2 / 128.0;
    match rng.next_u64() % 3 {
        0 => -745.13 + 1454.91 * unit(rng),
        1 => {
            #[allow(clippy::cast_precision_loss)] // |n| < 2^18
            let n = (rng.next_u64() % 268_660) as f64 - 137_590.0;
            (n + 0.5) * L + (unit(rng) - 0.5) * f64::from_bits(0x3d70_0000_0000_0000)
        }
        _ => {
            let x = unit(rng) * f64::from_bits((1023 - rng.next_u64() % 61) << 52);
            if rng.next_u64() & 1 == 1 { -x } else { x }
        }
    }
}

#[test]
#[ignore = "writes the internal cross-check corpus for scripts/check_formal.sh"]
fn internal_crosscheck_corpus() {
    let path = std::env::var("MORPHIQ_INTERNAL_CORPUS").expect("MORPHIQ_INTERNAL_CORPUS");
    let mut rng = SplitMix64::new(0x7163_726f_7373_0001);
    let mut out = String::new();
    for i in 0..4000 {
        // decide_with: leading words across the proved range, both signs.
        let eps = f64::from_bits(EPS[usize::try_from(rng.next_u64() % 4).unwrap()]);
        let e = i32::try_from(rng.next_u64() % 1900).unwrap() - 900;
        // One in eight a power of two, where the gap below is halved.
        let m = if rng.next_u64().is_multiple_of(8) {
            1.0
        } else {
            1.0 + unit(&mut rng)
        };
        let hi = m * f64::from_bits(u64::try_from(1023 + e).unwrap() << 52);
        let hi = if rng.next_u64() & 1 == 1 { -hi } else { hi };
        let y = near_threshold(&mut rng, hi, eps);
        writeln!(
            out,
            "decide_with {:016x} {:016x} {:016x} : {}",
            y.hi().to_bits(),
            y.lo().to_bits(),
            eps.to_bits(),
            opt(crate::ln::decide_with(y, eps))
        )
        .unwrap();
        // decide_scaled: exp's EPS, a leading word in [3/4, 5/2), every scale.
        let eps = f64::from_bits(EPS[0]);
        let k = i32::try_from(rng.next_u64() % 2046).unwrap() - 1021;
        let hi = if rng.next_u64().is_multiple_of(8) {
            1.0
        } else {
            0.75 + 1.75 * unit(&mut rng)
        };
        let (hi, k) = if rng.next_u64().is_multiple_of(16) {
            (0.75 + 0.25 * unit(&mut rng), 1024)
        } else {
            (hi, k)
        };
        let y = near_threshold(&mut rng, hi, eps);
        writeln!(
            out,
            "decide_scaled {:016x} {:016x} {:016x} {k} : {}",
            y.hi().to_bits(),
            y.lo().to_bits(),
            eps.to_bits(),
            opt(crate::exp::decide_scaled(y, k))
        )
        .unwrap();

        let x = reduction_argument(&mut rng);
        let words = crate::exp::Reduced::of(x).words();
        writeln!(
            out,
            "reduce {:016x} : {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
            x.to_bits(),
            words[0].to_bits(),
            words[1].to_bits(),
            words[2].to_bits(),
            words[3].to_bits(),
            words[4].to_bits(),
            words[5].to_bits()
        )
        .unwrap();
        // fast_at at that reduced argument, cycling through every table index.
        let r = DoubleWord::from_parts(words[4], words[5]).unwrap();
        let j = i % 128;
        let y = crate::exp::fast_at(r, j);
        writeln!(
            out,
            "fast {:016x} {:016x} {j} : {:016x} {:016x}",
            words[4].to_bits(),
            words[5].to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits()
        )
        .unwrap();

        let (a, b) = (r128(&mut rng), r128(&mut rng));
        // Cancellation: b near −a.
        let b = if rng.next_u64().is_multiple_of(4) {
            a.neg().add(b.mul_pow2(-100))
        } else {
            b
        };
        writeln!(out, "q128_mul {} {} : {}", q128(a), q128(b), q128(a.mul(b))).unwrap();
        writeln!(out, "q128_add {} {} : {}", q128(a), q128(b), q128(a.add(b))).unwrap();
        writeln!(
            out,
            "q128_to_f64 {} : {:016x}",
            q128(a),
            a.to_f64().to_bits()
        )
        .unwrap();
        let bits = rng.next_u64();
        writeln!(
            out,
            "q128_from_f64 {bits:016x} : {}",
            q128(Q128::from_f64(f64::from_bits(bits)))
        )
        .unwrap();

        let (c, d) = (r256(&mut rng), r256(&mut rng));
        let d = if rng.next_u64().is_multiple_of(4) {
            c.neg()
                .add(d.mul(Q256::from_f64(f64::from_bits(0x3cb0_0000_0000_0000))))
        } else {
            d
        };
        writeln!(out, "q256_mul {} {} : {}", q256(c), q256(d), q256(c.mul(d))).unwrap();
        writeln!(out, "q256_add {} {} : {}", q256(c), q256(d), q256(c.add(d))).unwrap();
        writeln!(
            out,
            "q256_to_f64 {} : {:016x}",
            q256(c),
            c.to_f64().to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "q256_from_f64 {bits:016x} : {}",
            q256(Q256::from_f64(f64::from_bits(bits)))
        )
        .unwrap();
        let k = usize::try_from(rng.next_u64() % 12).unwrap();
        let limbs: std::vec::Vec<u64> = (0..k)
            .map(|_| {
                if rng.next_u64().is_multiple_of(5) {
                    0
                } else {
                    rng.next_u64() >> (rng.next_u64() % 64)
                }
            })
            .collect();
        let neg = rng.next_u64() & 1 == 1;
        let e = exponent(&mut rng, 0);
        let hex: std::vec::Vec<String> = limbs.iter().map(|l| std::format!("{l:016x}")).collect();
        writeln!(
            out,
            "q256_from_limbs {} {e} {k} {} : {}",
            u8::from(neg),
            hex.join(" "),
            q256(Q256::from_limbs(neg, &limbs, e))
        )
        .unwrap();
    }
    std::fs::write(path, out).unwrap();
}
