//! Writes the internal cross-check corpus: `Q128` and `Q256` operations, the
//! rounding tests (`ln::decide_with`, `exp::decide_scaled`), `exp`'s stages
//! (`Stages::of`, `a_value`, `a`, `b_value`, `b`), the fallback's reduction,
//! fast value (`exp::fast_at`), accurate path (`Reduced::accurate_value`) and
//! small-argument path (`exp::small_parts`, `exp::small`), and `ln`'s
//! `asin`'s reduction, series, fast path, accurate path and entry
//! (`asin::crosscheck_*`), and `ln`'s
//! reduction (`ln::Reduced::of`, `z`, `z_exact`), the accurate values of `ln`
//! and `ln_1p` (`Reduced::accurate_value`, `z_prime`, `ln::split`,
//! `ln::small_accurate`) and `ln_1p`'s screens and stages H and B
//! (`ln::stages::stage_h_screen`, `stage_b_screen`, `stage_h_parts`,
//! `stage_b_parts`), and `exp2`'s fallback reduction and accurate value
//! on reproducible inputs, with
//! this crate's results, and the bivariate normal's scalar kernel (`bivariate.rs`:
//! `bivariate_norm_cdf` and the table `BivariateNormal::new` builds, with the library
//! calls each makes, for `formal/bivariate/BvnKernel.v`). `scripts/check_formal.sh` runs the proved
//! transcriptions (`formal/q`, `formal/binary64/RoundingTest.v`,
//! `formal/exp/ExpStageReduction.v`, `ExpStageA.v`, `ExpStageB.v`,
//! `ExpReduction.v`, `ExpFast.v`, `ExpAccurate.v`, `ExpSmall.v`,
//! `formal/ln/LnReduction.v`, `LnAccurate.v`, `Ln1pScreen.v`, `Ln1pStageH.v`
//! and `Ln1pStageB.v`, `formal/exp/Exp2FallbackReduction.v` and
//! `Exp2FallbackAccurate.v`, `Exp2FallbackFast.v` and `Exp2.v`, extracted by
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

mod asin;
mod asinh;
mod atan2;
mod bivariate;
mod normal;

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
pub(crate) fn reduction_argument(rng: &mut SplitMix64) -> f64 {
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

/// An argument of `exp`'s stages, `|x| < 704`: anywhere in that range, at a
/// tie of `x/L` (`L = ln 2 / 512`, where `n` turns), or tiny (`n = 0`).
fn stage_argument(rng: &mut SplitMix64) -> f64 {
    const L: f64 = core::f64::consts::LN_2 / 512.0;
    match rng.next_u64() % 3 {
        0 => 1407.99 * unit(rng) - 703.995,
        1 => {
            #[allow(clippy::cast_precision_loss)] // |n| < 2^20
            let n = (rng.next_u64() % 1_040_000) as f64 - 520_000.0;
            (n + 0.5) * L + (unit(rng) - 0.5) * f64::from_bits(0x3d60_0000_0000_0000)
        }
        _ => {
            let x = unit(rng) * f64::from_bits((1023 - rng.next_u64() % 61) << 52);
            if rng.next_u64() & 1 == 1 { -x } else { x }
        }
    }
}

/// `exp`'s stages at `x`: `Stages::of`'s words, both stages' values and
/// their tests' outcomes.
fn stage_line(out: &mut String, x: f64) {
    let stages = crate::exp::Stages::of(x);
    let [n, r1] = stages.words();
    let (j, k) = stages.jk();
    let (ya, la) = stages.a_value();
    let (yb, lb) = stages.b_value();
    writeln!(
        out,
        "stage {:016x} : {:016x} {:016x} {j} {k} {:016x} {:016x} {} {:016x} {:016x} {}",
        x.to_bits(),
        n.to_bits(),
        r1.to_bits(),
        ya.to_bits(),
        la.to_bits(),
        opt(stages.a()),
        yb.to_bits(),
        lb.to_bits(),
        opt(stages.b())
    )
    .unwrap();
}

/// An argument of `ln`'s reduction: any positive finite encoding, a
/// subnormal, near 1 (`R[i] = 1`), or at a table interval's edge.
fn ln_argument(rng: &mut SplitMix64) -> f64 {
    match rng.next_u64() % 4 {
        0 => f64::from_bits(1 + rng.next_u64() % 0x7fef_ffff_ffff_ffff),
        1 => f64::from_bits(1 + rng.next_u64() % ((1 << 52) - 1)),
        2 => 1.0 + (unit(rng) - 0.5) * f64::from_bits(0x3f90_0000_0000_0000),
        _ => {
            // 1 + i/128, or the number below it, scaled.
            let edge = 1.0
                + f64::from_bits(0x3f80_0000_0000_0000)
                    * f64::from(u32::try_from(rng.next_u64() % 128).unwrap());
            let edge = if rng.next_u64() & 1 == 1 {
                f64::from_bits(edge.to_bits() - 1)
            } else {
                edge
            };
            let e = i32::try_from(rng.next_u64() % 2000).unwrap() - 1000;
            edge * f64::from_bits(u64::try_from(1023 + e).unwrap() << 52)
        }
    }
}

/// An argument of `ln_1p`'s accurate path, `|x| ≥ 2^−54` and `x > −1`:
/// either branch (`|x| < 2^−7` and not), log-uniform in magnitude, both signs,
/// near −1 and around `2^53`, where `1 + x` splits as `(x, 1)`.
fn ln_1p_argument(rng: &mut SplitMix64) -> f64 {
    let magnitude = |rng: &mut SplitMix64, lo: u64, width: u64| {
        (1.0 + unit(rng)) * f64::from_bits((lo + rng.next_u64() % width) << 52)
    };
    match rng.next_u64() % 5 {
        // 2^−54 <= |x| < 2^−7, both signs.
        0 => {
            let x = magnitude(rng, 1023 - 54, 47);
            if rng.next_u64() & 1 == 1 { -x } else { x }
        }
        // 2^−7 <= x < 2^60.
        1 => magnitude(rng, 1023 - 7, 67),
        // −1 < x <= −2^−7.
        2 => -(1.0 - unit(rng) * (1.0 - f64::from_bits(0x3f80_0000_0000_0000))),
        // Near −1.
        3 => -1.0 + magnitude(rng, 1023 - 53, 40),
        // Around 2^53.
        _ => f64::from_bits(0x4340_0000_0000_0000 - 64 + rng.next_u64() % 128),
    }
}

#[test]
#[ignore = "writes the internal cross-check corpus for scripts/check_formal.sh"]
fn internal_crosscheck_corpus() {
    let path = std::env::var("MORPHIQ_INTERNAL_CORPUS").expect("MORPHIQ_INTERNAL_CORPUS");
    let mut rng = SplitMix64::new(0x7163_726f_7373_0001);
    let mut out = String::new();
    normal::write(&mut out);
    fast_corpus(&mut out);
    asin::write(&mut out);
    asinh::write(&mut out);
    atan2::write(&mut out);
    bivariate::write(&mut out);
    q256_exponent_corpus(&mut out);
    erfcx_accurate_tail_corpus(&mut out);
    erfcx_accurate_exponential_corpus(&mut out);
    erfcx_accurate_taylor_corpus(&mut out);
    erfcx_accurate_negative_corpus(&mut out);
    erfcx_public_entry_corpus(&mut out);
    // Cover the corrected reciprocal's full exponent range, including each
    // power-of-two boundary and its adjacent binary64 values.
    let mut erfcx_rng = SplitMix64::new(0x6572_6663_785f_0001);
    // The exact square and normalized exponential used by negative reflection.
    // Include the overflow-adjacent input, the -1/2 boundary, and direct
    // reductions beyond exp's usual 704 screen through the 710 proof limit.
    for i in 0..24_000 {
        let low = 0xbfe0_0000_0000_0001_u64;
        let high = crate::erfcx::X_OVF.to_bits() - 1;
        let bits = match i % 8 {
            0 => low + (i / 8) % 32,
            1 => high - (i / 8) % 32,
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        let x = f64::from_bits(bits);
        let (square, error) = crate::eft::two_prod(x, x);
        writeln!(
            out,
            "erfcx_reflection_square {bits:016x} : {:016x} {:016x}",
            square.to_bits(),
            error.to_bits()
        )
        .unwrap();
        let (nh, nl, nk) = crate::erfcx::n_eval(x);
        writeln!(
            out,
            "erfcx_reflection_value {bits:016x} : {nk} {:016x} {:016x}",
            nh.to_bits(),
            nl.to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "erfcx_reflection_fast {bits:016x} : {}",
            opt(crate::erfcx::fast_n(x))
        )
        .unwrap();
        let (s, se) = if i % 2 == 0 {
            (square, error)
        } else {
            let lower = 704.0_f64.to_bits();
            let upper = 710.0_f64.to_bits() - 1;
            let sb = match i % 6 {
                1 => lower + (i / 6) % 32,
                3 => upper - (i / 6) % 32,
                _ => lower + erfcx_rng.next_u64() % (upper - lower + 1),
            };
            let eb = match (i / 2) % 6 {
                0 => 0,
                1 => 1,
                2 => (1023 - 44) << 52,
                _ => erfcx_rng.next_u64() % (((1023 - 44) << 52) + 1),
            } | ((erfcx_rng.next_u64() & 1) << 63);
            (f64::from_bits(sb), f64::from_bits(eb))
        };
        let (h, l, k) = crate::erfcx::exp_dw(s, se);
        writeln!(
            out,
            "erfcx_reflection_exp {:016x} {:016x} : {k} {:016x} {:016x}",
            s.to_bits(),
            se.to_bits(),
            h.to_bits(),
            l.to_bits()
        )
        .unwrap();
    }
    for i in 0..24_000 {
        let middle = i % 2 == 0;
        let (low, high) = if middle {
            (16.0_f64.to_bits(), 512.0_f64.to_bits() - 1)
        } else {
            (512.0_f64.to_bits(), 1e270_f64.to_bits())
        };
        let bits = match (i / 2) % 4 {
            0 => low + (i / 8) % 32,
            1 => high - (i / 8) % 32,
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        let x = f64::from_bits(bits);
        let (name, result) = if middle {
            ("erfcx_middle_fast", crate::erfcx::fast_ya(x))
        } else {
            ("erfcx_tail_unscaled_fast", crate::erfcx::fast_yb(x))
        };
        writeln!(out, "{name} {bits:016x} : {}", opt(result)).unwrap();
    }
    for i in 0..24_000_u64 {
        let low = crate::erfcx::X_SUB.to_bits();
        let high = f64::MAX.to_bits();
        let bits = match i % 4 {
            0 => low + (i / 4) % 64,
            1 => high - (i / 4) % 64,
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        writeln!(
            out,
            "erfcx_tail_subnormal_fast {bits:016x} : {}",
            opt(crate::erfcx::fast_yb(f64::from_bits(bits)))
        )
        .unwrap();
    }
    for i in 0..24_000_u64 {
        let low = 1e270_f64.to_bits() + 1;
        let boundary = crate::erfcx::X_SUB.to_bits();
        let high = f64::MAX.to_bits();
        let bits = match i % 6 {
            0 => low + (i / 6) % 64,
            1 => boundary - 1 - (i / 6) % 64,
            2 => boundary + (i / 6) % 64,
            3 => high - (i / 6) % 64,
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        writeln!(
            out,
            "erfcx_tail_scaled_fast {bits:016x} : {}",
            opt(crate::erfcx::fast_yb(f64::from_bits(bits)))
        )
        .unwrap();
    }
    for bits in (4_u64..=9)
        .flat_map(|e| {
            let b = (1023 + e) << 52;
            [b - 1, b, b + 1]
        })
        .chain((0..4000).map(|_| {
            let e = 1027 + erfcx_rng.next_u64() % 5;
            (e << 52) | (erfcx_rng.next_u64() & ((1_u64 << 52) - 1))
        }))
    {
        let x = f64::from_bits(bits);
        if (16.0..=512.0).contains(&x) {
            let (_, _, th, tl) = crate::erfcx::reciprocal_square(x);
            writeln!(
                out,
                "erfcx_reciprocal_square {bits:016x} : {:016x} {:016x}",
                th.to_bits(),
                tl.to_bits()
            )
            .unwrap();
            let (w, wl) = crate::erfcx::middle_correction(th, tl);
            writeln!(
                out,
                "erfcx_reciprocal_correction {bits:016x} : {:016x} {:016x}",
                w.to_bits(),
                wl.to_bits()
            )
            .unwrap();
            let (zh, zl) = crate::erfcx::ya_eval(x);
            writeln!(
                out,
                "erfcx_middle {bits:016x} : {:016x} {:016x}",
                zh.to_bits(),
                zl.to_bits()
            )
            .unwrap();
            let (h, l) = crate::erfcx::reciprocal(x);
            writeln!(
                out,
                "erfcx_reciprocal {bits:016x} : {:016x} {:016x}",
                h.to_bits(),
                l.to_bits()
            )
            .unwrap();
        }
    }
    for i in 0..8000 {
        let mut operand = |salt: u64| {
            let e = 1013 + erfcx_rng.next_u64() % 11;
            let h = f64::from_bits((e << 52) | (erfcx_rng.next_u64() & ((1_u64 << 52) - 1)));
            let l = match (i + salt) % 8 {
                0 => 0.0,
                1 => f64::from_bits(1),
                2 => f64::from_bits((1_u64 << 52) - 1),
                3 => f64::from_bits(1_u64 << 52),
                4 => f64::from_bits(23_u64 << 52),
                5 => f64::from_bits(523_u64 << 52),
                _ => h * f64::from_bits(969_u64 << 52) * unit(&mut erfcx_rng),
            };
            (h, if erfcx_rng.next_u64() & 1 == 0 { l } else { -l })
        };
        let (ah, al) = operand(0);
        let (bh, bl) = operand(3);
        let (h, l) = crate::erfcx::dw_mul(ah, al, bh, bl);
        writeln!(
            out,
            "erfcx_product {:016x} {:016x} {:016x} {:016x} : {:016x} {:016x}",
            ah.to_bits(),
            al.to_bits(),
            bh.to_bits(),
            bl.to_bits(),
            h.to_bits(),
            l.to_bits()
        )
        .unwrap();
    }
    for i in 0..12000 {
        let e = 1032 + erfcx_rng.next_u64() % 888;
        let bits = (e << 52) | (erfcx_rng.next_u64() & ((1_u64 << 52) - 1));
        let bits = match i {
            0 => 1032_u64 << 52,
            1 => 1920_u64 << 52,
            _ => bits,
        };
        let (h, l) = crate::erfcx::quotient(f64::from_bits(bits));
        writeln!(
            out,
            "erfcx_quotient {bits:016x} : {:016x} {:016x}",
            h.to_bits(),
            l.to_bits()
        )
        .unwrap();
        let low = 1e270_f64.to_bits() + 1;
        let high = f64::MAX.to_bits();
        let bits = match i {
            0 => low,
            1 => high,
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        let (h, l, _) = crate::erfcx::yb_eval(f64::from_bits(bits));
        writeln!(
            out,
            "erfcx_scaled_quotient {bits:016x} : {:016x} {:016x}",
            h.to_bits(),
            l.to_bits()
        )
        .unwrap();
    }
    for i in 0_usize..12000 {
        let e = (i % 4) as i32;
        let hm = f64::from_bits(((1017 + e) as u64) << 52);
        let grid = f64::from_bits(((1000 + e) as u64) << 52);
        let k = erfcx_rng.next_u64() % 131072;
        let midpoint = (k as f64 + 0.5) * grid;
        let h = match i / 4 {
            0 => 0.0,
            1 => -0.0,
            2 => f64::from_bits(1),
            3 => -f64::from_bits(1),
            4 => hm,
            5 => -hm,
            _ => {
                let bits = match i % 5 {
                    0 => midpoint.to_bits() - 1,
                    1 => midpoint.to_bits(),
                    2 => midpoint.to_bits() + 1,
                    _ => erfcx_rng.next_u64() % (hm.to_bits() + 1),
                };
                f64::from_bits(bits | ((erfcx_rng.next_u64() & 1) << 63))
            }
        };
        let (hi, lo) = crate::erfcx::table_split(h, e);
        writeln!(
            out,
            "erfcx_table_split {:016x} {e} : {:016x} {:016x} {:016x}",
            h.to_bits(),
            hi.to_bits(),
            lo.to_bits(),
            (hi * hi).to_bits()
        )
        .unwrap();
    }
    // Actual table reduction: all uniform ties and binade boundaries,
    // adjacent encodings, signed zero and both signs of subnormal input.
    for sample in 0_u64..24000 {
        let x = if sample < 12000 {
            match sample {
                0 => -0.5,
                1 => f64::from_bits(1.0_f64.to_bits() - 1),
                2 => 0.0,
                3 => -0.0,
                4 => f64::from_bits(1),
                5 => -f64::from_bits(1),
                6..=149 => {
                    let k = ((sample - 6) / 3) as i32 - 16;
                    let tie = (k as f64 + 0.5) / 32.0;
                    let bits = match (sample - 6) % 3 {
                        0 => tie.to_bits() - 1,
                        1 => tie.to_bits(),
                        _ => tie.to_bits() + 1,
                    };
                    f64::from_bits(bits)
                }
                _ => {
                    let negative = erfcx_rng.next_u64() & 1 != 0;
                    let limit = if negative {
                        0.5_f64.to_bits() + 1
                    } else {
                        1.0_f64.to_bits()
                    };
                    let bits = erfcx_rng.next_u64() % limit;
                    f64::from_bits(bits | if negative { 1_u64 << 63 } else { 0 })
                }
            }
        } else {
            let j = sample - 12000;
            let low = 1.0_f64.to_bits();
            let high = 16.0_f64.to_bits() - 1;
            let bits = match j {
                0..=767 => {
                    let boundary = low + ((j / 3) << 46);
                    match j % 3 {
                        0 => boundary.saturating_sub(1).max(low),
                        1 => boundary,
                        _ => boundary + 1,
                    }
                }
                768 => high,
                _ => low + erfcx_rng.next_u64() % (high - low + 1),
            };
            f64::from_bits(bits)
        };
        let (idx, c, h, e) = crate::erfcx::t_reduce(x);
        writeln!(
            out,
            "erfcx_table_reduce {:016x} : {idx} {e} {:016x} {:016x}",
            x.to_bits(),
            c.to_bits(),
            h.to_bits()
        )
        .unwrap();
        let (yh, yl) = crate::erfcx::t_eval(x);
        writeln!(
            out,
            "erfcx_table_value {:016x} : {:016x} {:016x}",
            x.to_bits(),
            yh.to_bits(),
            yl.to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "erfcx_table_fast {:016x} : {}",
            x.to_bits(),
            opt(crate::erfcx::fast_t(x))
        )
        .unwrap();
    }
    for idx in 0_usize..177 {
        let e = if idx < 49 {
            0
        } else {
            ((idx - 49) / 32) as i32
        };
        let hm = f64::from_bits(((1017 + e) as u64) << 52);
        for sample in 0..32 {
            let h = match sample {
                0 => 0.0,
                1 => hm,
                2 => -hm,
                _ => hm * (2.0 * unit(&mut erfcx_rng) - 1.0),
            };
            let (h, _) = crate::erfcx::table_split(h, e);
            let (a1, b1, a2h, b2, p1, sq, p2) = crate::erfcx::table_leading(idx, h);
            writeln!(out, "erfcx_table_leading {idx} {:016x} : {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
                h.to_bits(), a1.to_bits(), b1.to_bits(), a2h.to_bits(), b2.to_bits(), p1.to_bits(), sq.to_bits(), p2.to_bits()).unwrap();
        }
    }
    // Tail correction and reconstruction through square/product underflow.
    // Include both neighbours of exponent boundaries and the dispatch endpoint.
    for i in 0..12000 {
        let low = 512_f64.to_bits();
        let high = 1e270_f64.to_bits();
        let bits = match i {
            0 => low,
            1 => high,
            2..=13 => {
                let exponent = [511_u64, 512, 537, 538][(i - 2) / 3];
                ((1023 + exponent) << 52) - 1 + ((i - 2) % 3) as u64
            }
            _ => low + erfcx_rng.next_u64() % (high - low + 1),
        };
        let x = f64::from_bits(bits);
        let u = crate::erfcx::tail_correction(x);
        writeln!(
            out,
            "erfcx_tail_correction {bits:016x} : {:016x}",
            u.to_bits()
        )
        .unwrap();
        let (h, l, _) = crate::erfcx::yb_eval(x);
        writeln!(
            out,
            "erfcx_tail {bits:016x} : {:016x} {:016x}",
            h.to_bits(),
            l.to_bits()
        )
        .unwrap();
    }
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

        stage_line(&mut out, stage_argument(&mut rng));

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
        // The accurate path's 128-bit value at the same argument.
        let reduced = crate::exp::Reduced::of(x);
        let (j, k) = reduced.jk();
        writeln!(
            out,
            "accurate {:016x} {j} {k} : {}",
            x.to_bits(),
            q128(reduced.accurate_value())
        )
        .unwrap();
        // The small-argument path, 2^−54 ≤ |x| < 2^−30: h, w and the result.
        let e = rng.next_u64() % 24;
        let x = (1.0 + unit(&mut rng)) * f64::from_bits((1023 - 54 + e) << 52);
        let x = if rng.next_u64() & 1 == 1 { -x } else { x };
        let (h, w) = crate::exp::small_parts(x);
        writeln!(
            out,
            "small {:016x} : {:016x} {} {:016x}",
            x.to_bits(),
            h.to_bits(),
            q128(w),
            crate::exp::small(x).to_bits()
        )
        .unwrap();
        // ln's reduction: E, i, y, R[i], the double-word z and z in Q128.
        let x = ln_argument(&mut rng);
        let reduced = crate::ln::Reduced::of(x);
        let (i, y, r) = reduced.parts();
        let z = reduced.z();
        writeln!(
            out,
            "ln_reduce {:016x} : {} {i} {:016x} {:016x} {:016x} {:016x} {}",
            x.to_bits(),
            reduced.e,
            y.to_bits(),
            r.to_bits(),
            z.hi().to_bits(),
            z.lo().to_bits(),
            q128(reduced.z_exact())
        )
        .unwrap();
        // ln's accurate value at the same argument (x = 1 never reaches it).
        if x != 1.0 {
            writeln!(
                out,
                "ln_accurate {:016x} : {}",
                x.to_bits(),
                q128(reduced.accurate_value(reduced.z_exact()))
            )
            .unwrap();
        }
        // ln_1p's accurate value, on both branches, as ln_1p computes it.
        let x = ln_1p_argument(&mut rng);
        let value = if x.abs() < f64::from_bits(0x3f80_0000_0000_0000) {
            crate::ln::small_accurate(x)
        } else {
            let (h, l) = crate::ln::split(x);
            let reduced = crate::ln::Reduced::of(h);
            reduced.accurate_value(reduced.z_prime(l))
        };
        writeln!(out, "ln_1p_accurate {:016x} : {}", x.to_bits(), q128(value)).unwrap();

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
    // Arguments stage B's test leaves undecided, so both of its outcomes
    // occur: searched for from a fixed seed (about one in 2^16.7).
    let mut found = 0;
    while found < 8 {
        let x = 1407.99 * unit(&mut rng) - 703.995;
        if crate::exp::Stages::of(x).b().is_none() {
            stage_line(&mut out, x);
            found += 1;
        }
    }
    // ln_1p's stages: both screens at every argument, and (s, lo, eps) and
    // the test's result for arguments each stage's screen admits, across its
    // branches.
    let mut rng = SplitMix64::new(0x7163_726f_7373_0002);
    let (mut h, mut b) = (0, 0);
    while h < 4000 || b < 4000 {
        let x = ln_1p_stage_argument(&mut rng);
        writeln!(
            out,
            "ln1p_screens {:016x} : {} {}",
            x.to_bits(),
            u8::from(crate::ln::stages::stage_h_screen(x)),
            u8::from(crate::ln::stages::stage_b_screen(x))
        )
        .unwrap();
        if h < 4000 && crate::ln::stages::stage_h_screen(x) {
            ln_1p_stage_line(&mut out, "ln1p_h", x, crate::ln::stages::stage_h_parts(x));
            h += 1;
        }
        if b < 4000 && crate::ln::stages::stage_b_screen(x) {
            ln_1p_stage_line(&mut out, "ln1p_b", x, crate::ln::stages::stage_b_parts(x));
            b += 1;
        }
    }
    // Full exp2/expm1 stage transcriptions: admitted inputs, cancellation,
    // arbitrary encodings and screen boundaries (including NaNs/infinities).
    let mut rng = SplitMix64::new(0x7163_726f_7373_0003);
    let mut stage_case = |x: f64| {
        for (op, v) in [
            ("exp2_stages", crate::exp2::stages::stages(x)),
            ("expm1_stages", crate::expm1::stages::stages(x)),
        ] {
            writeln!(out, "{op} {:016x} : {}", x.to_bits(), opt(v)).unwrap();
        }
    };
    for _ in 0..2000 {
        stage_case(-1016.0 + 2032.0 * unit(&mut rng));
        stage_case(-37.0 + 741.0 * unit(&mut rng));
        stage_case(-1.0 + 2.0 * unit(&mut rng));
        stage_case(f64::from_bits(rng.next_u64()));
    }
    for edge in [
        -1016.0_f64,
        -37.0,
        -0.03125,
        0.03125,
        704.0,
        1016.0,
        f64::from_bits((1023 - 55) << 52),
        -f64::from_bits((1023 - 55) << 52),
    ] {
        for x in [edge.next_down(), edge, edge.next_up()] {
            stage_case(x);
        }
    }
    // The exp2 fallback independently computes j/k, the residual and Q128
    // value. Cover all table indices, both tie parities, signs, binade and
    // entry-screen boundaries, plus finite inputs outside the proved domain.
    let mut fallback_case = |x: f64| {
        let (j, k, d, q) = crate::exp2::crosscheck_fallback(x);
        exp2_entry_line(&mut out, x);
        if x > -1075.0 && x < 1024.0 {
            exp2_fast_line(&mut out, x);
        }
        writeln!(
            out,
            "exp2_fallback {:016x} : {j} {k} {:016x} {}",
            x.to_bits(),
            d.to_bits(),
            q128(q)
        )
        .unwrap();
    };
    for n in -256..=256 {
        for x in [f64::from(n) / 128.0, (f64::from(n) + 0.5) / 128.0] {
            for x in [x.next_down(), x, x.next_up()] {
                fallback_case(x);
            }
        }
    }
    for edge in [
        -2000.0_f64,
        -1075.0,
        -1021.0,
        -1.0,
        -0.0,
        0.0,
        1.0,
        1024.0,
        1075.0,
        2000.0,
        f64::from_bits((1023 - 55) << 52),
        -f64::from_bits((1023 - 55) << 52),
        f64::from_bits(0xbc97_1547_652b_82fe),
        f64::from_bits(0x3ca7_1547_652b_82fe),
    ] {
        for x in [edge.next_down(), edge, edge.next_up()] {
            fallback_case(x);
        }
    }
    for _ in 0..4000 {
        fallback_case(-1075.0 + 2099.0 * unit(&mut rng));
    }
    // Whole entry: independent fixture inputs (including worst cases),
    // arbitrary encodings (NaN payloads included), and small values spanning
    // both ends of the interval that rounds to one.
    // Read the generated flat x fields from both precise values and cases.
    // Case descriptions can contain brackets, unlike the precise-only arrays
    // accepted by test_exact::entries.
    for case in include_str!("../../reference/fixtures/exp2.json")
        .lines()
        .filter(|line| line.trim_start().starts_with("\"x\":"))
    {
        exp2_entry_line(&mut out, crate::test_exact::word(case, "x"));
    }
    for _ in 0..4000 {
        exp2_entry_line(&mut out, f64::from_bits(rng.next_u64()));
        let x = (unit(&mut rng) - 0.5) * f64::from_bits((1023 - 50) << 52);
        exp2_entry_line(&mut out, x);
    }
    for bits in [
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0xfff0_0000_0000_0001,
        0x7ff8_0000_0000_0042,
        0xfff8_0000_0000_0042,
    ] {
        exp2_entry_line(&mut out, f64::from_bits(bits));
    }
    // Exercise rejection of the fallback's interval test with normal scaling,
    // independently of whether the newer stages would accept the input.
    let mut rejected = 0;
    for _ in 0..(1 << 22) {
        let x = -1016.0 + 2032.0 * unit(&mut rng);
        if crate::exp2::crosscheck_fast(x).1.is_none() {
            exp2_fast_line(&mut out, x);
            exp2_entry_line(&mut out, x);
            rejected += 1;
            if rejected == 8 {
                break;
            }
        }
    }
    assert_eq!(rejected, 8, "fallback rejection coverage");
    // Every small-path operation, including both outcomes of its Ziv test.
    let mut rng = SplitMix64::new(0x7163_726f_7373_0006);
    let (mut accepted, mut rejected) = (0, 0);
    let mut small_case = |x: f64| {
        let (y, decision, q) = crate::expm1::crosscheck_small(x);
        if decision.is_some() {
            accepted += 1;
        } else {
            rejected += 1;
        }
        writeln!(
            out,
            "expm1_small {:016x} : {:016x} {:016x} {} {} {:016x}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            opt(decision),
            q128(q),
            q.to_f64().to_bits(),
        )
        .unwrap();
    };
    for exponent in 969..=1018 {
        let edge = exponent << 52;
        for offset in 0..=8 {
            for bits in [edge - offset, edge + offset] {
                let x = f64::from_bits(bits);
                small_case(x);
                small_case(-x);
            }
        }
    }
    for _ in 0..8000 {
        small_case((unit(&mut rng) - 0.5) / 16.0);
    }
    for x in [-0.0, 0.0] {
        small_case(x);
    }
    for case in include_str!("../../reference/fixtures/expm1.json")
        .lines()
        .filter(|line| line.trim_start().starts_with("\"x\":"))
    {
        let x = crate::test_exact::word(case, "x");
        if x.abs() >= f64::from_bits(0x3c80_0000_0000_0000) && x.abs() <= 0.0312501 {
            small_case(x);
        }
    }
    assert!(
        accepted > 0 && rejected >= 8,
        "both expm1 small-path decisions"
    );
    // Whole public entry: special values, every screen boundary, fixtures,
    // and arbitrary encodings across the normal and subnormal ranges.
    for case in include_str!("../../reference/fixtures/expm1.json")
        .lines()
        .filter(|line| line.trim_start().starts_with("\"x\":"))
    {
        expm1_entry_line(&mut out, crate::test_exact::word(case, "x"));
    }
    for edge in [
        0x3c90_0000_0000_0000,
        0x3fa0_0000_0000_0000,
        0xc042_b708_8723_20e2,
        0x4086_2e42_fefa_39f0,
    ] {
        for offset in 0..=32 {
            for bits in [edge - offset, edge + offset] {
                expm1_entry_line(&mut out, f64::from_bits(bits));
                expm1_entry_line(&mut out, -f64::from_bits(bits));
            }
        }
    }
    for bits in [
        0,
        1,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0xfff0_0000_0000_0001,
        0x7ff8_0000_0000_0042,
        0xfff8_0000_0000_0042,
    ] {
        expm1_entry_line(&mut out, f64::from_bits(bits));
    }
    for _ in 0..4000 {
        expm1_entry_line(&mut out, f64::from_bits(rng.next_u64()));
        expm1_entry_line(&mut out, (unit(&mut rng) - 0.5) / 16.0);
    }
    // expm1's general fallback: compute the reduction metadata, both scaled
    // words, decision, Q128 subtraction and final conversion from x alone.
    let mut rng = SplitMix64::new(0x7163_726f_7373_0005);
    let mut seen = [false; 128];
    let (mut accepted, mut rejected) = (0, 0);
    let (mut least_k, mut greatest_k) = (i32::MAX, i32::MIN);
    let mut general_case = |x: f64| {
        if x < -38.0 || x >= f64::from_bits(0x4086_2e42_fefa_39f0) || !x.is_finite() {
            return;
        }
        let (j, k, y, decision, q) = crate::expm1::crosscheck_general(x);
        seen[j] = true;
        if x >= -37.43 && x.abs() >= 0.03125 {
            least_k = least_k.min(k);
            greatest_k = greatest_k.max(k);
        }
        if decision.is_some() {
            accepted += 1;
        } else {
            rejected += 1;
        }
        writeln!(
            out,
            "expm1_general {:016x} : {j} {k} {:016x} {:016x} {} {} {:016x}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            opt(decision),
            q128(q),
            q.to_f64().to_bits(),
        )
        .unwrap();
    };
    for _ in 0..8000 {
        general_case(-37.42 + 747.2 * unit(&mut rng));
        general_case(-1.0 + 2.0 * unit(&mut rng));
    }
    for edge in [
        f64::from_bits(0xc042_b708_8723_20e2),
        -37.0,
        -0.03125,
        0.03125,
        704.0,
        f64::from_bits(0x4086_2e42_fefa_39f0),
    ] {
        for offset in 0..=32 {
            general_case(f64::from_bits(edge.to_bits() - offset));
            general_case(f64::from_bits(edge.to_bits() + offset));
        }
    }
    // Finite inputs outside the general fallback's proved domain, including
    // cancellation to zero: the transcription must still match its operations.
    for x in [-38.0, -37.43, -0.02, -0.0, 0.0, 0.02] {
        general_case(x);
    }
    for case in include_str!("../../reference/fixtures/expm1.json")
        .lines()
        .filter(|line| line.trim_start().starts_with("\"x\":"))
    {
        general_case(crate::test_exact::word(case, "x"));
    }
    assert!(
        seen.into_iter().all(core::convert::identity),
        "all expm1 fallback table indices"
    );
    assert!(
        accepted > 0 && rejected >= 8,
        "both expm1 fallback decisions"
    );
    assert_eq!((least_k, greatest_k), (-54, 1024), "expm1 scaling extremes");
    logarithm_fallback_corpus(&mut out);
    std::fs::write(path, out).unwrap();
}

/// Public dispatch: independent witness inputs and arbitrary binary64 encodings.
fn erfcx_public_entry_corpus(out: &mut String) {
    let mut write = |x: f64| {
        writeln!(
            out,
            "erfcx_entry {:016x} : {:016x}",
            x.to_bits(),
            crate::normal::erfcx(x).to_bits()
        )
        .unwrap();
    };
    for case in crate::test_exact::entries(
        include_str!("../../reference/fixtures/erfcx.json"),
        &["cases"],
    ) {
        write(crate::test_exact::word(case, "x"));
    }
    let mut rng = SplitMix64::new(0x6572_6663_7870_7562);
    for _ in 0..4096 {
        write(f64::from_bits(rng.next_u64()));
    }
}

/// The complete negative fallback, including both correction branches.
fn erfcx_accurate_negative_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x6572_6663_786e_6567);
    let lower = crate::erfcx::X_OVF.next_up();
    let upper = (-0.5_f64).next_down();
    let mut branches = [0; 2];
    for sample in 0..2048 {
        let x = if sample < 128 {
            f64::from_bits(lower.to_bits() - sample)
        } else if sample < 256 {
            -f64::from_bits(16.0_f64.to_bits() - 64 + sample - 128)
        } else if sample < 384 {
            f64::from_bits(upper.to_bits() + sample - 256)
        } else if sample % 2 == 0 {
            lower + (upper - lower) * unit(&mut rng)
        } else {
            -f64::from_bits(
                0.5_f64.to_bits() + 1 + rng.next_u64() % ((-lower).to_bits() - 0.5_f64.to_bits()),
            )
        }
        .clamp(lower, upper);
        branches[usize::from(-x >= 16.0)] += 1;
        writeln!(
            out,
            "erfcx_accurate_negative {:016x} : {}",
            x.to_bits(),
            q256(crate::erfcx::accurate_negative(x))
        )
        .unwrap();
    }
    assert!(
        branches.into_iter().all(|count| count >= 256),
        "both accurate erfcx reflection corrections"
    );
}

/// Accurate Taylor fields: every center, interval boundaries, tiny residuals.
fn erfcx_accurate_taylor_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x6572_6663_7874_6179);
    let mut seen = [false; 177];
    for sample in 0..4096 {
        let x = if sample < 177 * 9 {
            let i = u32::try_from(sample / 9).unwrap();
            let (center, radius) = if i < 49 {
                ((f64::from(i) - 16.0) / 32.0, 1.0 / 64.0)
            } else {
                let scale = f64::from(1_u32 << ((i - 49) / 32));
                (
                    scale * (1.0 + f64::from(2 * ((i - 49) % 32) + 1) / 64.0),
                    scale / 64.0,
                )
            };
            match sample % 9 {
                0 => center,
                1 => center.next_down(),
                2 => center.next_up(),
                3 => center - radius,
                4 => center + radius,
                5 => (center - radius).next_down(),
                6 => (center - radius).next_up(),
                7 => (center + radius).next_down(),
                _ => (center + radius).next_up(),
            }
        } else {
            match sample - 177 * 9 {
                0 => 0.0,
                1 => -0.0,
                2 => f64::from_bits(1),
                3 => -f64::from_bits(1),
                4 => f64::MIN_POSITIVE,
                5 => -f64::MIN_POSITIVE,
                6 => f64::from_bits(f64::MIN_POSITIVE.to_bits() - 1),
                7 => -f64::from_bits(f64::MIN_POSITIVE.to_bits() - 1),
                _ if sample % 2 == 0 => -0.5 + 16.5 * unit(&mut rng),
                _ => {
                    let negative = rng.next_u64() & 1 != 0;
                    let upper = if negative {
                        0.5_f64.to_bits()
                    } else {
                        16.0_f64.to_bits()
                    };
                    let bits = rng.next_u64() % upper;
                    f64::from_bits(bits | if negative { 1_u64 << 63 } else { 0 })
                }
            }
        }
        .clamp(-0.5, 16.0_f64.next_down());
        seen[crate::erfcx::t_reduce(x).0] = true;
        writeln!(
            out,
            "erfcx_accurate_taylor {:016x} : {}",
            x.to_bits(),
            q256(crate::erfcx::accurate_taylor(x))
        )
        .unwrap();
    }
    assert!(
        seen.into_iter().all(core::convert::identity),
        "every accurate erfcx Taylor center"
    );
}

/// Every accurate exponential table index, exact squares, and reduction edges.
fn erfcx_accurate_exponential_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x6572_6663_7865_7870);
    let mut seen = [false; 128];
    for i in 0..2048 {
        let (s, se) = if i < 384 {
            let k = [1, 512, 1023][i / 128];
            let n = f64::from(u32::try_from(k * 128 + i % 128).unwrap());
            (n / crate::exp::tables::INV_L, 0.0)
        } else {
            let bits = match i {
                384 => 0.5_f64.to_bits(),
                385 => (-crate::erfcx::X_OVF).to_bits() - 1,
                386 => 16.0_f64.to_bits(),
                _ => {
                    0.5_f64.to_bits()
                        + rng.next_u64() % ((-crate::erfcx::X_OVF).to_bits() - 0.5_f64.to_bits())
                }
            };
            let x = f64::from_bits(bits);
            crate::eft::two_prod(x, x)
        };
        let n = (s * crate::exp::tables::INV_L + crate::exp::tables::SHIFTER)
            - crate::exp::tables::SHIFTER;
        #[allow(clippy::cast_possible_truncation)] // integer shifter result, 46..=131071
        let index = (n as i32).rem_euclid(128);
        seen[usize::try_from(index).unwrap()] = true;
        let value = crate::erfcx::accurate_reflected_exp(s, se);
        writeln!(
            out,
            "erfcx_accurate_exp {:016x} {:016x} : {}",
            s.to_bits(),
            se.to_bits(),
            q256(value)
        )
        .unwrap();
    }
    assert!(
        seen.into_iter().all(core::convert::identity),
        "every accurate erfcx exponential table index"
    );
}

/// Accurate erfcx tails: loop-heavy inputs, every input binade, and subnormal seeds.
fn erfcx_accurate_tail_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x6572_6663_7851_3235);
    for i in 0_u64..4096 {
        let bits = match i {
            0 => 16.0_f64.to_bits(),
            1 => 16.0_f64.to_bits() + 1,
            2 => f64::MAX.to_bits(),
            3 => f64::MAX.to_bits() - 1,
            4 => 2045_u64 << 52,
            5 => (2045_u64 << 52) + 1,
            6 => (2045_u64 << 52) - 1,
            7..=1023 => 16.0_f64.to_bits() + rng.next_u64() % (2_u64 << 52),
            _ => ((1027 + (i - 1024) % 1020) << 52) | (rng.next_u64() >> 12),
        };
        let value = crate::erfcx::accurate_asym(f64::from_bits(bits));
        writeln!(out, "erfcx_accurate_tail {bits:016x} : {}", q256(value)).unwrap();
    }
}

fn q256_exponent_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x7132_3536_6578_7001);
    for i in 0..12_000 {
        let exponent = match i {
            0..=4 => [-518, -517, -516, -1277, 768][i],
            _ => i32::try_from(rng.next_u64() % 1_638_401).unwrap() - 819_200,
        };
        let (_, significand, _) = r256(&mut rng).parts();
        let q = if i.is_multiple_of(17) {
            Q256::ZERO
        } else {
            Q256::new(rng.next_u64() & 1 != 0, significand, exponent)
        };
        let power = match i % 7 {
            0 => 0,
            1 => -600,
            2 => 600,
            3 => -1024,
            4 => 1024,
            _ => i32::try_from(rng.next_u64() % 4097).unwrap() - 2048,
        };
        writeln!(out, "q256_top {} : {}", q256(q), q.top()).unwrap();
        writeln!(
            out,
            "q256_mul_pow2 {} {power} : {}",
            q256(q),
            q256(q.mul_pow2(power))
        )
        .unwrap();
    }
}

/// An argument of `ln_1p`'s stages: small of either sign, near −1, below and
/// above `2^53`, any encoding, or at a table interval's edge.
fn ln_1p_stage_argument(rng: &mut SplitMix64) -> f64 {
    let binade = |rng: &mut SplitMix64, low: u64, width: u64| {
        f64::from_bits(((low + rng.next_u64() % width) << 52) | (rng.next_u64() >> 12))
    };
    match rng.next_u64() % 6 {
        // 2^-60 ..= 2^-6, either sign
        0 => {
            let x = binade(rng, 963, 55);
            if rng.next_u64() & 1 == 1 { -x } else { x }
        }
        // −1 + 2^-53 ..= −1/2
        1 => -1.0 + binade(rng, 970, 52),
        // 2^-6 ..= 2^60
        2 => binade(rng, 1017, 66),
        // 2^53 ..= 2^1023
        3 => binade(rng, 1076, 947),
        4 => f64::from_bits(rng.next_u64()),
        _ => {
            // h at a table interval's edge, give or take 4 encodings: 1 + x = h.
            let i = rng.next_u64() % 512;
            let e = rng.next_u64() % 100;
            let d = rng.next_u64() % 9;
            f64::from_bits(0x3fe6_a000_0000_0000 + (i << 43) + (e << 52) + d - 4) - 1.0
        }
    }
}

fn ln_1p_stage_line(
    out: &mut String,
    op: &str,
    x: f64,
    (s, lo, eps, y): (f64, f64, f64, Option<f64>),
) {
    writeln!(
        out,
        "{op} {:016x} : {:016x} {:016x} {:016x} {}",
        x.to_bits(),
        s.to_bits(),
        lo.to_bits(),
        eps.to_bits(),
        opt(y)
    )
    .unwrap();
}

fn exp2_entry_line(out: &mut String, x: f64) {
    writeln!(
        out,
        "exp2_entry {:016x} : {:016x}",
        x.to_bits(),
        crate::exp2::exp2(x).to_bits()
    )
    .unwrap();
}

fn exp2_fast_line(out: &mut String, x: f64) {
    let (y, decided) = crate::exp2::crosscheck_fast(x);
    writeln!(
        out,
        "exp2_fast {:016x} : {:016x} {:016x} {}",
        x.to_bits(),
        y.hi().to_bits(),
        y.lo().to_bits(),
        opt(decided)
    )
    .unwrap();
}

fn expm1_entry_line(out: &mut String, x: f64) {
    writeln!(
        out,
        "expm1_entry {:016x} : {:016x}",
        x.to_bits(),
        crate::expm1::expm1(x).to_bits()
    )
    .unwrap();
}

fn logarithm_line(out: &mut String, x: f64) {
    for (op, y) in [
        ("ln_entry", crate::ln::ln(x)),
        ("ln1p_entry", crate::ln::ln_1p(x)),
    ] {
        writeln!(out, "{op} {:016x} : {:016x}", x.to_bits(), y.to_bits()).unwrap();
    }
    if x > 0.0 && x < f64::INFINITY {
        let y = crate::ln::Reduced::of(x).fast_value();
        writeln!(
            out,
            "ln_fast {:016x} : {:016x} {:016x} {}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            opt(crate::ln::decide(y))
        )
        .unwrap();
    }
    if x > -1.0 && x < f64::INFINITY && x.abs() >= f64::from_bits(0x3c90_0000_0000_0000) {
        let (y, d) = crate::ln::crosscheck_ln1p_fast(x);
        writeln!(
            out,
            "ln1p_fast {:016x} : {:016x} {:016x} {}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits(),
            opt(d)
        )
        .unwrap();
    }
}

fn logarithm_fallback_corpus(out: &mut String) {
    let mut rng = SplitMix64::new(0x6c6e_6661_6c6c_626b);
    // Every table interval, subnormal normalization, and both sides of all
    // public screens. Large ln_1p inputs include subnormal l/h quotients.
    for i in 0..=128_u64 {
        for exponent in [1, 511, 1022, 1023, 1024, 2044, 2045] {
            let edge = (exponent << 52) + (i << 45);
            for bits in [edge - 1, edge, edge + 1] {
                let x = f64::from_bits(bits);
                logarithm_line(out, x);
                if exponent == 1 {
                    logarithm_line(out, x * f64::from_bits(0x3c90_0000_0000_0000));
                }
            }
        }
    }
    for edge in [
        0x3c90_0000_0000_0000_u64,
        0x3f80_0000_0000_0000,
        0x3ff0_0000_0000_0000,
        0x4340_0000_0000_0000,
        0x7fd0_0000_0000_0000,
        0x7fe0_0000_0000_0000,
        0x7fef_ffff_ffff_ffff,
    ] {
        for offset in 0..=8 {
            for bits in [edge - offset, edge + offset] {
                logarithm_line(out, f64::from_bits(bits));
                logarithm_line(out, -f64::from_bits(bits));
            }
        }
    }
    for bits in [
        0,
        1,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0xfff0_0000_0000_0001,
        0x7ff8_0000_0000_0042,
        0xfff8_0000_0000_0042,
    ] {
        logarithm_line(out, f64::from_bits(bits));
    }
    for case in include_str!("../../reference/fixtures/ln.json")
        .lines()
        .filter(|l| l.trim_start().starts_with("\"x\":"))
    {
        logarithm_line(out, crate::test_exact::word(case, "x"));
    }
    for _ in 0..4000 {
        logarithm_line(out, ln_argument(&mut rng));
        logarithm_line(out, ln_1p_argument(&mut rng));
        logarithm_line(out, f64::from_bits(rng.next_u64()));
    }
    // Explicitly include rounding-test rejections, including the small
    // ln_1p branch, without inflating extraction with the search stream.
    for kind in 0..3 {
        let mut rejected = 0;
        for _ in 0..(1 << 22) {
            let x = if kind == 0 {
                ln_argument(&mut rng)
            } else if kind == 1 {
                ln_1p_argument(&mut rng)
            } else {
                (unit(&mut rng) - 0.5) / 64.0
            };
            let decision = if kind == 0 {
                crate::ln::decide(crate::ln::Reduced::of(x).fast_value())
            } else {
                crate::ln::crosscheck_ln1p_fast(x).1
            };
            if decision.is_none() {
                logarithm_line(out, x);
                rejected += 1;
                if rejected == 8 {
                    break;
                }
            }
        }
        assert_eq!(rejected, 8, "logarithm fallback rejection coverage {kind}");
    }
}

/// Explicit fast entry transcriptions, including screen neighbors and fallback
/// inputs. Exp supplies its unchanged strong owner's result separately; the
/// extraction verifies dispatch and the complete accelerated arithmetic.
fn fast_corpus(out: &mut String) {
    let mut write = |x: f64| {
        writeln!(
            out,
            "fast_ln {:016x} : {:016x}",
            x.to_bits(),
            crate::fast::elementary::ln(x).to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "fast_exp {:016x} {:016x} : {:016x}",
            x.to_bits(),
            crate::elementary::exp(x).to_bits(),
            crate::fast::elementary::exp(x).to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "fast_exp_coarse {:016x} {:016x} : {:016x}",
            x.to_bits(),
            crate::elementary::exp(x).to_bits(),
            crate::fast::elementary::exp_coarse(x).to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "fast_erfcx {:016x} : {:016x}",
            x.to_bits(),
            crate::fast::normal::erfcx(x).to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "fast_normal {:016x} : {:016x}",
            x.to_bits(),
            crate::fast::normal::norm_cdf(x).to_bits()
        )
        .unwrap();
        writeln!(
            out,
            "fast_log_cdf {:016x} : {:016x}",
            x.to_bits(),
            crate::fast::normal::log_norm_cdf(x).to_bits()
        )
        .unwrap();
    };
    for x in [
        0.0_f64,
        -0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        -704.0,
        704.0,
        -0.5,
        -1.0,
        1.0,
        16.0,
        -8.0,
        8.0,
        -f64::from_bits(0x3de0_0000_0000_0000),
        f64::from_bits(0x3de0_0000_0000_0000),
        -745.0,
        710.0,
        f64::MAX,
        -f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits(0x7ff8_1234_5678_9abc),
        f64::from_bits(0xfff8_1234_5678_9abc),
    ] {
        write(x.next_down());
        write(x);
        write(x.next_up());
    }
    let mut rng = SplitMix64::new(0xfa57_2026_1027_0002);
    for _ in 0..512 {
        write(f64::from_bits(rng.next_u64()));
        write(-704.0 + 1408.0 * unit(&mut rng));
        write(-0.5 + 16.5 * unit(&mut rng));
        write(-8.0 + 16.0 * unit(&mut rng));
    }
}
