//! Writes the internal cross-check corpus: `Q128` and `Q256` operations, the
//! rounding tests (`ln::decide_with`, `exp::decide_scaled`), `exp`'s stages
//! (`Stages::of`, `a_value`, `a`, `b_value`, `b`), the fallback's reduction,
//! fast value (`exp::fast_at`), accurate path (`Reduced::accurate_value`) and
//! small-argument path (`exp::small_parts`, `exp::small`), and `ln`'s
//! reduction (`ln::Reduced::of`, `z`, `z_exact`), the accurate values of `ln`
//! and `ln_1p` (`Reduced::accurate_value`, `z_prime`, `ln::split`,
//! `ln::small_accurate`) and `ln_1p`'s screens and stages H and B
//! (`ln::stages::stage_h_screen`, `stage_b_screen`, `stage_h_parts`,
//! `stage_b_parts`), and `exp2`'s fallback reduction and accurate value
//! on reproducible inputs, with
//! this crate's results. `scripts/check_formal.sh` runs the proved
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
    std::fs::write(path, out).unwrap();
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
