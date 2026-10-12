//! The fast paths against the accurate paths, their pass rates, and every
//! unrounded result against its certified bound (docs/ln.md §4–§7).

use super::{EPS, Reduced, TWO_M7, decide, ln_1p_double_word, series, split};
use crate::double_word::DoubleWord;
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::{Exact, entries, field, word};

fn double_word(y: DoubleWord) -> Exact {
    Exact::of(Q128::from_f64(y.hi())).add(&Exact::of(Q128::from_f64(y.lo())))
}

const FIXTURE: &str = include_str!("../../../reference/fixtures/ln.json");

/// A signed 192-bit reference from a fixture object.
fn reference(c: &str) -> Exact {
    let v = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
    if field(c, "negative") == "true" {
        v.neg()
    } else {
        v
    }
}

/// The fixture's 192-bit references for `function`: `(x, value)`.
fn precise(function: &str) -> std::vec::Vec<(f64, Exact)> {
    entries(FIXTURE, &["precise", function])
        .into_iter()
        .map(|c| (word(c, "x"), reference(c)))
        .collect()
}

#[test]
fn every_unrounded_ln_is_within_its_certified_bound() {
    let cases = precise("ln");
    assert_eq!(cases.len(), 1200);
    for (x, reference) in cases {
        let reduced = Reduced::of(x);
        let (s, lo, eps, _) = super::stage::parts(reduced.e, reduced.y);
        let exact = |x| Exact::of(Q128::from_f64(x));
        let error = exact(s).add(&exact(lo)).sub(&reference).abs();
        assert!(
            error.cmp(&exact(eps)) != core::cmp::Ordering::Greater,
            "reciprocal stage, ln({x:e})"
        );
        // §4: 2^-64. §6: 2^-123.
        assert!(
            double_word(reduced.fast_value()).within(&reference, 1, 64),
            "fast, ln({x:e})"
        );
        let y = Exact::of(reduced.accurate_value(reduced.z_exact()));
        assert!(y.within(&reference, 1, 123), "accurate, ln({x:e})");
    }
}

#[test]
fn every_unrounded_ln_1p_is_within_its_certified_bound() {
    let cases = precise("ln_1p");
    assert_eq!(cases.len(), 1400);
    for (x, reference) in cases {
        let (fast, accurate) = if x.abs() < TWO_M7 {
            let z = Q128::from_f64(x);
            (ln_1p_double_word(DoubleWord::from_f64(x)), z.mul(series(z)))
        } else {
            let (h, l) = split(x);
            let reduced = Reduced::of(h);
            (
                reduced.fast_value().add_f64(l / h),
                reduced.accurate_value(reduced.z_prime(l)),
            )
        };
        // §7: the fast path within 2^-63 (2^-64 on the z = x branch), the
        // accurate path within 2^-123.
        assert!(
            double_word(fast).within(&reference, 1, 63),
            "fast, ln_1p({x:e})"
        );
        assert!(
            Exact::of(accurate).within(&reference, 1, 123),
            "accurate, ln_1p({x:e})"
        );
    }
}

/// The analytic miss rate of the rounding test with `ε₁ = 2^−63`: an
/// argument misses when its value lies within `ε₁·|Y|` of a breakpoint, a
/// fraction `2·ε₁·|Y| / ulp(Y) ≤ 2^−9` of each gap.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 512.0;

#[test]
fn ln_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6c6e_5f70_6173_7331);
    let (mut tried, mut missed) = (0u32, 0u32);
    let mut stage_missed = 0u32;
    for n in 0..(1u32 << 20) {
        // Every positive finite encoding, and arguments near 1.
        let x = if n % 2 == 0 {
            f64::from_bits(1 + rng.next_u64() % 0x7fef_ffff_ffff_ffff)
        } else {
            f64::from_bits(0x3fe0_0000_0000_0000 + rng.next_u64() % (1 << 53))
        };
        if x == 1.0 {
            continue;
        }
        let reduced = Reduced::of(x);
        tried += 1;
        let accurate = reduced.accurate_value(reduced.z_exact()).to_f64();
        if let Some(y) = super::stage::parts(reduced.e, reduced.y).3 {
            assert_eq!(
                y.to_bits(),
                accurate.to_bits(),
                "reciprocal stage ln({x:e})"
            );
        } else {
            stage_missed += 1;
        }
        match decide(reduced.fast_value()) {
            Some(y) => {
                assert_eq!(y.to_bits(), accurate.to_bits(), "ln({x:e})");
            }
            None => missed += 1,
        }
    }
    std::eprintln!("ln reciprocal stage: {stage_missed} of {tried} sent to the fallback");
    assert!(stage_missed < tried / 64);
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("ln fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

#[test]
fn ln_1p_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6c6e_3170_7061_7331);
    let (mut tried, mut missed) = (0u32, 0u32);
    for _ in 0..(1u32 << 20) {
        // Magnitudes from 2^-54 to 2^1023, either sign where ln_1p is defined.
        let e = 969 + rng.next_u64() % 1077;
        let x = f64::from_bits((e << 52) | (rng.next_u64() >> 12) | (rng.next_u64() & 1) << 63);
        if x <= -1.0 {
            continue;
        }
        tried += 1;
        let (fast, accurate) = if x.abs() < TWO_M7 {
            let z = Q128::from_f64(x);
            (
                decide(ln_1p_double_word(DoubleWord::from_f64(x))),
                z.mul(series(z)),
            )
        } else {
            let (h, l) = split(x);
            let reduced = Reduced::of(h);
            (
                decide(reduced.fast_value().add_f64(l / h)),
                reduced.accurate_value(reduced.z_prime(l)),
            )
        };
        match fast {
            Some(y) => assert_eq!(y.to_bits(), accurate.to_f64().to_bits(), "ln_1p({x:e})"),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("ln_1p fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

/// The rounding test's constant is `ε₁·(1 + 2^−50)` with `ε₁ = 2^−63` (§5).
#[test]
fn rounding_test_constant_is_its_definition() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(EPS.to_bits(), (two(-63) * (1.0 + two(-50))).to_bits());
}

#[test]
fn ln_1p_of_a_double_word_is_within_its_certified_bound() {
    let cases = entries(FIXTURE, &["precise", "ln_1p_z"]);
    assert!(cases.len() > 500);
    for c in cases {
        let (z_hi, z_lo) = (word(c, "z_hi"), word(c, "z_lo"));
        let reference = reference(c);
        // §4, step 4: 3·2^-66 (formal/ln/p.g).
        let p = ln_1p_double_word(DoubleWord::sum(z_hi, z_lo));
        assert!(
            double_word(p).within(&reference, 3, 66),
            "ln(1 + {z_hi:e} + {z_lo:e})"
        );
    }
}

/// §5's test at its boundary: `y_hi` returned exactly when `|y_lo| + EPS·|y_hi|`
/// is below half the smaller gap, for either sign and at a power of two, where
/// the gap toward zero is half the other.
#[test]
fn the_rounding_test_decides_at_its_boundary() {
    for y_hi in [1.5, -1.5, 1.0, -1.0, 0.75, -0.75, 600.25, -600.25] {
        let magnitude = f64::abs(y_hi);
        let mut gap = crate::ulp::ulp(magnitude);
        if magnitude.to_bits() & super::FRACTION == 0 {
            gap *= 0.5;
        }
        let margin = EPS * magnitude;
        for (y_lo, decided) in [
            (0.5 * gap - 2.0 * margin, true),
            (0.5 * gap - 0.5 * margin, false),
            (-(0.5 * gap - 2.0 * margin), true),
            (-(0.5 * gap - 0.5 * margin), false),
        ] {
            let y = DoubleWord::sum(y_hi, y_lo);
            assert_eq!(decide(y).is_some(), decided, "({y_hi:e}, {y_lo:e})");
        }
    }
}

/// Arguments for stages H and B covering every branch (§7): `e^d` and `z²/4`
/// (the consumers' families), log-uniform over `(−1, 2^1020)`, random
/// encodings, small `|x|` of both signs, near −1, `l ≠ 0`, the table
/// intervals' edges at random exponents, every threshold ±2,000 encodings and
/// powers of two with their neighbours.
fn stage_corpus() -> std::vec::Vec<f64> {
    use super::stage_tables::OFF;
    let mut rng = SplitMix64::new(0x6c6e_3170_7374_6731);
    let unit = |rng: &mut SplitMix64| (rng.next_u64() >> 11) as f64 / (1u64 << 53) as f64;
    let binade = |rng: &mut SplitMix64, lo: i64, hi: i64| {
        let e = lo + (rng.next_u64() % (hi - lo) as u64) as i64;
        f64::from_bits((((1023 + e) as u64) << 52) | (rng.next_u64() >> 12))
    };
    let nudge = |x: f64, d: i64| f64::from_bits((x.to_bits() as i64).wrapping_add(d) as u64);
    let n = 1 << 16;
    let mut v = std::vec::Vec::new();
    for _ in 0..n {
        v.push(crate::elementary::exp(-30.0 * unit(&mut rng)));
        let z = 12.0 * unit(&mut rng) - 6.0;
        v.push(z * z / 4.0);
        v.push(match rng.next_u64() % 4 {
            0 | 1 => binade(&mut rng, -60, 1020),
            2 => -binade(&mut rng, -60, 0),
            _ => -1.0 + binade(&mut rng, -53, -1),
        });
        v.push(f64::from_bits(rng.next_u64()));
        let s = binade(&mut rng, -60, -6);
        v.push(if rng.next_u64() & 1 == 0 { s } else { -s });
        v.push(binade(&mut rng, -7, 60));
        let i = rng.next_u64() % 512;
        let d = (rng.next_u64() % 9) as i64 - 4;
        let e = (rng.next_u64() % 120) as i64 - 6;
        let h = f64::from_bits((OFF as i64 + (i << 43) as i64 + d + (e << 52)) as u64);
        v.push(h - 1.0);
    }
    let two = |k: i32| f64::from_bits(((1023 + k) as u64) << 52);
    for c in [
        two(-54),
        two(-46),
        two(-9),
        two(-10),
        two(53),
        two(1020),
        -1.0,
        1.0,
    ] {
        for sign in [1.0, -1.0] {
            for d in -2000..=2000 {
                v.push(nudge(sign * c, d));
            }
        }
    }
    for e in -60..1023 {
        for d in -16..=16 {
            v.push(nudge(two(e), d));
            v.push(nudge(-two(e.min(-1)), d));
            v.push(nudge(two(e), d) - 1.0);
        }
    }
    v
}

#[test]
fn each_stage_returns_the_reference_bits_wherever_it_decides() {
    use super::stages::{stage_b_parts, stage_b_screen, stage_h_parts, stage_h_screen};
    use super::{ln_1p, ln_1p_reference};
    let (mut h_tried, mut h_decided, mut b_tried, mut b_decided) = (0u32, 0u32, 0u32, 0u32);
    for x in stage_corpus() {
        let want = ln_1p_reference(x).to_bits();
        if stage_h_screen(x) {
            h_tried += 1;
            if let Some(y) = stage_h_parts(x).3 {
                h_decided += 1;
                assert_eq!(y.to_bits(), want, "stage H at {x:e}");
            }
        }
        if stage_b_screen(x) {
            b_tried += 1;
            if let Some(y) = stage_b_parts(x).3 {
                b_decided += 1;
                assert_eq!(y.to_bits(), want, "stage B at {x:e}");
            }
        }
        assert_eq!(ln_1p(x).to_bits(), want, "ln_1p at {x:e}");
    }
    std::eprintln!("stage H decided {h_decided} of {h_tried}, stage B {b_decided} of {b_tried}");
    assert!(h_decided > h_tried - h_tried / 64);
    assert!(b_decided > b_tried - b_tried / 64);
}
