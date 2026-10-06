//! The reduction against 256-bit references (docs/sin_cos.md §3).

use super::reduce;
use crate::test_exact::{Exact, entries, field, word};

#[test]
fn the_reduction_is_within_its_bound_everywhere() {
    let fixture = include_str!("../../../reference/fixtures/sin_cos.json");
    let cases = entries(fixture, &["reduction"]);
    assert_eq!(cases.len(), 607);
    for c in cases {
        let x = word(c, "x");
        let v = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        let reference = if field(c, "negative") == "true" {
            v.neg()
        } else {
            v
        };
        let (k, r) = reduce(x);
        assert_eq!(
            k,
            field(c, "k").parse::<u32>().unwrap(),
            "k mod 4 for {x:e}"
        );
        assert!(Exact::of_q256(r).within(&reference, 1, 199), "r for {x:e}");
    }
}

use super::{EPS, EPS_TAN, Function, Reduced, accurate, fast, tan, tan_accurate, tan_fast};
use crate::double_word::DoubleWord;
use crate::ln::decide_with;
use crate::q128::Q128;
use crate::random::SplitMix64;

fn double_word(y: DoubleWord) -> Exact {
    Exact::of(Q128::from_f64(y.hi())).add(&Exact::of(Q128::from_f64(y.lo())))
}

/// The value `Reduced::finish` approximates: `±sin r` or `±cos r`.
fn selected(reduced: &Reduced, function: Function) -> (DoubleWord, Exact) {
    let (use_cos, negate) = reduced.select(function);
    let (s, c) = fast(&reduced.r);
    let (sa, ca) = accurate(reduced.r);
    let (y, a) = if use_cos { (c, ca) } else { (s, sa) };
    let a = Exact::of_q256(a);
    if negate { (y.neg(), a.neg()) } else { (y, a) }
}

#[test]
fn every_unrounded_result_is_within_its_certified_bound() {
    let fixture = include_str!("../../../reference/fixtures/sin_cos.json");
    let cases = entries(fixture, &["precise"]);
    assert_eq!(cases.len(), 1200);
    for c in cases {
        let x = word(c, "x");
        let reduced = Reduced::of(x);
        for (name, function) in [("sin", Function::Sin), ("cos", Function::Cos)] {
            let key = |suffix: &str| std::format!("{name}_{suffix}");
            let reference = {
                let v = Exact::of_hex(field(c, &key("m")), field(c, &key("e")).parse().unwrap());
                if field(c, &key("negative")) == "true" {
                    v.neg()
                } else {
                    v
                }
            };
            let (fast_value, accurate_value) = selected(&reduced, function);
            // §4: 2^-62. §5: 2^-198.
            assert!(
                double_word(fast_value).within(&reference, 1, 62),
                "fast {name}({x:e})"
            );
            assert!(
                accurate_value.within(&reference, 1, 198),
                "accurate {name}({x:e})"
            );
        }
    }
}

/// The analytic miss rate with `ε₁ = 2^−62`: at most `2^−8`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 256.0;

#[test]
fn fast_paths_agree_with_the_accurate_paths_and_mostly_decide() {
    let mut rng = SplitMix64::new(0x7472_6967_7061_7373);
    for (name, function) in [("sin", Function::Sin), ("cos", Function::Cos)] {
        let (mut tried, mut missed) = (0u32, 0u32);
        for n in 0..(1u32 << 16) {
            let x = if n % 2 == 0 {
                f64::from_bits(
                    0x3e60_0000_0000_0000
                        + rng.next_u64() % (0x7fef_ffff_ffff_ffff - 0x3e60_0000_0000_0000),
                )
            } else {
                #[allow(clippy::cast_precision_loss)]
                let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
                u * 8.0
            };
            if x <= f64::from_bits(0x3e60_0000_0000_0000) {
                continue;
            }
            let reduced = Reduced::of(x);
            tried += 1;
            let (use_cos, negate) = reduced.select(function);
            let (s, c) = fast(&reduced.r);
            let y = if use_cos { c } else { s };
            let y = if negate { y.neg() } else { y };
            match decide_with(y, EPS) {
                Some(v) => assert_eq!(
                    v.to_bits(),
                    reduced.finish(function).to_bits(),
                    "{name}({x:e})"
                ),
                None => missed += 1,
            }
            let (sa, ca) = accurate(reduced.r);
            let a = if use_cos { ca } else { sa };
            let a = if negate { a.neg() } else { a };
            assert_eq!(
                reduced.finish(function).to_bits(),
                match decide_with(y, EPS) {
                    Some(v) => v,
                    None => a.to_f64(),
                }
                .to_bits()
            );
        }
        let rate = f64::from(missed) / f64::from(tried);
        std::eprintln!(
            "{name} fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})"
        );
        assert!(
            rate <= 4.0 * ANALYTIC_MISS_RATE,
            "{name} miss rate {rate:e}"
        );
    }
}

#[test]
fn every_unrounded_tan_is_within_its_certified_bound() {
    let fixture = include_str!("../../../reference/fixtures/tan.json");
    let cases = entries(fixture, &["precise"]);
    assert_eq!(cases.len(), 1200);
    for c in cases {
        let x = word(c, "x");
        let v = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        let reference = if field(c, "negative") == "true" {
            v.neg()
        } else {
            v
        };
        let reduced = Reduced::of(x);
        // §8: 2^-60 and 2^-196.
        let fast_value = tan_fast(&reduced).expect("inside the division's domain");
        assert!(
            double_word(fast_value).within(&reference, 1, 60),
            "fast tan({x:e})"
        );
        assert!(
            Exact::of_q256(tan_accurate(&reduced)).within(&reference, 1, 196),
            "accurate tan({x:e})"
        );
    }
}

/// The analytic miss rate with `ε₁ = 2^−60`: at most `2^−6`.
const ANALYTIC_TAN_MISS_RATE: f64 = 1.0 / 64.0;

#[test]
fn tan_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x7461_6e70_6173_7301);
    let (mut tried, mut missed) = (0u32, 0u32);
    for n in 0..(1u32 << 16) {
        let x = if n % 2 == 0 {
            f64::from_bits(
                0x3e60_0000_0000_0000
                    + rng.next_u64() % (0x7fef_ffff_ffff_ffff - 0x3e60_0000_0000_0000),
            )
        } else {
            #[allow(clippy::cast_precision_loss)]
            let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
            u * 8.0
        };
        if x <= f64::from_bits(0x3e60_0000_0000_0000) {
            continue;
        }
        let reduced = Reduced::of(x);
        tried += 1;
        let accurate_value = tan_accurate(&reduced).to_f64();
        match tan_fast(&reduced).and_then(|y| decide_with(y, EPS_TAN)) {
            Some(v) => assert_eq!(v.to_bits(), accurate_value.to_bits(), "tan({x:e})"),
            None => missed += 1,
        }
        assert_eq!(
            tan(x).to_bits(),
            tan(-x).to_bits() ^ (1 << 63),
            "tan(-{x:e})"
        );
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("tan fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(
        rate <= 4.0 * ANALYTIC_TAN_MISS_RATE,
        "tan miss rate {rate:e}"
    );
}

/// `r` rounds every value within `2^−198` relatively of `a`: both midpoints
/// beside `r` lie farther from `a` than that.
fn rounds_alike(a: &Exact, r: f64) -> bool {
    let bound = a.abs().mul(&Exact::pow2(-198));
    let r_exact = Exact::of_f64(r);
    [
        f64::from_bits(r.to_bits() - 1),
        f64::from_bits(r.to_bits() + 1),
    ]
    .iter()
    .all(|&n| {
        let mid = r_exact.add(&Exact::of_f64(n)).mul(&Exact::pow2(-1));
        a.sub(&mid).abs().cmp(&bound) == core::cmp::Ordering::Greater
    })
}

/// `normal_pair` (`docs/random.md`) evaluates `sin` at `φ = RN(RN(2π)·m·2^−53)`
/// for integer `m ≤ 2^50`. [LM] covers `φ ≤ 1.4422·2^−26` and `φ ≥ 2^−24`;
/// every `φ` between is checked here: the fast path's rounding test decides
/// it (§6), or the accurate path's `2^−198` enclosure rounds to one binary64.
/// Either way `sin(φ)` is correctly rounded, by the certified bounds.
#[test]
fn sin_is_correctly_rounded_at_every_small_normal_pair_angle() {
    const TAU: f64 = f64::from_bits(0x4019_21fb_5444_2d18);
    let scale = f64::from_bits((1023 - 53) << 52);
    let below = f64::from_bits(0x3e70_0000_0000_0000); // 2^-24
    let phi = |m: u64| {
        #[allow(clippy::cast_precision_loss)] // m < 2^30
        let v = m as f64 * scale;
        TAU * v
    };
    // The least m whose angle exceeds the threshold, by bisection: phi is
    // nondecreasing in m.
    let (mut lo, mut hi) = (0_u64, 1 << 30);
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if phi(mid) <= super::SIN_IS_X {
            lo = mid
        } else {
            hi = mid
        }
    }
    let (mut checked, mut accurate_needed) = (0_u64, 0_u64);
    let mut m = hi;
    while phi(m) < below {
        let x = phi(m);
        let reduced = Reduced::of(x);
        let (s, _) = fast(&reduced.r);
        if decide_with(s, EPS).is_none() {
            accurate_needed += 1;
            // sin returns the accurate value rounded (Reduced::finish).
            let (a, _) = accurate(reduced.r);
            assert!(
                rounds_alike(&Exact::of_q256(a), a.to_f64()),
                "sin({x:e}) undecided"
            );
        }
        checked += 1;
        m += 1;
    }
    std::eprintln!("small sin angles: {checked} checked, {accurate_needed} by the accurate path");
    assert_eq!(checked, 70_041_414);
}
