//! `log2`'s and `log10`'s unrounded results against their certified bounds,
//! and their fast paths against their accurate paths (docs/log2.md).

use super::{log2_accurate, log2_fast, log10_accurate, log10_fast};
use crate::double_word::kernel::DoubleWord;
use crate::ln::{Reduced, decide};
use crate::q128::Q128;
use crate::random::SplitMix64;
use crate::test_exact::{Exact, entries, field, word};

const FIXTURE: &str = include_str!("../../../reference/fixtures/log2_log10.json");

fn double_word(y: DoubleWord) -> Exact {
    Exact::of(Q128::from_f64(y.hi())).add(&Exact::of(Q128::from_f64(y.lo())))
}

fn check(function: &str, fast: fn(&Reduced) -> DoubleWord, accurate: fn(&Reduced) -> Q128) {
    let cases = entries(FIXTURE, &["precise", function]);
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
        // §3–§5: the fast paths within 2^-63, the accurate within 2^-122.
        assert!(
            double_word(fast(&reduced)).within(&reference, 1, 63),
            "fast, {function}({x:e})"
        );
        assert!(
            Exact::of(accurate(&reduced)).within(&reference, 1, 122),
            "accurate, {function}({x:e})"
        );
    }
}

#[test]
fn every_unrounded_log2_is_within_its_certified_bound() {
    check("log2", log2_fast, log2_accurate);
}

#[test]
fn every_unrounded_log10_is_within_its_certified_bound() {
    check("log10", log10_fast, log10_accurate);
}

fn check_accurate_rounding(function: &str, accurate: fn(&Reduced) -> Q128) {
    // The generated fixture places its rounded arrays after the same-named
    // arrays of 192-bit values in `precise`.
    let key = std::format!("\"{function}\": [");
    let rounded = &FIXTURE[FIXTURE.rfind(&key).unwrap()..];
    let cases = entries(rounded, &[function]);
    assert_eq!(cases.len(), if function == "log2" { 4029 } else { 4034 });
    for case in cases {
        let x = word(case, "x");
        if !x.is_finite() || x <= 0.0 {
            continue;
        }
        let expected = word(case, function);
        let got = accurate(&Reduced::of(x)).to_f64();
        assert_eq!(
            got.to_bits(),
            expected.to_bits(),
            "accurate {function}({x:e}), input {:016x}",
            x.to_bits()
        );
    }
}

#[test]
fn log2_accurate_rounding_matches_the_independent_fixture() {
    check_accurate_rounding("log2", log2_accurate);
}

#[test]
fn log10_accurate_rounding_matches_the_independent_fixture() {
    // This fixture observation does not claim whole-domain correct rounding:
    // log10 retains its documented bounded accurate-path contract.
    check_accurate_rounding("log10", log10_accurate);
}

/// The analytic miss rate with `ε₁ = 2^−63`, as for `ln`: at most `2^−9`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 512.0;

fn agreement(
    name: &str,
    fast: fn(&Reduced) -> DoubleWord,
    accurate: fn(&Reduced) -> Q128,
    seed: u64,
) {
    let mut rng = SplitMix64::new(seed);
    let (mut tried, mut missed) = (0u32, 0u32);
    for n in 0..(1u32 << 20) {
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
        match decide(fast(&reduced)) {
            Some(y) => assert_eq!(
                y.to_bits(),
                accurate(&reduced).to_f64().to_bits(),
                "{name}({x:e})"
            ),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("{name} fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(
        rate <= 4.0 * ANALYTIC_MISS_RATE,
        "{name} miss rate {rate:e}"
    );
}

#[test]
fn log2_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    agreement("log2", log2_fast, log2_accurate, 0x6c6f_6732_7061_7331);
}

#[test]
fn log10_fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    agreement("log10", log10_fast, log10_accurate, 0x6c6f_6731_3070_6131);
}
