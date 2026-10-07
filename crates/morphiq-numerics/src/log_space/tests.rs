//! `log_sum_exp` and `log_diff_exp` against the reference fixture
//! (`generators/log_space_reference.py`; docs/log_space.md §9).
//!
//! Exact cases must match bit for bit (any NaN where the fixture says `nan`).
//! A bounded case passes when `lo ≤ ŷ ≤ hi`: the documented bound around the
//! exact result, rounded inward, so the comparison is exact.

use super::{log_diff_exp, log_sum_exp};
use crate::test_exact::{entries, field, word};
use std::vec::Vec;

const FIXTURE: &str = include_str!("../../../reference/fixtures/log_space.json");

/// A `log_sum_exp` input: its elements' encodings, space-separated.
fn xs(case: &str) -> Vec<f64> {
    field(case, "x")
        .split_whitespace()
        .map(|bits| f64::from_bits(u64::from_str_radix(bits, 16).unwrap()))
        .collect()
}

fn same(got: f64, case: &str) -> bool {
    match field(case, "y") {
        "nan" => got.is_nan(),
        _ => got.to_bits() == word(case, "y").to_bits(),
    }
}

/// Checks every bounded case, and reports how far the results that are not
/// correctly rounded are from RN(y), in ulps of RN(y): `[1, 2, 3, 4–15, ≥ 16]`.
///
/// Distances above one ulp come from cancellation between `m` and `L`: the
/// bound's `β·u·|L|` term is absolute, and can be many ulps of a small `y`.
/// A result on the other side of zero from `RN(y)` counts as `≥ 16`.
fn check_bounded(name: &str, cases: &[&str], f: impl Fn(&str) -> f64) {
    let mut correctly_rounded = 0;
    let mut by_distance = [0usize; 5];
    for case in cases {
        let got = f(case);
        let (lo, hi, rn) = (word(case, "lo"), word(case, "hi"), word(case, "rn"));
        assert!(
            lo <= got && got <= hi,
            "{name} {case}: {got:e} outside [{lo:e}, {hi:e}]"
        );
        if got.to_bits() == rn.to_bits() || (got == 0.0 && rn == 0.0) {
            correctly_rounded += 1;
            continue;
        }
        let same_side = got.is_sign_negative() == rn.is_sign_negative() && got != 0.0 && rn != 0.0;
        let ulps = if same_side {
            got.to_bits().abs_diff(rn.to_bits())
        } else {
            u64::MAX
        };
        by_distance[match ulps {
            1 => 0,
            2 => 1,
            3 => 2,
            4..=15 => 3,
            _ => 4,
        }] += 1;
    }
    std::eprintln!(
        "{name}: {} bounded cases within the bound; {correctly_rounded} correctly rounded; \
         the rest by ulps from RN(y) [1, 2, 3, 4-15, >=16]: {by_distance:?}",
        cases.len()
    );
}

#[test]
fn log_sum_exp_special_values_are_exact() {
    let cases = entries(FIXTURE, &["log_sum_exp", "exact"]);
    assert_eq!(cases.len(), 29);
    for case in cases {
        let got = log_sum_exp(&xs(case));
        assert!(
            same(got, case),
            "{case}: got {got:e} ({:016x})",
            got.to_bits()
        );
    }
}

#[test]
fn log_diff_exp_special_values_are_exact() {
    let cases = entries(FIXTURE, &["log_diff_exp", "exact"]);
    assert_eq!(cases.len(), 21);
    for case in cases {
        let got = log_diff_exp(word(case, "a"), word(case, "b"));
        assert!(
            same(got, case),
            "{case}: got {got:e} ({:016x})",
            got.to_bits()
        );
    }
}

#[test]
fn log_sum_exp_is_within_its_bound() {
    let cases = entries(FIXTURE, &["log_sum_exp", "bounded"]);
    assert_eq!(cases.len(), 651);
    check_bounded("log_sum_exp", &cases, |c| log_sum_exp(&xs(c)));
}

#[test]
fn log_diff_exp_is_within_its_bound() {
    let cases = entries(FIXTURE, &["log_diff_exp", "bounded"]);
    assert_eq!(cases.len(), 451);
    check_bounded("log_diff_exp", &cases, |c| {
        log_diff_exp(word(c, "a"), word(c, "b"))
    });
}

#[test]
fn labelled_cases_are_present() {
    // The hand-picked edge cases carry labels; a regenerated fixture that lost
    // them would silently weaken the tests above.
    for (name, expected) in [("log_sum_exp", 51), ("log_diff_exp", 51)] {
        let labelled = entries(FIXTURE, &[name, "bounded"])
            .into_iter()
            .filter(|c| c.contains("\"label\":"))
            .count();
        assert_eq!(labelled, expected, "{name}");
    }
}

#[test]
fn log_sum_exp_does_not_depend_on_where_zero_mass_sits() {
    let a = log_sum_exp(&[-1.5, 0.25, -3.0]);
    let b = log_sum_exp(&[f64::NEG_INFINITY, -1.5, f64::NEG_INFINITY, 0.25, -3.0]);
    assert_eq!(a.to_bits(), b.to_bits());
}

/// Local cost, for docs/log_space.md §8: `cargo test --release -p
/// morphiq-numerics measure_cost -- --ignored --nocapture`. Not a gate.
#[test]
#[ignore = "a local measurement, not a check"]
fn measure_cost() {
    use std::time::Instant;
    let mut stream = crate::random::SplitMix64::new(0x1095_C057);
    let mut unit = || crate::random::unit_closed_open(stream.next_u64());
    let pairs: Vec<(f64, f64)> = (0..1 << 16)
        .map(|_| {
            let a = 40.0 * unit() - 20.0;
            (a, a - 30.0 * unit() - 1e-9)
        })
        .collect();
    type Binary = fn(f64, f64) -> f64;
    let functions: [(&str, Binary); 2] = [
        ("log_sum_exp, n = 2", |a, b| log_sum_exp(&[a, b])),
        ("log_diff_exp", log_diff_exp),
    ];
    for (name, f) in functions {
        let mut sink = 0.0;
        let start = Instant::now();
        for _ in 0..16 {
            for &(a, b) in &pairs {
                sink += f(core::hint::black_box(a), core::hint::black_box(b));
            }
        }
        #[allow(clippy::cast_precision_loss)] // timing arithmetic
        let ns = start.elapsed().as_nanos() as f64 / (16.0 * pairs.len() as f64);
        std::eprintln!("{name}: {ns:.1} ns per call ({sink:e})");
    }
}
