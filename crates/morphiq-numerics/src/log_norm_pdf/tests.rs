//! `log_norm_pdf` against the correctly rounded references of
//! `generators/log_norm_pdf_reference.py` (docs/log_norm_pdf.md §6).
//!
//! Every result must be correctly rounded. Decision 1 allows an exception only
//! in regime M where the rounding test of §3 does not decide, and then within
//! `(1/2 + 2^−50)` ulp; the test below checks any mismatch against both
//! conditions.

use super::tables::{C_HI, C_LO};
use super::{TWO_500, TWO_M27, log_norm_pdf};
use crate::double_word::DoubleWord;
use crate::ln::decide_with;
use crate::test_exact::{entries, word};
use crate::ulp::ulp;
use std::vec::Vec;

const FIXTURE: &str = include_str!("../../../reference/fixtures/log_norm_pdf.json");

/// `EPS = 2^−80·(1 + 2^−50)`: decision 2's rounding test at `ε₁ = 2^−80`.
const EPS: f64 = f64::from_bits(0x3af0_0000_0000_0004);

/// Is `x`'s result covered by the correct-rounding guarantee?
fn decided(x: f64) -> bool {
    let a = x.abs();
    if !(TWO_M27..=TWO_500).contains(&a) {
        return true; // regimes S and L are correctly rounded everywhere
    }
    let z = DoubleWord::product(a, a * 0.5).add(DoubleWord::sum(C_HI, C_LO));
    decide_with(z, EPS).is_some()
}

fn check(section: &str, expected_len: usize) -> (usize, usize) {
    let cases = entries(FIXTURE, &[section]);
    assert_eq!(cases.len(), expected_len, "{section}");
    let (mut undecided, mut mismatches) = (0, 0);
    for case in cases {
        let (x, y) = (word(case, "x"), word(case, "y"));
        let got = log_norm_pdf(x);
        if !decided(x) {
            undecided += 1;
        }
        if y.is_nan() {
            assert!(got.is_nan(), "{case}");
            continue;
        }
        if got.to_bits() == y.to_bits() {
            continue;
        }
        // Decision 1's only exception: an undecided case within
        // (1/2 + 2^−50) ulp of the exact value, so within (1 + 2^−50) ulp of
        // y = RN(exact).
        mismatches += 1;
        assert!(!decided(x), "{case}: got {got:e}, a decided case");
        let bound = ulp(y) * (1.0 + f64::from_bits(0x3cd0_0000_0000_0000));
        assert!(
            (got - y).abs() <= bound,
            "{case}: got {got:e}, beyond the bound"
        );
    }
    std::eprintln!(
        "log_norm_pdf {section}: {expected_len} cases, {undecided} undecided by the rounding test, \
         {mismatches} not correctly rounded"
    );
    (undecided, mismatches)
}

#[test]
fn hand_picked_cases_are_correctly_rounded() {
    let (_, mismatches) = check("hand", 119);
    assert_eq!(mismatches, 0);
}

#[test]
fn random_cases_are_correctly_rounded_where_decided() {
    check("random", 6424);
}

#[test]
fn the_result_depends_on_the_magnitude_only() {
    for section in ["hand", "random"] {
        for case in entries(FIXTURE, &[section]) {
            let x = word(case, "x");
            let (p, n) = (log_norm_pdf(x), log_norm_pdf(-x));
            assert!(
                p.to_bits() == n.to_bits() || (p.is_nan() && n.is_nan()),
                "{case}"
            );
        }
    }
}

#[test]
fn every_finite_result_is_at_most_minus_c() {
    for section in ["hand", "random"] {
        for case in entries(FIXTURE, &[section]) {
            let got = log_norm_pdf(word(case, "x"));
            assert!(got.is_nan() || got <= -C_HI, "{case}");
        }
    }
}

/// Local cost, for docs/log_norm_pdf.md §5: `cargo test --release -p
/// morphiq-numerics log_norm_pdf::tests::measure_cost -- --ignored --nocapture`.
/// Not a gate.
#[test]
#[ignore = "a local measurement, not a check"]
fn measure_cost() {
    use crate::random::{SplitMix64, unit_closed_open};
    use std::time::Instant;
    let mut stream = SplitMix64::new(0x1095_C0D7);
    let xs: Vec<f64> = (0..1 << 16)
        .map(|_| 16.0 * unit_closed_open(stream.next_u64()) - 8.0)
        .collect();
    let mut sink = 0.0;
    let start = Instant::now();
    for _ in 0..64 {
        for &x in &xs {
            sink += log_norm_pdf(core::hint::black_box(x));
        }
    }
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let ns = start.elapsed().as_nanos() as f64 / (64.0 * xs.len() as f64);
    std::eprintln!("log_norm_pdf, x in [-8, 8]: {ns:.1} ns per call ({sink:e})");
}
