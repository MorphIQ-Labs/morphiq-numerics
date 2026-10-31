//! `bivariate_norm_cdf` against its reference fixture
//! (`generators/bivariate_normal_reference.py`): every case within the
//! contract's absolute bound, every case at or above the relative floor within
//! the relative bound, and every reported bound at least the observed error.
//! The expected values are 36-digit mpmath integrals of Plackett's identity at
//! two precisions, never a rearrangement of the function under test
//! (docs/bivariate_normal.md section 7).

use morphiq_numerics::bivariate_normal::{
    ABSOLUTE_ERROR_BOUND, BivariateNormal, absolute_error_bound, bivariate_norm_cdf,
    bivariate_norm_cdf_bounded,
};
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/bivariate_normal.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

struct Case {
    kind: String,
    x: f64,
    y: f64,
    rho: f64,
    expected: f64,
}

fn cases() -> Vec<Case> {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    fixture["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|case| Case {
            kind: case["kind"].as_str().unwrap_or("grid").to_string(),
            x: word(&case["h"]),
            y: word(&case["k"]),
            rho: word(&case["rho"]),
            expected: case["value"].as_str().unwrap().parse().unwrap(),
        })
        .collect()
}

#[test]
fn every_case_is_within_the_absolute_bound_and_its_reported_bound() {
    let mut worst = (0.0_f64, String::new());
    let mut wrong = Vec::new();
    for case in cases() {
        let got = bivariate_norm_cdf(case.x, case.y, case.rho);
        let bounded = bivariate_norm_cdf_bounded(case.x, case.y, case.rho);
        assert_eq!(got.to_bits(), bounded.value.to_bits());
        let error = (got - case.expected).abs();
        let label = format!(
            "{}: P({:e}, {:e}; {:e}) = {got:e}, expected {:e}, error {error:e}",
            case.kind, case.x, case.y, case.rho, case.expected
        );
        if error > worst.0 {
            worst = (error, label.clone());
        }
        if error > bounded.error || bounded.error != absolute_error_bound(case.rho) {
            wrong.push(label);
        }
    }
    println!("worst absolute error {:e}: {}", worst.0, worst.1);
    assert!(
        wrong.is_empty(),
        "{} cases wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

#[test]
fn the_reusable_evaluator_returns_the_one_shot_bits() {
    for case in cases() {
        let table = BivariateNormal::new(case.rho).unwrap();
        assert_eq!(
            table.cdf(case.x, case.y).to_bits(),
            bivariate_norm_cdf(case.x, case.y, case.rho).to_bits()
        );
        assert_eq!(
            table.cdf(case.y, case.x).to_bits(),
            table.cdf(case.x, case.y).to_bits(),
            "symmetric in the arguments"
        );
    }
}

/// The deep-tail negative-correlation corner of MorphIQ Risk's issue #380 is a
/// required case set. The value is returned to the absolute bound, and where
/// the value is smaller than that bound the reported error is not smaller than
/// the value: the result refuses to look relative (docs/bivariate_normal.md
/// section 8).
#[test]
fn hard_cases_are_bounded_absolutely_and_refuse_relative_use() {
    let hard: Vec<Case> = cases()
        .into_iter()
        .filter(|case| case.kind == "hard")
        .collect();
    assert!(
        hard.len() >= 8,
        "the corner's required cases are in the fixture"
    );
    for case in hard {
        let bounded = bivariate_norm_cdf_bounded(case.x, case.y, case.rho);
        let error = (bounded.value - case.expected).abs();
        assert!(
            error <= ABSOLUTE_ERROR_BOUND,
            "{case:?}: error {error:e}",
            case = (case.x, case.y, case.rho)
        );
        if case.expected < ABSOLUTE_ERROR_BOUND {
            assert!(
                bounded.error >= case.expected,
                "{:?}: reported bound {:e} is smaller than the value {:e}",
                (case.x, case.y, case.rho),
                bounded.error,
                case.expected
            );
        }
    }
}

/// A result for a positive correlation that is a probability of at least
/// `TAIL_FLOOR` in a lower tail is correct in relative terms to
/// `TAIL_RELATIVE` (for a negative correlation the integral is subtracted from
/// the product and the result cancels, which the contract refuses for relative
/// use: section 8): the node count of the rule,
/// which the canonical Genz implementation's tails also follow, sets the
/// truncation there, and a shorter rule is orders of magnitude off on these
/// cases (docs/bivariate_normal.md section 4). The bound is twice the
/// measured worst case (`4.7e-9` at `P(-8, -8; 0.1)`, where Genz's rule has the
/// same 6 nodes); it is not a contract of the function, whose published bound
/// is absolute.
const TAIL_FLOOR: f64 = 1e-30;
const TAIL_RELATIVE: f64 = 1e-8;

#[test]
fn lower_tail_results_keep_their_relative_accuracy() {
    let mut worst = (0.0_f64, String::new());
    let mut checked = 0;
    for case in cases().into_iter().filter(|case| case.kind == "tail") {
        if case.expected < TAIL_FLOOR || case.rho < 0.0 {
            continue;
        }
        checked += 1;
        let got = bivariate_norm_cdf(case.x, case.y, case.rho);
        let relative = ((got - case.expected) / case.expected).abs();
        if relative > worst.0 {
            worst = (
                relative,
                format!("P({:e}, {:e}; {:e})", case.x, case.y, case.rho),
            );
        }
    }
    println!(
        "worst tail relative error {:e} over {checked}: {}",
        worst.0, worst.1
    );
    assert!(
        checked >= 50,
        "the tail cases are in the fixture: {checked}"
    );
    assert!(
        worst.0 <= TAIL_RELATIVE,
        "relative error {:e} at {}",
        worst.0,
        worst.1
    );
}

/// High correlation with both thresholds far below zero, `hk = h k` from 100
/// to 1400: the correlation integral is most of the result there and the high
/// branch computes it (docs/bivariate_normal.md section 7.1). Measured, not a
/// contract: the cancellation of `Phi(-max) - J / 2 pi` grows with depth, and
/// faster as `rho` falls toward the split. The bounds are about 8 times the
/// measured worst: `DEEP_NEAR` for probabilities of at least `1e-150` (`6.3e-11`
/// at `P(-25, -25; 0.93)`) and `DEEP_FAR` for the rest at `rho >= 0.97`.
const DEEP_NEAR: f64 = 5e-10;
const DEEP_FAR: f64 = 1e-9;

#[test]
fn results_below_the_integral_cutoff_never_fall_under_the_truth() {
    // Past `phi = 700` the correlation integral is dropped, so a result that
    // small is the leading term alone: no relative accuracy is claimed, but the
    // omitted integral is nonnegative, so the value can only err high.
    let mut checked = 0;
    for case in cases().into_iter().filter(|case| case.kind == "deep") {
        if case.expected >= 1e-300 || case.expected == 0.0 || case.rho <= 0.0 {
            continue;
        }
        checked += 1;
        let got = bivariate_norm_cdf(case.x, case.y, case.rho);
        assert!(
            got >= case.expected * (1.0 - 1e-12),
            "P({:e}, {:e}; {:e}) = {got:e} fell under {:e}",
            case.x,
            case.y,
            case.rho,
            case.expected
        );
    }
    assert!(
        checked >= 5,
        "rows below 1e-300 are in the fixture: {checked}"
    );
}

#[test]
fn deep_tails_at_high_correlation_keep_their_relative_accuracy() {
    let mut worst = (0.0_f64, String::new());
    let mut checked = 0;
    for case in cases().into_iter().filter(|case| case.kind == "deep") {
        // Below `1e-300` the result is subnormal or nearly so.
        if case.expected < 1e-300 {
            continue;
        }
        let bound = if case.expected >= 1e-150 {
            DEEP_NEAR
        } else if case.rho >= 0.97 {
            DEEP_FAR
        } else {
            continue;
        };
        checked += 1;
        let got = bivariate_norm_cdf(case.x, case.y, case.rho);
        let relative = ((got - case.expected) / case.expected).abs();
        assert!(
            relative <= bound,
            "P({:e}, {:e}; {:e}) = {got:e}, expected {:e}: relative error {relative:e}",
            case.x,
            case.y,
            case.rho,
            case.expected
        );
        if relative > worst.0 {
            worst = (
                relative,
                format!("P({:e}, {:e}; {:e})", case.x, case.y, case.rho),
            );
        }
    }
    println!(
        "worst deep-tail relative error {:e} over {checked}: {}",
        worst.0, worst.1
    );
    assert!(
        checked >= 50,
        "the deep cases are in the fixture: {checked}"
    );
}
