//! The ln and ln_1p reference fixture's own consistency, independent of the
//! oracle that wrote it (`generators/ln_reference.py`).
//!
//! Both functions are increasing and rounding to nearest preserves order, so
//! sorted by argument the reference results never decrease. `ln(x)` is negative
//! exactly when `x < 1`, and `ln_1p(x)` has the sign of `x`, signed zeros
//! included.

use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/ln.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn cases(function: &str) -> Vec<(String, f64, f64)> {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    fixture[function]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            (
                c["kind"].as_str().unwrap().to_owned(),
                word(&c["x"]),
                word(&c[function]),
            )
        })
        .collect()
}

fn assert_never_decreasing(function: &str, domain_start: f64) {
    let mut points: Vec<(f64, f64)> = cases(function)
        .into_iter()
        .filter(|(_, x, _)| *x >= domain_start)
        .map(|(_, x, y)| (x, y))
        .collect();
    points.sort_by(|a, b| a.0.total_cmp(&b.0));
    for pair in points.windows(2) {
        let ((x0, y0), (x1, y1)) = (pair[0], pair[1]);
        assert!(
            y0 <= y1,
            "{function}({x0:e}) = {y0:e} exceeds {function}({x1:e}) = {y1:e}"
        );
    }
}

#[test]
fn reference_results_never_decrease_as_the_argument_grows() {
    assert_never_decreasing("ln", 0.0);
    assert_never_decreasing("ln_1p", -1.0);
}

#[test]
fn ln_is_negative_exactly_below_one() {
    for (_, x, y) in cases("ln") {
        if x > 0.0 && x.is_finite() {
            assert_eq!(y < 0.0, x < 1.0, "ln({x:e}) = {y:e}");
            assert_eq!(y == 0.0, x == 1.0, "ln({x:e}) = {y:e}");
        }
    }
}

#[test]
fn ln_1p_has_the_sign_of_its_argument() {
    for (_, x, y) in cases("ln_1p") {
        if x > -1.0 && x.is_finite() {
            assert_eq!(
                y.is_sign_negative(),
                x.is_sign_negative(),
                "ln_1p({x:e}) = {y:e}"
            );
        }
    }
}

#[test]
fn special_values_follow_ieee_754() {
    let find = |function: &str, x: f64| {
        cases(function)
            .into_iter()
            .find(|(_, a, _)| a.to_bits() == x.to_bits())
            .map(|(_, _, y)| y)
            .unwrap()
    };
    assert!(find("ln", -1.0).is_nan() && find("ln", f64::NEG_INFINITY).is_nan());
    assert_eq!(find("ln", 0.0), f64::NEG_INFINITY);
    assert_eq!(find("ln", -0.0), f64::NEG_INFINITY);
    assert_eq!(find("ln", 1.0).to_bits(), 0.0_f64.to_bits());
    assert_eq!(find("ln", f64::INFINITY), f64::INFINITY);
    assert!(find("ln_1p", -2.0).is_nan());
    assert_eq!(find("ln_1p", -1.0), f64::NEG_INFINITY);
    assert_eq!(find("ln_1p", 0.0).to_bits(), 0.0_f64.to_bits());
    assert_eq!(find("ln_1p", -0.0).to_bits(), (-0.0_f64).to_bits());
    assert_eq!(find("ln_1p", f64::INFINITY), f64::INFINITY);
}

#[test]
fn the_published_worst_cases_are_all_present() {
    let worst = cases("ln")
        .into_iter()
        .filter(|(kind, _, _)| kind == "worst case")
        .count();
    assert_eq!(worst, 5, "Lefèvre and Muller's Table 5 lists five");
}
