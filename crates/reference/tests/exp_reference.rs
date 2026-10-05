//! The exp reference fixture's own consistency, independent of the oracle
//! that wrote it (`generators/exp_reference.py`).
//!
//! `exp` is increasing and rounding to nearest preserves order, so sorted by
//! argument the reference results never decrease. Each derived threshold sits
//! next to its neighbour, one encoding away, with results on either side of
//! the boundary it names.

use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/exp.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn cases() -> Vec<(String, f64, f64)> {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    fixture["cases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            (
                c["kind"].as_str().unwrap().to_owned(),
                word(&c["x"]),
                word(&c["exp"]),
            )
        })
        .collect()
}

#[test]
fn reference_results_never_decrease_as_the_argument_grows() {
    let mut finite: Vec<(f64, f64)> = cases()
        .into_iter()
        .filter(|(_, x, _)| !x.is_nan())
        .map(|(_, x, y)| (x, y))
        .collect();
    finite.sort_by(|a, b| a.0.total_cmp(&b.0));
    for pair in finite.windows(2) {
        let ((x0, y0), (x1, y1)) = (pair[0], pair[1]);
        assert!(
            y0 <= y1,
            "exp({x0:e}) = {y0:e} exceeds exp({x1:e}) = {y1:e}"
        );
    }
}

#[test]
fn every_threshold_sits_next_to_its_neighbour_across_its_boundary() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let t = |name: &str| word(&fixture["thresholds"][name]);
    let next = |x: f64| f64::from_bits(x.to_bits() + 1);
    let exp_of = |x: f64| {
        cases()
            .into_iter()
            .find(|(_, a, _)| a.to_bits() == x.to_bits())
            .map(|(_, _, y)| y)
            .unwrap()
    };
    let (finite, overflow) = (
        t("largest x with a finite result"),
        t("least x overflowing"),
    );
    assert_eq!(next(finite).to_bits(), overflow.to_bits());
    assert!(exp_of(finite).is_finite() && exp_of(overflow) == f64::INFINITY);

    // Negative arguments: the more negative one has the larger encoding.
    let (nonzero, zero) = (
        t("least x with a nonzero result"),
        t("largest x rounding to 0"),
    );
    assert_eq!(next(nonzero).to_bits(), zero.to_bits());
    assert!(exp_of(nonzero) > 0.0 && exp_of(zero) == 0.0);

    let (normal, subnormal) = (
        t("least x with a normal result"),
        t("largest x with a subnormal result"),
    );
    assert_eq!(next(normal).to_bits(), subnormal.to_bits());
    assert!(exp_of(normal) >= f64::MIN_POSITIVE && exp_of(subnormal) < f64::MIN_POSITIVE);

    let (one, above) = (
        t("largest positive x rounding to 1"),
        t("least positive x above 1"),
    );
    assert_eq!(next(one).to_bits(), above.to_bits());
    assert!(exp_of(one) == 1.0 && exp_of(above) > 1.0);
    assert_eq!(above, f64::from_bits((1023 - 53) << 52)); // 2^-53

    let (one, below) = (
        t("least negative x rounding to 1"),
        t("largest negative x below 1"),
    );
    assert_eq!(next(one).to_bits(), below.to_bits());
    assert!(exp_of(one) == 1.0 && exp_of(below) < 1.0);
    assert_eq!(one, -f64::from_bits((1023 - 54) << 52)); // -2^-54
}

#[test]
fn the_published_worst_cases_are_all_present() {
    let worst = cases()
        .into_iter()
        .filter(|(kind, _, _)| kind == "worst case")
        .count();
    assert_eq!(worst, 7, "Lefèvre and Muller's Table 4 lists seven");
}
