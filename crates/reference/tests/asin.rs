//! `asin` against its reference fixture (`generators/asin_reference.py`), bit
//! for bit: the 40 hardest arguments of CORE-MATH's worst-case list, the
//! rounding threshold and its neighbours, special values, the structure's
//! boundaries and random arguments (docs/asin.md §7). The fixture holds the
//! correctly rounded values, so a mismatch is a wrong rounding to be
//! reported, not waived.

use morphiq_numerics::elementary::asin;
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/asin.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

#[test]
fn asin_is_correctly_rounded_on_every_reference_case() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["asin"].as_array().unwrap();
    let mut wrong = Vec::new();
    for case in cases {
        let (x, expected) = (word(&case["x"]), word(&case["asin"]));
        let got = asin(x);
        let agrees = if expected.is_nan() {
            got.is_nan()
        } else {
            got.to_bits() == expected.to_bits()
        };
        if !agrees {
            wrong.push(format!(
                "{}: asin({x:e}) = {got:e}, expected {expected:e}",
                case["kind"].as_str().unwrap()
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} cases wrong:\n{}",
        wrong.len(),
        cases.len(),
        wrong.join("\n")
    );
}

#[test]
fn asin_rounds_to_the_argument_below_the_fixture_threshold() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let threshold = word(&fixture["threshold"]);
    assert_eq!(asin(threshold.next_down()), threshold.next_down());
    assert!(asin(threshold) > threshold);
}
