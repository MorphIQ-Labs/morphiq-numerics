//! `expm1` against its reference fixture (`generators/expm1_reference.py`), bit
//! for bit: every threshold and its neighbour, special values and random
//! arguments at every scale (docs/expm1.md). The fixture holds correctly
//! rounded values, so a mismatch would be an argument inside the stated
//! window, to be reported, not waived.

use morphiq_numerics::elementary::expm1;
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/expm1.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

#[test]
fn expm1_is_correctly_rounded_on_every_reference_case() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let mut wrong = Vec::new();
    for case in cases {
        let (x, expected) = (word(&case["x"]), word(&case["expm1"]));
        let got = expm1(x);
        let agrees = if expected.is_nan() {
            got.is_nan()
        } else {
            got.to_bits() == expected.to_bits()
        };
        if !agrees {
            wrong.push(format!(
                "{}: expm1({x:e}) = {got:e}, expected {expected:e}",
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
