//! `atan2` against its reference fixture (`generators/atan2_reference.py`), bit
//! for bit: the 40 hardest pairs of CORE-MATH's worst-case list, every pair of
//! special values, the subnormal midpoints, the structure's boundaries and
//! random pairs (docs/atan2.md §7). The fixture holds the correctly rounded
//! values, so a mismatch is a wrong rounding to be reported, not waived.

use morphiq_numerics::elementary::atan2;
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/atan2.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

#[test]
fn atan2_is_correctly_rounded_on_every_reference_case() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["atan2"].as_array().unwrap();
    let mut wrong = Vec::new();
    for case in cases {
        let (y, x, expected) = (word(&case["y"]), word(&case["x"]), word(&case["atan2"]));
        let got = atan2(y, x);
        let agrees = if expected.is_nan() {
            got.is_nan()
        } else {
            got.to_bits() == expected.to_bits()
        };
        if !agrees {
            wrong.push(format!(
                "{}: atan2({y:e}, {x:e}) = {got:e}, expected {expected:e}",
                case["kind"].as_str().unwrap()
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} cases wrong:\n{}",
        wrong.len(),
        cases.len(),
        wrong
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
