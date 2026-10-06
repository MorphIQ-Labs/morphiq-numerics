//! `log2` and `log10` against their reference fixture
//! (`generators/log2_log10_reference.py`), bit for bit: [LM] Table 7's worst
//! cases, exact powers, special values and random arguments (docs/log2.md).
//! The fixture holds correctly rounded values, so a `log10` mismatch would be
//! an argument inside its stated window, to be reported, not waived.

use morphiq_numerics::elementary::{log2, log10};
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/log2_log10.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn check(function: &str, f: fn(f64) -> f64) {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture[function].as_array().unwrap();
    let mut wrong = Vec::new();
    for case in cases {
        let (x, expected) = (word(&case["x"]), word(&case[function]));
        let got = f(x);
        let agrees = if expected.is_nan() {
            got.is_nan()
        } else {
            got.to_bits() == expected.to_bits()
        };
        if !agrees {
            wrong.push(format!(
                "{}: {function}({x:e}) = {got:e}, expected {expected:e}",
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
fn log2_is_correctly_rounded_on_every_reference_case() {
    check("log2", log2);
}

#[test]
fn log10_is_correctly_rounded_on_every_reference_case() {
    check("log10", log10);
}
