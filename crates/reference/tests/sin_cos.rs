//! `sin`, `cos` and `sincos` against their reference fixture
//! (`generators/sin_cos_reference.py`), bit for bit: [LM] Tables 8 and 10's
//! worst cases, the small-argument thresholds, arguments near multiples of
//! π/2, special values and random arguments in every binade
//! (docs/sin_cos.md). Outside [LM]'s ranges a mismatch would be an argument
//! inside the stated window, to be reported, not waived.

use morphiq_numerics::elementary::{cos, sin, sincos};
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/sin_cos.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn check(function: &str, f: fn(f64) -> f64) {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
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
fn sin_is_correctly_rounded_on_every_reference_case() {
    check("sin", sin);
}

#[test]
fn cos_is_correctly_rounded_on_every_reference_case() {
    check("cos", cos);
}

#[test]
fn sincos_returns_exactly_sin_and_cos() {
    check("sin", |x| sincos(x).0);
    check("cos", |x| sincos(x).1);
}
