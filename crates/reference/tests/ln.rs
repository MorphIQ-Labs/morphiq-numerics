//! `ln` and `ln_1p` against their reference fixture
//! (`generators/ln_reference.py`), bit for bit: [LM] Table 5's worst cases,
//! special values and random arguments (docs/ln.md §9). The fixture holds the
//! correctly rounded values, so an `ln_1p` mismatch would be an argument inside
//! §7's window, to be reported, not waived.

use morphiq_numerics::elementary::{ln, ln_1p};
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/ln.json");

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
fn ln_is_correctly_rounded_on_every_reference_case() {
    check("ln", ln);
}

#[test]
fn ln_1p_is_correctly_rounded_on_every_reference_case() {
    check("ln_1p", ln_1p);
}
