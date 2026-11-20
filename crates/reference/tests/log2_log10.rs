//! `log2` and `log10` against their reference fixture
//! (`generators/log2_log10_reference.py`), bit for bit: [LM] Table 7's worst
//! cases, exact powers, special values and random arguments (docs/log2.md).
//! The fixture holds correctly rounded values, so a `log10` mismatch would be
//! an argument inside its stated window, to be reported, not waived.

use morphiq_numerics::elementary::{log2, log2_slice, log10, log10_slice};
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

fn check_slice(name: &str, scalar: fn(f64) -> f64, batched: fn(&[f64], &mut [f64])) {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture[name].as_array().unwrap();
    let xs: Vec<f64> = cases.iter().map(|case| word(&case["x"])).collect();
    for len in (0..=17).chain([xs.len()]) {
        for offset in 0..=usize::from(len <= 17) * 7 {
            let input = &xs[offset..offset + len];
            let mut out = vec![f64::NAN; len];
            batched(input, &mut out);
            for (i, (&x, &got)) in input.iter().zip(&out).enumerate() {
                let expected = word(&cases[offset + i][name]);
                assert!(if expected.is_nan() {
                    got.is_nan()
                } else {
                    got.to_bits() == expected.to_bits()
                });
                assert_eq!(got.to_bits(), scalar(x).to_bits(), "{name}({x:e})");
            }
        }
    }
}

#[test]
fn log2_slices_match_independent_fixtures_and_scalar_bits() {
    check_slice("log2", log2, log2_slice);
}

#[test]
fn log10_slices_match_independent_fixtures_and_scalar_bits() {
    check_slice("log10", log10, log10_slice);
}

#[test]
#[should_panic(expected = "log2_slice: slices of different lengths")]
fn log2_slices_reject_different_lengths() {
    log2_slice(&[1.0, 2.0], &mut [0.0]);
}

#[test]
#[should_panic(expected = "log10_slice: slices of different lengths")]
fn log10_slices_reject_different_lengths() {
    log10_slice(&[1.0, 2.0], &mut [0.0]);
}
