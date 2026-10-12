//! `exp2` against its reference fixture (`generators/exp2_reference.py`), bit
//! for bit: [LM] Table 6's worst cases, every threshold and its neighbour,
//! integers, special values and random arguments (docs/exp2.md).

use morphiq_numerics::elementary::exp2;
use serde_json::Value;

const FIXTURE: &str = include_str!("../fixtures/exp2.json");

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

#[test]
fn exp2_is_correctly_rounded_on_every_reference_case() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let mut wrong = Vec::new();
    for case in cases {
        let (x, expected) = (word(&case["x"]), word(&case["exp2"]));
        let got = exp2(x);
        let agrees = if expected.is_nan() {
            got.is_nan()
        } else {
            got.to_bits() == expected.to_bits()
        };
        if !agrees {
            wrong.push(format!(
                "{}: exp2({x:e}) = {got:e}, expected {expected:e}",
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
fn slices_match_independent_fixture_and_preserve_scalar_bits() {
    let fixture: Value = serde_json::from_str(FIXTURE).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let xs: Vec<f64> = cases.iter().map(|c| word(&c["x"])).collect();
    for len in (0..=17).chain([xs.len()]) {
        for offset in 0..=usize::from(len <= 17) * 7 {
            let input = &xs[offset..offset + len];
            let mut out = vec![f64::NAN; len];
            morphiq_numerics::elementary::exp2_slice(input, &mut out);
            for (i, (&x, &got)) in input.iter().zip(&out).enumerate() {
                let expected = word(&cases[offset + i]["exp2"]);
                assert!(if expected.is_nan() {
                    got.is_nan()
                } else {
                    got.to_bits() == expected.to_bits()
                });
                assert_eq!(got.to_bits(), exp2(x).to_bits());
            }
        }
    }
}

#[test]
#[should_panic(expected = "exp2_slice: slices of different lengths")]
fn slices_reject_different_lengths() {
    morphiq_numerics::elementary::exp2_slice(&[1.0, 2.0], &mut [0.0]);
}
