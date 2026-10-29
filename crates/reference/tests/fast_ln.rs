//! Absolute log-unit bound, including independent high/low oracle uncertainty.
use morphiq_numerics::fast::elementary::{ln, ln_slice};
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn within_bound(actual: f64, high: f64, low: f64) -> bool {
    if !actual.is_finite() {
        return false;
    }
    let high = Exact::of(high);
    let reference = &high + &Exact::of(low);
    let uncertainty = &(&high.abs() * &Exact::power_of_two(-104)) + &Exact::power_of_two(-1074);
    let error_upper = &(&Exact::of(actual) - &reference).abs() + &uncertainty;
    let magnitude_lower = &reference.abs() - &uncertainty;
    let cap_lower = &(&magnitude_lower * &Exact::power_of_two(-53)) + &Exact::power_of_two(-65);
    error_upper <= cap_lower
}

#[test]
fn scalar_and_slice_meet_log_unit_budget_on_independent_witnesses() {
    let fixture: Value = serde_json::from_str(include_str!("../fixtures/fast_ln.json")).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let input: Vec<f64> = cases.iter().map(|c| word(&c["x"])).collect();
    let mut output = vec![0.0; input.len()];
    ln_slice(&input, &mut output);
    for ((case, &x), &actual) in cases.iter().zip(&input).zip(&output) {
        assert_eq!(actual.to_bits(), ln(x).to_bits(), "slice/scalar at {x:?}");
        assert!(
            within_bound(actual, word(&case["high"]), word(&case["low"])),
            "ln({x:?})={actual:?} exceeds the log-unit budget"
        );
        if x == 1.0 {
            assert_eq!(actual.to_bits(), 0);
        } else {
            assert_eq!(actual.is_sign_negative(), x < 1.0);
        }
    }
}

#[test]
fn oracle_comparison_rejects_out_of_contract_outputs() {
    for reference in [1.0_f64, -1.0, 0.0] {
        assert!(within_bound(reference, reference, 0.0));
        assert!(!within_bound(
            reference + f64::from_bits(0x3cd0_0000_0000_0000),
            reference,
            0.0
        ));
    }
    assert!(!within_bound(f64::NAN, 1.0, 0.0));
    assert!(!within_bound(f64::INFINITY, 1.0, 0.0));
}
