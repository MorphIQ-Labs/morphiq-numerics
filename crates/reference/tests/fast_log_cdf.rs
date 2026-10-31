//! Mixed log-unit bound for the bounded log-CDF, including independent
//! high/low oracle uncertainty.
use morphiq_numerics::fast::normal::{log_norm_cdf, log_norm_cdf_slice};
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

/// `abs(actual - L) <= 2^-51 * abs(L) + 2^-48`, decided in exact integer
/// arithmetic with the oracle's enclosure counted against the result.
fn within_bound(actual: f64, high: f64, low: f64) -> bool {
    if !actual.is_finite() {
        return false;
    }
    let high = Exact::of(high);
    let reference = &high + &Exact::of(low);
    let uncertainty = &(&high.abs() * &Exact::power_of_two(-104)) + &Exact::power_of_two(-1074);
    let error_upper = &(&Exact::of(actual) - &reference).abs() + &uncertainty;
    let magnitude_lower = &reference.abs() - &uncertainty;
    let cap_lower = &(&magnitude_lower * &Exact::power_of_two(-51)) + &Exact::power_of_two(-48);
    error_upper <= cap_lower
}

#[test]
fn scalar_and_slice_meet_log_unit_budget_on_independent_witnesses() {
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/fast_log_cdf.json")).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let input: Vec<f64> = cases.iter().map(|c| word(&c["x"])).collect();
    let mut output = vec![0.0; input.len()];
    log_norm_cdf_slice(&input, &mut output);
    let mut negative = 0;
    let mut positive = 0;
    for ((case, &x), &actual) in cases.iter().zip(&input).zip(&output) {
        assert_eq!(
            actual.to_bits(),
            log_norm_cdf(x).to_bits(),
            "slice/scalar at {x:?}"
        );
        assert!(
            within_bound(actual, word(&case["high"]), word(&case["low"])),
            "log_norm_cdf({x:?})={actual:?} exceeds the log-unit budget"
        );
        assert!(actual < 0.0 && actual.is_normal(), "{x:?} -> {actual:?}");
        if x < 0.0 {
            negative += 1;
        } else {
            positive += 1;
        }
    }
    assert!(
        negative > 1000 && positive > 1000,
        "both accelerated branches need witnesses"
    );
}

#[test]
fn oracle_comparison_rejects_out_of_contract_outputs() {
    let reference = -1.5_f64;
    assert!(within_bound(reference, reference, 0.0));
    assert!(within_bound(
        reference + f64::from_bits(0x3cf0_0000_0000_0000),
        reference,
        0.0
    ));
    assert!(!within_bound(
        reference + 2.0 * f64::from_bits(0x3cf0_0000_0000_0000),
        reference,
        0.0
    ));
    assert!(!within_bound(f64::NAN, reference, 0.0));
    assert!(!within_bound(f64::NEG_INFINITY, reference, 0.0));
}
