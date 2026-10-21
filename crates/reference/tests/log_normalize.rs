//! Returned error radii checked using exact integer arithmetic against
//! independent mpmath 1.4.1 interval endpoints. See log_normalize_reference.py.

use morphiq_numerics::log_space::normalize_log_weights;
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn values(row: &Value, name: &str) -> Vec<f64> {
    row[name]
        .as_str()
        .unwrap()
        .split_whitespace()
        .map(|s| f64::from_bits(u64::from_str_radix(s, 16).unwrap()))
        .collect()
}

#[test]
fn returned_radius_encloses_true_values_without_test_rounding() {
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/log_normalize.json")).unwrap();
    for row in fixture["cases"].as_array().unwrap() {
        let x = values(row, "x");
        let lo = values(row, "truth_lo");
        let hi = values(row, "truth_hi");
        let mut out = vec![0.0; x.len()];
        let result = normalize_log_weights(&x, &mut out).unwrap();
        let half = Exact::power_of_two(-1);
        let radius = &Exact::of(result.max_absolute_error()) * &half;
        for (i, &value) in out.iter().enumerate() {
            if value == f64::NEG_INFINITY {
                continue;
            }
            // Truth endpoints were divided by 2 before outward rounding so
            // real logs slightly below -MAX retain finite reference endpoints.
            let center = &Exact::of(value) * &half;
            assert!(
                &center - &radius <= Exact::of(lo[i]),
                "{}[{i}]: lower radius",
                row["label"]
            );
            assert!(
                &center + &radius >= Exact::of(hi[i]),
                "{}[{i}]: upper radius",
                row["label"]
            );
        }
    }
}
