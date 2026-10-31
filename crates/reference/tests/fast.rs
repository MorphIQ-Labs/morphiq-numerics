//! Explicit fast contracts against independent high/low oracle intervals.
use morphiq_numerics::fast::{elementary, normal};
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn within_bound(actual: f64, high: f64, low: f64, relative: bool, exponent: i64) -> bool {
    if !actual.is_finite() {
        return false;
    }
    let high = Exact::of(high);
    let reference = &high + &Exact::of(low);
    // The generator independently encloses both precision observations in this
    // interval. Exact integer arithmetic keeps oracle uncertainty and the
    // public error budget separate, including subnormal low words.
    let uncertainty = &(&high.abs() * &Exact::power_of_two(-104)) + &Exact::power_of_two(-1074);
    if reference <= uncertainty {
        return false;
    }
    let error_upper = &(&Exact::of(actual) - &reference).abs() + &uncertainty;
    let cap_lower = if relative {
        &(&reference - &uncertainty) * &Exact::power_of_two(exponent)
    } else {
        Exact::power_of_two(exponent)
    };
    error_upper <= cap_lower
}

#[test]
fn accelerated_domains_meet_their_bound_including_reference_uncertainty() {
    let data: Value = serde_json::from_str(include_str!("../fixtures/fast.json")).unwrap();
    let mut observed = [0; 3];
    for row in data["cases"].as_array().unwrap() {
        let name = row["primitive"].as_str().unwrap();
        let x = word(&row["x"]);
        let (index, actual, relative, exponent) = match name {
            "exp" => (0, elementary::exp(x), true, -38),
            "erfcx" => (1, normal::erfcx(x), true, -51),
            "cdf" => (2, normal::norm_cdf(x), false, -49),
            _ => unreachable!("unknown fixture primitive"),
        };
        assert!(
            within_bound(
                actual,
                word(&row["high"]),
                word(&row["low"]),
                relative,
                exponent
            ),
            "{name}({x:?}): {actual:?} exceeds the public bound including oracle uncertainty"
        );
        observed[index] += 1;
    }
    assert!(observed.iter().all(|&n| n > 100), "empty oracle population");
}

#[test]
fn oracle_interval_rejects_results_outside_the_public_budget() {
    let ulp = f64::from_bits(0x3cb0_0000_0000_0000);
    for (relative, exponent, inside, outside) in [
        (true, -38, 8192.0 * ulp, 32768.0 * ulp),
        (true, -51, ulp, 4.0 * ulp),
        (false, -49, ulp, 16.0 * ulp),
    ] {
        assert!(within_bound(1.0 + inside, 1.0, 0.0, relative, exponent));
        assert!(!within_bound(1.0 + outside, 1.0, 0.0, relative, exponent));
        assert!(!within_bound(f64::INFINITY, 1.0, 0.0, relative, exponent));
        assert!(!within_bound(f64::NAN, 1.0, 0.0, relative, exponent));
    }
}
