//! The explicit fast domains against retained independent interval references.
use morphiq_numerics::fast::{elementary, normal};
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn exp_within_bound(actual: f64, row: &Value) -> bool {
    if !actual.is_finite() {
        return false;
    }
    let digits = row["fast_m"].as_str().unwrap();
    assert_eq!(digits.len(), 48, "expected a 192-bit interval reference");
    let mut mantissa = Exact::integer(0);
    for digit in digits.chars() {
        mantissa = &(&mantissa * &Exact::integer(16))
            + &Exact::integer(i64::from(digit.to_digit(16).unwrap()));
    }
    let exponent = row["fast_e"].as_i64().unwrap();
    let reference = &mantissa * &Exact::power_of_two(exponent);
    // The independent interval oracle guarantees |reference-y| <= 2^-192*y.
    // Its 192-bit mantissa and 2^-192 < 1/2 imply y < 2^(exponent+193),
    // so 2^(exponent+1) conservatively encloses the reference uncertainty.
    let uncertainty = Exact::power_of_two(exponent + 1);
    let error_upper = &(&Exact::of(actual) - &reference).abs() + &uncertainty;
    let cap_lower = &(&reference - &uncertainty) * &Exact::power_of_two(-51);
    error_upper <= cap_lower
}

#[test]
fn precise_exp_reference_resolves_binary64_oracle_uncertainty() {
    let data: Value = serde_json::from_str(include_str!("../fixtures/exp.json")).unwrap();
    let row = data["cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["x"] == "c0841f4e25e67aaa")
        .unwrap();
    // CI's witness: actual relative error is 3.378e-16, below 2^-51, although
    // distance to the rounded binary64 reference plus half an ULP exceeds it.
    assert!(exp_within_bound(f64::from_bits(0x05e0_5523_445b_e6d0), row));
    assert!(!exp_within_bound(
        f64::from_bits(0x05e0_5523_445b_e6d2),
        row
    ));
}

#[test]
fn accelerated_domains_meet_their_bound_including_reference_rounding() {
    let small = f64::from_bits(0x3de0_0000_0000_0000);
    type Scalar = fn(f64) -> f64;
    for (name, fixture, key, function) in [
        (
            "exp",
            include_str!("../fixtures/exp.json"),
            "exp",
            elementary::exp as Scalar,
        ),
        (
            "erfcx",
            include_str!("../fixtures/erfcx.json"),
            "y",
            normal::erfcx,
        ),
        (
            "cdf",
            include_str!("../fixtures/normal.json"),
            "cdf",
            normal::norm_cdf,
        ),
    ] {
        let data: Value = serde_json::from_str(fixture).unwrap();
        let mut observed = 0;
        for row in data["cases"].as_array().unwrap() {
            let x = word(&row["x"]);
            let accelerated = match name {
                "exp" => x.abs() < 704.0,
                "erfcx" => (-0.5..16.0).contains(&x) && x.abs() >= small,
                "cdf" => (small..=8.0).contains(&x.abs()),
                _ => unreachable!(),
            };
            if !accelerated {
                continue;
            }
            let actual = function(x);
            if name == "exp" {
                assert!(exp_within_bound(actual, row), "exp({x:?}) exceeds 2^-51");
                observed += 1;
                continue;
            }
            let reference = word(&row[key]);
            let uncertainty =
                (reference.next_up() - reference).max(reference - reference.next_down()) * 0.5;
            let error_upper = ((actual - reference).abs() + uncertainty).next_up();
            let cap_lower = if name == "cdf" {
                f64::from_bits(0x3ce0_0000_0000_0000)
            } else {
                (reference.abs().next_down() * f64::from_bits(0x3cc0_0000_0000_0000)).next_down()
            };
            assert!(
                actual.is_finite() && error_upper <= cap_lower,
                "{name}({x:?}): {error_upper:e} > {cap_lower:e}"
            );
            observed += 1;
        }
        assert!(
            observed > 100,
            "empty or unexpectedly small {name} reference population"
        );
    }
}
