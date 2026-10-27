//! The explicit fast domains against retained independent rounded references.
use morphiq_numerics::fast::{elementary, normal};
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
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
            let reference = word(&row[key]);
            let actual = function(x);
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
