//! Public slices against independent generated fixtures and scalar bits.
use morphiq_numerics::elementary::{cos, cos_slice, sin, sin_slice, sincos_slice, tan, tan_slice};
use serde_json::Value;

fn word(value: &Value) -> f64 {
    f64::from_bits(u64::from_str_radix(value.as_str().unwrap(), 16).unwrap())
}

fn check(name: &str, fixture: &str, scalar: fn(f64) -> f64, slice: fn(&[f64], &mut [f64])) {
    let fixture: Value = serde_json::from_str(fixture).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let xs: Vec<_> = cases.iter().map(|case| word(&case["x"])).collect();
    for len in (0..=17).chain([xs.len()]) {
        for offset in 0..=usize::from(len <= 17) * 7 {
            let input = &xs[offset..offset + len];
            let mut out = vec![f64::NAN; len];
            slice(input, &mut out);
            for (i, (&x, got)) in input.iter().zip(out).enumerate() {
                let expected = word(&cases[offset + i][name]);
                assert!(
                    if expected.is_nan() {
                        got.is_nan()
                    } else {
                        got.to_bits() == expected.to_bits()
                    },
                    "{name}({x:e})"
                );
                assert_eq!(got.to_bits(), scalar(x).to_bits(), "{name}({x:e})");
            }
        }
    }
}

#[test]
fn trig_slices_match_independent_oracles() {
    let fixture = include_str!("../fixtures/sin_cos.json");
    check("sin", fixture, sin, sin_slice);
    check("cos", fixture, cos, cos_slice);
    check("tan", include_str!("../fixtures/tan.json"), tan, tan_slice);
}

#[test]
fn paired_slices_match_both_independent_oracles() {
    let fixture: Value = serde_json::from_str(include_str!("../fixtures/sin_cos.json")).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    let xs: Vec<_> = cases.iter().map(|case| word(&case["x"])).collect();
    let (mut sine, mut cosine) = (vec![0.0; xs.len()], vec![0.0; xs.len()]);
    sincos_slice(&xs, &mut sine, &mut cosine);
    for ((case, s), c) in cases.iter().zip(sine).zip(cosine) {
        for (name, got) in [("sin", s), ("cos", c)] {
            let expected = word(&case[name]);
            assert!(if expected.is_nan() {
                got.is_nan()
            } else {
                got.to_bits() == expected.to_bits()
            });
        }
    }
}

#[test]
// Inspecting output after a panic requires unwinding; aborting targets trap.
#[cfg(panic = "unwind")]
fn trig_slices_reject_shapes_before_writing() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    for slice in [sin_slice, cos_slice, tan_slice] {
        let mut out = [42.0];
        assert!(catch_unwind(AssertUnwindSafe(|| slice(&[0.5, 1.0], &mut out))).is_err());
        assert_eq!(out, [42.0]);
    }
    for (sine_len, cosine_len) in [(1, 2), (2, 1)] {
        let (mut s, mut c) = (vec![42.0; sine_len], vec![43.0; cosine_len]);
        assert!(
            catch_unwind(AssertUnwindSafe(|| sincos_slice(
                &[0.5, 1.0],
                &mut s,
                &mut c
            )))
            .is_err()
        );
        assert!(s.iter().all(|&x| x == 42.0) && c.iter().all(|&x| x == 43.0));
    }
}
