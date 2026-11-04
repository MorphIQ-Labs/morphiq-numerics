//! Bounded pairs against the independent interval-oracle strong-pair fixture.
use morphiq_numerics::fast::random::{ABSOLUTE_ERROR_BOUND, normal_pair, normal_pair_slice};
use morphiq_numerics::random::SplitMix64;
use serde_json::Value;

fn word(value: &Value) -> u64 {
    u64::from_str_radix(value.as_str().unwrap(), 16).unwrap()
}

fn bits(pair: (f64, f64)) -> (u64, u64) {
    (pair.0.to_bits(), pair.1.to_bits())
}

#[test]
fn every_independent_reference_pair_meets_the_absolute_bound_and_zero_signs() {
    let fixture: Value = serde_json::from_str(include_str!("../fixtures/box_muller.json")).unwrap();
    let mut rows: Vec<&Value> = fixture["edges"].as_array().unwrap().iter().collect();
    for family in ["splitmix64", "xoshiro256pp"] {
        for stream in fixture[family].as_object().unwrap().values() {
            rows.extend(stream.as_array().unwrap());
        }
    }
    assert_eq!(rows.len(), 3168);
    for row in rows {
        let (w1, w2) = (word(&row["w1"]), word(&row["w2"]));
        let got = normal_pair(w1, w2);
        let expected = (
            f64::from_bits(word(&row["z0"])),
            f64::from_bits(word(&row["z1"])),
        );
        for (actual, reference) in [(got.0, expected.0), (got.1, expected.1)] {
            assert!(actual.is_finite());
            assert!(
                (actual - reference).abs() <= ABSOLUTE_ERROR_BOUND,
                "words {w1:016x} {w2:016x}: {actual:e} vs {reference:e}"
            );
            if reference == 0.0 {
                assert_eq!(actual.to_bits(), reference.to_bits());
            }
        }
    }
}

#[test]
fn slice_lengths_and_remainders_preserve_every_scalar_bit() {
    let mut stream = SplitMix64::new(282);
    let first: Vec<u64> = (0..4096).map(|_| stream.next_u64()).collect();
    let second: Vec<u64> = (0..4096).map(|_| stream.next_u64()).collect();
    for n in (0..=33).chain([63, 64, 65, 1023, 4096]) {
        let mut out = vec![(f64::NAN, f64::NAN); n];
        normal_pair_slice(&first[..n], &second[..n], &mut out);
        for ((&a, &b), &actual) in first.iter().zip(&second).zip(&out) {
            assert_eq!(bits(actual), bits(normal_pair(a, b)));
        }
    }
}

#[test]
// Inspecting output after a panic requires unwinding; aborting targets trap.
#[cfg(panic = "unwind")]
fn mismatched_lengths_preserve_all_output_before_panicking() {
    for (first, second, count) in [(1, 2, 1), (2, 1, 2), (2, 2, 1), (0, 0, 1)] {
        let mut out = vec![(12.5, -3.25); count];
        let before = out.clone();
        let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            normal_pair_slice(&vec![0; first], &vec![0; second], &mut out);
        }));
        assert!(error.is_err());
        assert_eq!(out, before);
    }
}

#[test]
fn discarded_word_bits_do_not_change_the_sampling_grid() {
    let mut stream = SplitMix64::new(0x282_626f_786d_756c);
    for _ in 0..10_000 {
        let (a, b) = (stream.next_u64(), stream.next_u64());
        assert_eq!(
            bits(normal_pair(a, b)),
            bits(normal_pair(a ^ 0xfff, b ^ 0x7ff))
        );
    }
}
