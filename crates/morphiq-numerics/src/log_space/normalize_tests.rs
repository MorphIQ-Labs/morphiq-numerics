//! Independent interval fixtures: generators/log_normalize_reference.py,
//! mpmath 1.4.1, adaptive 256+ bit interval arithmetic. No tolerance widening.

use super::{MAX_NORMALIZE_TERMS, NormalizeError, log_sum_exp, normalize_log_weights};
use crate::test_exact::{entries, field, word};
use std::{vec, vec::Vec};

const FIXTURE: &str = include_str!("../../../reference/fixtures/log_normalize.json");

fn values(case: &str, name: &str) -> Vec<f64> {
    field(case, name)
        .split_whitespace()
        .map(|s| f64::from_bits(u64::from_str_radix(s, 16).unwrap()))
        .collect()
}

#[test]
fn normalized_logs_cover_independent_intervals() {
    let cases = entries(FIXTURE, &["cases"]);
    assert_eq!(cases.len(), 58);
    for case in cases {
        let x = values(case, "x");
        let mut output = vec![f64::NAN; x.len()];
        let evaluation = normalize_log_weights(&x, &mut output).unwrap();
        let lo = values(case, "lo");
        let hi = values(case, "hi");
        let radius = evaluation.max_absolute_error();
        assert!(radius.is_finite() && radius >= 0.0);
        for i in 0..x.len() {
            let got = output[i];
            assert!(
                lo[i] <= got && got <= hi[i],
                "{}[{i}]: {got:e} outside [{:e}, {:e}]",
                field(case, "label"),
                lo[i],
                hi[i]
            );
            if x[i] == f64::NEG_INFINITY {
                assert_eq!(got, f64::NEG_INFINITY);
            } else {
                assert!(got.is_finite() && got <= 0.0);
            }
        }
        // Compatibility is a separate check from the independent oracle.
        assert_eq!(evaluation.log_sum().to_bits(), log_sum_exp(&x).to_bits());
    }
}

fn rejects_without_writes(x: &[f64], length: usize, expected: NormalizeError) {
    let sentinel = f64::from_bits(0x7ff8_0000_0000_3456);
    let mut output = vec![sentinel; length];
    assert_eq!(normalize_log_weights(x, &mut output), Err(expected));
    assert!(output.iter().all(|x| x.to_bits() == sentinel.to_bits()));
}

#[test]
fn invalid_shape_support_and_representability_leave_output_unchanged() {
    rejects_without_writes(&[], 0, NormalizeError::ZeroMass);
    rejects_without_writes(&[0.0], 0, NormalizeError::LengthMismatch);
    rejects_without_writes(&[], 1, NormalizeError::LengthMismatch);
    rejects_without_writes(&[f64::NEG_INFINITY; 3], 3, NormalizeError::ZeroMass);
    for invalid in [f64::NAN, f64::INFINITY] {
        for index in 0..3 {
            let mut input = [0.0; 3];
            input[index] = invalid;
            rejects_without_writes(&input, 3, NormalizeError::InvalidWeight(index));
        }
    }
    rejects_without_writes(
        &[f64::MAX, -f64::MAX],
        2,
        NormalizeError::Unrepresentable(1),
    );
    rejects_without_writes(
        &[-f64::MAX, f64::MAX],
        2,
        NormalizeError::Unrepresentable(0),
    );
    rejects_without_writes(
        &[0.0, f64::NAN, f64::INFINITY],
        3,
        NormalizeError::InvalidWeight(1),
    );
}

#[test]
fn one_finite_entry_is_exact_even_among_structural_zeros() {
    for value in [-f64::MAX, -800.0, -0.0, 0.0, f64::from_bits(1), f64::MAX] {
        for index in 0..3 {
            let mut input = [f64::NEG_INFINITY; 3];
            input[index] = value;
            let mut output = [42.0; 3];
            let result = normalize_log_weights(&input, &mut output).unwrap();
            assert_eq!(result.log_sum().to_bits(), value.to_bits());
            assert_eq!(result.max_absolute_error().to_bits(), 0.0_f64.to_bits());
            for (i, p) in output.iter().enumerate() {
                assert_eq!(
                    p.to_bits(),
                    if i == index {
                        0.0_f64.to_bits()
                    } else {
                        f64::NEG_INFINITY.to_bits()
                    }
                );
            }
        }
        let mut out = [1.0];
        assert_eq!(
            normalize_log_weights(&[value], &mut out)
                .unwrap()
                .log_sum()
                .to_bits(),
            value.to_bits()
        );
        assert_eq!(out, [0.0]);
    }
}

#[test]
fn maximum_qualified_count_matches_closed_form_and_counts_only_finite_entries() {
    let maximum = entries(FIXTURE, &["maximum_uniform"])[0];
    assert_eq!(
        field(maximum, "count").parse::<usize>().unwrap(),
        MAX_NORMALIZE_TERMS
    );
    let mut input = vec![0.0; MAX_NORMALIZE_TERMS];
    let mut output = vec![1.0; input.len()];
    let result = normalize_log_weights(&input, &mut output).unwrap();
    let (lo, hi) = (word(maximum, "lo"), word(maximum, "hi"));
    assert!(output.iter().all(|v| lo <= *v && *v <= hi));
    assert!(result.max_absolute_error() > 0.0);
    input.push(0.0);
    rejects_without_writes(&input, input.len(), NormalizeError::TooManyFiniteTerms);
    *input.last_mut().unwrap() = f64::NEG_INFINITY;
    output.push(1.0);
    normalize_log_weights(&input, &mut output).unwrap();
    assert_eq!(*output.last().unwrap(), f64::NEG_INFINITY);
    assert!(
        output[..MAX_NORMALIZE_TERMS]
            .iter()
            .all(|v| lo <= *v && *v <= hi)
    );
}

#[test]
fn oracle_rejects_unshifted_subtraction_and_ordinary_space_zeroing() {
    let cases = entries(FIXTURE, &["cases"]);
    let common = cases
        .iter()
        .find(|c| field(c, "label") == "huge-positive-common-offset")
        .unwrap();
    let x = values(common, "x");
    let broken = x[0] - log_sum_exp(&x);
    assert!(broken > values(common, "hi")[0]);
    let tail = cases
        .iter()
        .find(|c| field(c, "label") == "finite-mass-below-ordinary-underflow")
        .unwrap();
    assert!(f64::NEG_INFINITY < values(tail, "lo")[1]);
}

#[test]
fn fixed_order_normalization_matches_the_scalar_reduction_bits() {
    // A feature-equivalence control, separate from the interval fixtures.
    // This path evaluates the same mathematical contract using the scalar
    // helper even in a SIMD build, including lane boundaries and remainders.
    for n in [2, 3, 31, 32, 33, 64, 65, 129] {
        let x: Vec<_> = (0..n)
            .map(|i| {
                if i % 7 == 0 {
                    f64::NEG_INFINITY
                } else {
                    -(f64::from(i) * 0.125)
                }
            })
            .collect();
        let (maximum, first) = super::shift(&x).unwrap();
        let correction = crate::elementary::ln_1p(super::scalar_terms(&x, maximum, first));
        let mut output = vec![0.0; x.len()];
        normalize_log_weights(&x, &mut output).unwrap();
        for (x, got) in x.iter().zip(output) {
            assert_eq!(got.to_bits(), ((x - maximum) - correction).to_bits());
        }
    }
}

#[test]
fn finite_pair_specialization_preserves_slice_bits_and_failures() {
    // Operation-sequence consistency, separate from the independent interval
    // anchors above: padding with an exact zero forces the general slice path.
    // SplitMix64 supplies raw bit patterns, including huge spans and subnormals.
    let mut seed = 0x6e6f_726d_7061_6972_u64;
    let mut word = || {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        f64::from_bits(z ^ (z >> 31))
    };
    for _ in 0..8192 {
        let pair = [word(), word()];
        let mut compact = [17.0; 2];
        let mut padded = [17.0; 3];
        let a = normalize_log_weights(&pair, &mut compact);
        let b = normalize_log_weights(&[pair[0], pair[1], f64::NEG_INFINITY], &mut padded);
        assert_eq!(a, b);
        assert_eq!(
            compact.map(f64::to_bits),
            [padded[0].to_bits(), padded[1].to_bits()]
        );
    }
}
