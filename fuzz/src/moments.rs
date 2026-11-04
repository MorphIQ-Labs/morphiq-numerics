//! Independent MPFR interval oracle for the moment readouts.
use morphiq_numerics::reduce::{MomentEstimate, Moments2};
use rug::{Float, float::Round};

// Exact finite binary64 products span fewer than 4,300 bits. These tests have
// at most 1,027 samples, so 8,192 bits make the raw sums and products exact.
// Division and square root are rounded independently in both directions.
const PRECISION: u32 = 8192;

fn inside(value: f64, error: f64, lower: &Float, upper: &Float) -> bool {
    let value = Float::with_val(PRECISION, value);
    let error = Float::with_val(PRECISION, error);
    let left = Float::with_val(PRECISION, &value - &error);
    let right = Float::with_val(PRECISION, &value + &error);
    left <= *lower && right >= *upper
}

fn assert_encloses(estimate: MomentEstimate, lower: &Float, upper: &Float) {
    assert!(inside(
        estimate.value(),
        estimate.absolute_error(),
        lower,
        upper,
    ));
}

fn oracle(xs: &[f64]) -> [(Float, Float); 3] {
    let mut sum = Float::with_val(PRECISION, 0);
    let mut squares = Float::with_val(PRECISION, 0);
    for &sample in xs {
        let x = Float::with_val(PRECISION, sample);
        sum += &x;
        squares += Float::with_val(PRECISION, &x * &x);
    }
    let n = xs.len() as u32;
    let mean = (
        Float::with_val_round(PRECISION, &sum / n, Round::Down).0,
        Float::with_val_round(PRECISION, &sum / n, Round::Up).0,
    );
    let mut numerator = Float::with_val(PRECISION, &squares * n);
    numerator -= Float::with_val(PRECISION, &sum * &sum);
    let denominator = n * (n - 1);
    let variance = (
        Float::with_val_round(PRECISION, &numerator / denominator, Round::Down).0,
        Float::with_val_round(PRECISION, &numerator / denominator, Round::Up).0,
    );
    let mut sem_lower = Float::with_val_round(PRECISION, &variance.0 / n, Round::Down).0;
    let mut sem_upper = Float::with_val_round(PRECISION, &variance.1 / n, Round::Up).0;
    sem_lower.sqrt_round(Round::Down);
    sem_upper.sqrt_round(Round::Up);
    [mean, variance, (sem_lower, sem_upper)]
}

#[test]
fn moment_bounds_contain_independent_mpfr_intervals() {
    let cases = [
        vec![1e16, 1e16 + 2.0, 1e16 + 4.0],
        vec![1e16, 1e16, 1e16 + 2.0],
        vec![1.0, 1.0, 1.0 + f64::EPSILON],
        vec![-0.0, 0.0, -0.0],
        vec![-1e25, 1e25, 2.0, -3.0],
        vec![1e-25, -1e-25, 2e-25, -3e-25],
        (0..1027).map(|i| 1e12 + (i % 31) as f64 * 0.25).collect(),
        (0..1027).map(|i| if i == 0 { 0.0 } else { 1.0 }).collect(),
    ];
    for xs in cases {
        let expected = oracle(&xs);
        for chunk in [1, 7, 64, 4096] {
            let mut total = Moments2::new();
            for samples in xs.chunks(chunk) {
                let mut batch = Moments2::new();
                for &sample in samples {
                    batch.push(sample).unwrap();
                }
                total.merge(&batch).unwrap();
            }
            for (actual, (lower, upper)) in [
                total.mean().unwrap(),
                total.variance().unwrap(),
                total.standard_error().unwrap(),
            ]
            .into_iter()
            .zip(&expected)
            {
                assert_encloses(actual, lower, upper);
            }
        }
    }
}

#[test]
fn mpfr_oracle_rejects_lost_small_spreads_and_false_zero_error() {
    let expected = oracle(&[1e16, 1e16, 1e16 + 2.0]);
    assert!(!inside(2.0, 1e-15, &expected[1].0, &expected[1].1));
    let rounded = f64::from_bits(0x3ff5_5555_5555_5555);
    assert!(!inside(rounded, 0.0, &expected[1].0, &expected[1].1));
    assert!(inside(rounded, 1e-15, &expected[1].0, &expected[1].1));
}
