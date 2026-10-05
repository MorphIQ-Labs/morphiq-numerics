//! The reductions against their stated error bounds, decided in exact integer
//! arithmetic, and against Ogita, Rump and Oishi's worked example.

use morphiq_numerics::reduce::{dot, dot2, max_abs, sum, sum_squares, sum_squares2, sum2};
use morphiq_numerics_reference::{Exact, Words};

/// `u = 2^-53` to the power `k`.
fn u(k: i64) -> Exact {
    Exact::power_of_two(-53 * k)
}

fn exact_sum(x: &[f64]) -> Exact {
    x.iter()
        .fold(Exact::integer(0), |acc, &v| &acc + &Exact::of(v))
}

fn exact_dot(x: &[f64], y: &[f64]) -> Exact {
    x.iter().zip(y).fold(Exact::integer(0), |acc, (&a, &b)| {
        &acc + &(&Exact::of(a) * &Exact::of(b))
    })
}

fn magnitudes(x: &[f64]) -> Exact {
    x.iter()
        .fold(Exact::integer(0), |acc, &v| &acc + &Exact::of(v).abs())
}

fn abs_dot(x: &[f64], y: &[f64]) -> Exact {
    x.iter().zip(y).fold(Exact::integer(0), |acc, (&a, &b)| {
        &acc + &(&Exact::of(a) * &Exact::of(b)).abs()
    })
}

fn k_u(k: usize) -> Exact {
    &Exact::integer(i64::try_from(k).unwrap()) * &u(1)
}

/// `|computed − exact| ≤ γ_k · T`, with `γ_k = k·u / (1 − k·u)`'s denominator
/// cleared: `|computed − exact| · (1 − k·u) ≤ k·u · T`.
fn assert_gamma_bound(computed: f64, exact: &Exact, k: usize, t: &Exact, context: &str) {
    let error = (&Exact::of(computed) - exact).abs();
    let one_minus = &Exact::integer(1) - &k_u(k);
    assert!(
        &error * &one_minus <= &k_u(k) * t,
        "{context}: error exceeds γ_{k}·T"
    );
}

/// `|computed − exact| ≤ u·|exact| + γ_k² · T`, with the denominator
/// `(1 − k·u)²` cleared.
fn assert_compensated_bound(computed: f64, exact: &Exact, k: usize, t: &Exact, context: &str) {
    let error = (&Exact::of(computed) - exact).abs();
    let one_minus = &Exact::integer(1) - &k_u(k);
    let squared = &one_minus * &one_minus;
    let rhs = &(&(&u(1) * &exact.abs()) * &squared) + &(&(&k_u(k) * &k_u(k)) * t);
    assert!(
        &error * &squared <= rhs,
        "{context}: error exceeds u·|s| + γ_{k}²·T"
    );
}

/// A value with a random sign and an exponent in `[low, high]`.
fn value(words: &mut Words, low: i64, high: i64) -> f64 {
    let span = u64::try_from(high - low + 1).unwrap();
    let e = low + i64::try_from(words.next_word() % span).unwrap();
    words.with_exponent(e)
}

/// Terms whose sum cancels heavily: random values, then their negatives
/// perturbed by a few units in the last place, shuffled by the stream.
fn ill_conditioned(words: &mut Words, n: usize) -> Vec<f64> {
    let mut x: Vec<f64> = (0..n / 2).map(|_| value(words, -40, 40)).collect();
    let negatives: Vec<f64> = x
        .iter()
        .map(|&v| {
            let k = words.next_word() % 4;
            -f64::from_bits(v.to_bits() + k)
        })
        .collect();
    x.extend(negatives);
    for i in (1..x.len()).rev() {
        let j = usize::try_from(words.next_word() % u64::try_from(i + 1).unwrap()).unwrap();
        x.swap(i, j);
    }
    x
}

const CASES: usize = 2_000;

#[test]
fn sum_is_within_gamma_n_minus_1_of_the_magnitudes() {
    let mut words = Words::new(0x5c4e_0001_5c4e_0001);
    for case in 0..CASES {
        let n = 1 + case % 64;
        let x: Vec<f64> = if case % 2 == 0 {
            (0..n).map(|_| value(&mut words, -60, 60)).collect()
        } else {
            ill_conditioned(&mut words, n)
        };
        let k = x.len().saturating_sub(1);
        assert_gamma_bound(sum(&x), &exact_sum(&x), k, &magnitudes(&x), "sum");
    }
}

#[test]
fn sum2_is_within_its_compensated_bound() {
    let mut words = Words::new(0x5c4e_0002_5c4e_0002);
    for case in 0..CASES {
        let n = 1 + case % 64;
        let x: Vec<f64> = if case % 2 == 0 {
            (0..n).map(|_| value(&mut words, -60, 60)).collect()
        } else {
            ill_conditioned(&mut words, n)
        };
        let k = x.len().saturating_sub(1);
        assert_compensated_bound(sum2(&x), &exact_sum(&x), k, &magnitudes(&x), "sum2");
    }
}

/// Ogita, Rump and Oishi's Table 4.1: for `p = [1, θ, θ², −θ, −θ², −1]` with
/// `fl(1 ± θ) = 1` and `fl(θ ± θ²) = θ`, the plain sum is exactly 0 and Sum2
/// returns `−θ²`. Its error is still within the bound.
#[test]
fn sum2_reproduces_the_papers_worked_example() {
    // 2^-54: 1 ± θ and θ ± θ² are ties that round (to even) to 1 and θ.
    let theta = f64::from_bits((1023 - 54) << 52);
    assert_eq!(1.0 + theta, 1.0);
    assert_eq!(1.0 - theta, 1.0);
    assert_eq!(theta + theta * theta, theta);
    assert_eq!(theta - theta * theta, theta);
    let p = [1.0, theta, theta * theta, -theta, -theta * theta, -1.0];
    assert_eq!(sum(&p).to_bits(), 0.0_f64.to_bits());
    assert_eq!(sum2(&p).to_bits(), (-(theta * theta)).to_bits());
    assert_compensated_bound(sum2(&p), &exact_sum(&p), 5, &magnitudes(&p), "table 4.1");
}

#[test]
fn dot_is_within_gamma_n_when_no_product_underflows() {
    let mut words = Words::new(0x0d07_0001_0d07_0001);
    for case in 0..CASES {
        let n = 1 + case % 64;
        let x: Vec<f64> = (0..n).map(|_| value(&mut words, -60, 60)).collect();
        let y: Vec<f64> = if case % 2 == 0 {
            (0..n).map(|_| value(&mut words, -60, 60)).collect()
        } else {
            // Products that cancel: y paired with x's terms to nearly sum to zero.
            ill_conditioned(&mut words, n)
        };
        assert_gamma_bound(dot(&x, &y), &exact_dot(&x, &y), n, &abs_dot(&x, &y), "dot");
    }
}

#[test]
fn dot2_is_within_its_compensated_bound() {
    let mut words = Words::new(0x0d07_0002_0d07_0002);
    for case in 0..CASES {
        let n = 1 + case % 64;
        let (x, y): (Vec<f64>, Vec<f64>) = if case % 2 == 0 {
            (
                (0..n).map(|_| value(&mut words, -60, 60)).collect(),
                (0..n).map(|_| value(&mut words, -60, 60)).collect(),
            )
        } else {
            // An ill-conditioned dot product: pairs (a, b) and (a, −b'), b' a
            // few ulps from b, so the exact result is tiny next to |x|ᵀ|y|.
            let half: Vec<(f64, f64)> = (0..n / 2 + 1)
                .map(|_| (value(&mut words, -30, 30), value(&mut words, -30, 30)))
                .collect();
            let mut pairs: Vec<(f64, f64)> = half.clone();
            for &(a, b) in &half {
                let k = words.next_word() % 4;
                pairs.push((a, -f64::from_bits(b.to_bits() + k)));
            }
            pairs.truncate(n);
            pairs.into_iter().unzip()
        };
        assert_compensated_bound(
            dot2(&x, &y),
            &exact_dot(&x, &y),
            n,
            &abs_dot(&x, &y),
            "dot2",
        );
    }
}

#[test]
fn sums_of_squares_are_the_dot_products_of_a_vector_with_itself() {
    let mut words = Words::new(0x5953_0001_5953_0001);
    for case in 0..CASES {
        let n = case % 64;
        let x: Vec<f64> = (0..n).map(|_| value(&mut words, -60, 60)).collect();
        assert_eq!(sum_squares(&x).to_bits(), dot(&x, &x).to_bits());
        assert_eq!(sum_squares2(&x).to_bits(), dot2(&x, &x).to_bits());
        let exact = exact_dot(&x, &x);
        assert_compensated_bound(sum_squares2(&x), &exact, n, &exact, "sum_squares2");
    }
}

#[test]
fn empty_and_single_inputs() {
    for f in [sum, sum2, sum_squares, sum_squares2, max_abs] {
        assert_eq!(f(&[]).to_bits(), 0.0_f64.to_bits());
    }
    assert_eq!(dot(&[], &[]).to_bits(), 0.0_f64.to_bits());
    assert_eq!(dot2(&[], &[]).to_bits(), 0.0_f64.to_bits());
    // The plain sum of one term is that term; Sum2 adds σ = +0, as the paper
    // states it, so −0 becomes +0.
    assert_eq!(sum(&[-0.0]).to_bits(), (-0.0_f64).to_bits());
    assert_eq!(sum2(&[-0.0]).to_bits(), 0.0_f64.to_bits());
    assert_eq!(sum2(&[1.5]).to_bits(), 1.5_f64.to_bits());
}

#[test]
#[should_panic(expected = "different lengths")]
fn dot_rejects_slices_of_different_lengths() {
    let _ = dot(&[1.0, 2.0], &[1.0]);
}

#[test]
fn max_abs_is_the_largest_magnitude_and_propagates_the_first_nan() {
    assert_eq!(max_abs(&[1.0, -3.0, 2.0]), 3.0);
    assert_eq!(max_abs(&[-0.0]).to_bits(), 0.0_f64.to_bits());
    assert_eq!(max_abs(&[f64::NEG_INFINITY, 1.0]), f64::INFINITY);
    let first = f64::from_bits(0x7ff8_0000_0000_0001);
    let second = f64::from_bits(0x7ff8_0000_0000_0002);
    assert_eq!(
        max_abs(&[1.0, first, 2.0, second]).to_bits(),
        first.to_bits()
    );
}
