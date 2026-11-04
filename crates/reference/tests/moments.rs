//! Independent exact-integer checks of the moment estimates' error bounds.
//! Clear denominators before comparison; no floating-point oracle tolerance.
use morphiq_numerics::reduce::{MomentEstimate, Moments2, MomentsError};
use morphiq_numerics_reference::{Exact, Words};

fn accumulate(xs: &[f64]) -> Moments2 {
    let mut result = Moments2::new();
    for &x in xs {
        result.push(x).unwrap();
    }
    result
}

fn rational_bound(estimate: MomentEstimate, numerator: &Exact, denominator: &Exact) {
    assert!(estimate.value().is_finite());
    assert!(estimate.absolute_error().is_finite());
    assert!(estimate.absolute_error() >= 0.0);
    let residual = &(&Exact::of(estimate.value()) * denominator) - numerator;
    assert!(
        residual.abs() <= &Exact::of(estimate.absolute_error()) * denominator,
        "estimate outside its own absolute bound: {estimate:?}"
    );
}

fn check(xs: &[f64], moments: Moments2) {
    assert_eq!(moments.count(), xs.len() as u64);
    let n = Exact::integer(xs.len() as i64);
    let mut sum = Exact::integer(0);
    let mut squares = Exact::integer(0);
    for &x in xs {
        let x = Exact::of(x);
        sum = &sum + &x;
        squares = &squares + &(&x * &x);
    }
    rational_bound(moments.mean().unwrap(), &sum, &n);
    // n*sum(x²)-sum(x)² is exact, including severe cancellation.
    let numerator = &(&n * &squares) - &(&sum * &sum);
    let denominator = &n * &Exact::integer(xs.len() as i64 - 1);
    let variance = moments.variance().unwrap();
    assert!(variance.value() >= 0.0);
    rational_bound(variance, &numerator, &denominator);
    let sem = moments.standard_error().unwrap();
    assert!(sem.value() >= 0.0);
    let centre = Exact::of(sem.value());
    let error = Exact::of(sem.absolute_error());
    let lower = (&centre - &error).max(Exact::integer(0));
    let upper = &centre + &error;
    let sem_denominator = &denominator * &n;
    assert!(&(&lower * &lower) * &sem_denominator <= numerator);
    assert!(&(&upper * &upper) * &sem_denominator >= numerator);
}

#[test]
fn means_variances_and_standard_errors_enclose_exact_statistics() {
    let mut words = Words::new(0x285_0000_0000_0001);
    for case in 0..400 {
        let n = 2 + (words.next_word() % 63) as usize;
        let scale = f64::from_bits((923 + words.next_word() % 201) << 52);
        let xs: Vec<_> = (0..n)
            .map(|i| match case % 5 {
                0 => 1e16 + 2.0 * (words.next_word() % 15) as f64,
                1 => scale * ((words.next_word() >> 11) as f64 / (1_u64 << 53) as f64 - 0.5),
                2 => {
                    if i == 0 {
                        0.0
                    } else {
                        scale
                    }
                }
                3 => scale + (words.next_word() % 9) as f64 * scale * f64::EPSILON,
                _ => -scale,
            })
            .collect();
        check(&xs, accumulate(&xs));
        for chunk in [1, 2, 7, 31, 128] {
            let mut merged = Moments2::new();
            for batch in xs.chunks(chunk) {
                merged.merge(&accumulate(batch)).unwrap();
            }
            check(&xs, merged);
        }
    }
}

#[test]
fn small_spreads_survive_large_means() {
    for xs in [
        [1e16, 1e16 + 2.0, 1e16 + 4.0],
        [1e16, 1e16, 1e16 + 2.0],
        [1.0, 1.0, 1.0 + f64::EPSILON],
    ] {
        check(&xs, accumulate(&xs));
    }
    assert_eq!(
        accumulate(&[1e16, 1e16 + 2.0, 1e16 + 4.0])
            .variance()
            .unwrap()
            .value(),
        4.0
    );
    // RN(4/3), independently decoded from the exact rational result.
    assert_eq!(
        accumulate(&[1e16, 1e16, 1e16 + 2.0])
            .variance()
            .unwrap()
            .value()
            .to_bits(),
        0x3ff5_5555_5555_5555
    );
}

#[test]
fn undefined_statistics_and_nonfinite_samples_are_typed_refusals() {
    let mut moments = Moments2::new();
    assert_eq!(moments.mean(), Err(MomentsError::Empty));
    assert_eq!(moments.variance(), Err(MomentsError::InsufficientSamples));
    assert_eq!(
        moments.standard_error(),
        Err(MomentsError::InsufficientSamples)
    );
    moments.push(3.0).unwrap();
    assert_eq!(moments.mean().unwrap().value(), 3.0);
    assert_eq!(moments.mean().unwrap().absolute_error(), 0.0);
    assert_eq!(moments.variance(), Err(MomentsError::InsufficientSamples));
    for x in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        let before = moments;
        assert_eq!(moments.push(x), Err(MomentsError::NonFiniteSample));
        assert_eq!(moments, before);
    }
}

#[test]
fn arithmetic_and_count_refusals_preserve_both_accumulators() {
    let mut moments = accumulate(&[0.0]);
    for x in [f64::MAX, f64::from_bits(1)] {
        let before = moments;
        assert!(matches!(moments.push(x), Err(MomentsError::Arithmetic(_))));
        assert_eq!(moments, before);
        let other = accumulate(&[x]);
        assert!(matches!(
            moments.merge(&other),
            Err(MomentsError::Arithmetic(_))
        ));
        assert_eq!(moments, before);
        assert_eq!(other, accumulate(&[x]));
    }
    let one = accumulate(&[7.0]);
    moments = one;
    for _ in 0..53 {
        let copy = moments;
        moments.merge(&copy).unwrap();
    }
    assert_eq!(moments.count(), 1_u64 << 53);
    assert_eq!(moments.mean().unwrap().value(), 7.0);
    assert_eq!(moments.variance().unwrap().value(), 0.0);
    let before = moments;
    assert_eq!(moments.push(7.0), Err(MomentsError::CountOverflow));
    assert_eq!(moments.merge(&one), Err(MomentsError::CountOverflow));
    assert_eq!(moments, before);
    moments.merge(&Moments2::new()).unwrap();
    assert_eq!(moments, before);
}

#[test]
fn empty_merges_are_identities_and_zero_readouts_are_canonical() {
    let original = accumulate(&[2.0, 3.0, 8.0]);
    let mut left = Moments2::new();
    left.merge(&original).unwrap();
    assert_eq!(left, original);
    left.merge(&Moments2::new()).unwrap();
    assert_eq!(left, original);
    for xs in [[-0.0, -0.0], [-0.0, 0.0], [0.0, -0.0]] {
        let m = accumulate(&xs);
        for result in [m.mean(), m.variance(), m.standard_error()] {
            let result = result.unwrap();
            assert_eq!(result.value().to_bits(), 0);
            assert_eq!(result.absolute_error().to_bits(), 0);
        }
    }
}

#[test]
fn fixed_batches_and_merge_order_ignore_worker_count() {
    let xs: Vec<_> = (0..1027).map(|i| 1e8 + (i % 37) as f64 * 0.25).collect();
    let batches: Vec<_> = xs.chunks(64).collect();
    let expected = batches.iter().fold(Moments2::new(), |mut total, batch| {
        total.merge(&accumulate(batch)).unwrap();
        total
    });
    for workers in [1, 2, 4, 7] {
        let mut results = vec![Moments2::new(); batches.len()];
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .map(|worker| {
                    let batches = &batches;
                    scope.spawn(move || {
                        (worker..batches.len())
                            .step_by(workers)
                            .map(|i| (i, accumulate(batches[i])))
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            for handle in handles.into_iter().rev() {
                for (index, batch) in handle.join().unwrap() {
                    results[index] = batch;
                }
            }
        });
        let mut total = Moments2::new();
        for batch in results {
            total.merge(&batch).unwrap();
        }
        assert_eq!(total, expected);
        for (a, b) in [
            (total.mean(), expected.mean()),
            (total.variance(), expected.variance()),
            (total.standard_error(), expected.standard_error()),
        ] {
            let (a, b) = (a.unwrap(), b.unwrap());
            assert_eq!(a.value().to_bits(), b.value().to_bits());
            assert_eq!(a.absolute_error().to_bits(), b.absolute_error().to_bits());
        }
    }
}

#[test]
fn extreme_exponents_enclose_or_refuse_without_losing_state() {
    let mut admitted = 0;
    let mut refused = 0;
    for exponent in (-1074_i32..=1022).step_by(17) {
        let scale = if exponent < -1022 {
            f64::from_bits(1_u64 << (exponent + 1074))
        } else {
            f64::from_bits(((exponent + 1023) as u64) << 52)
        };
        let samples = [0.0, scale, -scale, scale + scale];
        let mut moments = Moments2::new();
        let mut xs = Vec::new();
        for x in samples {
            let before = moments;
            match moments.push(x) {
                Ok(()) => xs.push(x),
                Err(MomentsError::Arithmetic(_) | MomentsError::Range) => {
                    assert_eq!(moments, before);
                    refused += 1;
                }
                result => panic!("unexpected admission result: {result:?}"),
            }
        }
        let n = Exact::integer(xs.len() as i64);
        let sum = xs
            .iter()
            .fold(Exact::integer(0), |s, &x| &s + &Exact::of(x));
        let squares = xs.iter().fold(Exact::integer(0), |s, &x| {
            &s + &(&Exact::of(x) * &Exact::of(x))
        });
        match moments.mean() {
            Ok(mean) => {
                rational_bound(mean, &sum, &n);
                admitted += 1;
            }
            Err(MomentsError::Arithmetic(_) | MomentsError::Range) => refused += 1,
            result => panic!("unexpected mean result: {result:?}"),
        }
        if xs.len() < 2 {
            continue;
        }
        let numerator = &(&n * &squares) - &(&sum * &sum);
        let denominator = &n * &Exact::integer(xs.len() as i64 - 1);
        match moments.variance() {
            Ok(v) => {
                rational_bound(v, &numerator, &denominator);
                admitted += 1;
            }
            Err(MomentsError::Arithmetic(_) | MomentsError::Range) => refused += 1,
            result => panic!("unexpected variance result: {result:?}"),
        }
        match moments.standard_error() {
            Ok(sem) => {
                let centre = Exact::of(sem.value());
                let error = Exact::of(sem.absolute_error());
                let lower = (&centre - &error).max(Exact::integer(0));
                let upper = &centre + &error;
                let denominator = &denominator * &n;
                assert!(&(&lower * &lower) * &denominator <= numerator);
                assert!(&(&upper * &upper) * &denominator >= numerator);
                admitted += 1;
            }
            Err(MomentsError::Arithmetic(_) | MomentsError::Range) => refused += 1,
            result => panic!("unexpected standard-error result: {result:?}"),
        }
    }
    assert!(admitted > 100 && refused > 100);
}
