//! Local development measurements; never a timing assertion or CI speed gate.
use super::{Operation, evaluate, fast_decide, special};
use crate::lanes::{Kernel, map};
use core::hint::black_box;
use std::time::{Duration, Instant};
use std::vec;
use std::vec::Vec;

fn measure(mut run: impl FnMut(), count: usize) -> f64 {
    let start = Instant::now();
    let mut repetitions = 0_u32;
    loop {
        run();
        repetitions += 1;
        if start.elapsed() >= Duration::from_millis(150) {
            break;
        }
    }
    #[allow(clippy::cast_precision_loss)] // measurement sizes
    {
        start.elapsed().as_secs_f64() * 1e9 / (f64::from(repetitions) * count as f64)
    }
}

// Serial data dependency through the preceding result. This includes array
// lookup and index arithmetic; the identity chain reports that overhead.
fn dependent_measure(xs: &[f64], f: impl Fn(f64) -> f64) -> f64 {
    let mut index = 0;
    measure(
        || {
            for _ in 0..1024 {
                let value = f(black_box(xs[index]));
                let bits = usize::try_from((value.to_bits() >> 32) & 1023).unwrap();
                index = (index + 1 + bits) % xs.len();
                black_box(value);
            }
            black_box(index);
        },
        1024,
    )
}

fn workload(name: &str) -> Vec<f64> {
    (0..1024)
        .map(|i| {
            let u = f64::from(i) / 1023.0;
            match name {
                "tiny" => (u - 0.5) * super::SMALL,
                "central" => u - 0.5,
                "ordinary" => 10.0 * u - 5.0,
                "negative_tail" => -8.0 - 28.0 * u,
                "negative_far_tail" => -37.0 - u,
                "negative_first_table" => -37.0 - 27.0 * u,
                "negative_wide_tail" => {
                    let exponent = 6 + i * 506 / 1023;
                    let fraction = u64::try_from(i)
                        .unwrap()
                        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                        & ((1 << 50) - 1);
                    -f64::from_bits((u64::try_from(exponent + 1023).unwrap() << 52) | fraction)
                }
                "positive_tail" => 8.0 + 28.0 * u,
                "underflow" => 37.0 + 2.0 * u,
                "log_overflow" => -super::tables::LOG_OVERFLOW * (1.0 + u),
                "mixed" => match i % 5 {
                    0 => u - 0.5,
                    1 => -3.0 * u,
                    2 => 6.0 * u,
                    3 => -8.0 - 28.0 * u,
                    _ => 20.0 * u,
                },
                _ => unreachable!(),
            }
        })
        .collect()
}

fn bench<G: Kernel>(name: &str, op: Operation, complement: bool, kind: &str, xs: &[f64]) {
    let mut out = vec![0.0; xs.len()];
    let scalar = measure(
        || {
            for (o, &x) in out.iter_mut().zip(black_box(xs)) {
                *o = G::scalar(x);
            }
            black_box(&out);
        },
        xs.len(),
    );
    let batch = measure(
        || {
            map::<G>(black_box(xs), &mut out);
            black_box(&out);
        },
        xs.len(),
    );
    let chain = dependent_measure(xs, G::scalar);
    let overhead = dependent_measure(xs, |x| x);
    let mut fallback = 0;
    for &x in xs {
        let x = if complement { -x } else { x };
        if special(op, x).is_some() {
            continue;
        }
        let decided = fast_decide(op, x).is_some();
        if !decided {
            fallback += 1;
        }
    }
    std::println!(
        "{name},{kind},{},{scalar:.3},{batch:.3},{:.3},{fallback},{chain:.3},{overhead:.3}",
        xs.len(),
        scalar / batch
    );
    // Keep the scalar composition referenced independently of G::scalar.
    black_box(evaluate(op, xs[0]));
}

#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn normal_local_performance() {
    use super::lanes::Normal;
    std::println!(
        "function,workload,count,scalar_ns,batch_ns,speedup,accurate_count,scalar_chain_ns,chain_overhead_ns"
    );
    let selected = std::env::var("MORPHIQ_NORMAL_BENCH_WORKLOAD").ok();
    let length = std::env::var("MORPHIQ_NORMAL_BENCH_LENGTH")
        .map(|value| value.parse::<usize>().expect("integer benchmark length"))
        .unwrap_or(1024);
    assert!((1..=1024).contains(&length));
    let workloads = [
        "tiny",
        "central",
        "ordinary",
        "negative_tail",
        "negative_far_tail",
        "negative_first_table",
        "negative_wide_tail",
        "positive_tail",
        "underflow",
        "log_overflow",
        "mixed",
    ];
    if let Some(name) = selected.as_deref() {
        assert!(
            workloads.contains(&name),
            "unknown normal benchmark workload: {name}"
        );
    }
    for kind in workloads {
        if selected.as_deref().is_some_and(|selected| selected != kind) {
            continue;
        }
        let full = workload(kind);
        let xs: Vec<_> = (0..length)
            .map(|i| full[i * 1023 / length.saturating_sub(1).max(1)])
            .collect();
        bench::<Normal<0>>("pdf", Operation::Pdf, false, kind, &xs);
        bench::<Normal<1>>("cdf", Operation::Cdf, false, kind, &xs);
        bench::<Normal<2>>("ccdf", Operation::Cdf, true, kind, &xs);
        bench::<Normal<3>>("centered", Operation::Centered, false, kind, &xs);
        bench::<Normal<4>>("log_cdf", Operation::LogCdf, false, kind, &xs);
    }
}
