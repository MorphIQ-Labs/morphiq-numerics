//! Standalone same-host scalar measurements. Compare identical invocations
//! built at the baseline and candidate revisions, with no other timed work.
//! Each result is the median of 31 rounds on 4,096 fixed-seed arguments.

use morphiq_numerics::elementary::{exp2, expm1};
use morphiq_numerics_reference::Words;
use std::hint::black_box;
use std::time::Instant;
const N: usize = 4096;
const ROUNDS: usize = 31;

fn unit(words: &mut Words) -> f64 {
    #[allow(clippy::cast_precision_loss)] // a 53-bit integer
    let u = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
    u
}

/// Median nanoseconds per element of `f` over `xs`.
fn median_ns(xs: &[f64], out: &mut [f64], f: &dyn Fn(&[f64], &mut [f64])) -> f64 {
    // Calibrate the repetitions to about 10 ms.
    let start = Instant::now();
    f(black_box(xs), out);
    let once = start.elapsed().as_secs_f64().max(1e-7);
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let reps = ((0.01 / once) as usize).max(1);
    let mut times: Vec<f64> = (0..ROUNDS)
        .map(|_| {
            let start = Instant::now();
            for _ in 0..reps {
                f(black_box(xs), out);
                black_box(&mut *out);
            }
            #[allow(clippy::cast_precision_loss)]
            let per = start.elapsed().as_secs_f64() * 1e9 / (reps * xs.len()) as f64;
            per
        })
        .collect();
    times.sort_by(f64::total_cmp);
    times[ROUNDS / 2]
}

fn main() {
    if let Some(arg) = std::env::args().nth(1) {
        if arg == "--help" || arg == "-h" {
            println!(
                "bench-exp-stages: median scalar ns/element on standalone exp2/expm1 workloads"
            );
            return;
        }
        if arg == "--version" || arg == "-V" {
            println!("bench-exp-stages {}", env!("CARGO_PKG_VERSION"));
            return;
        }
    }
    let mut words = Words::new(0x6578_705f_7374_6167);
    let mut out = vec![0.0; N];
    println!("| function | range | ns/element |");
    println!("|---|---|---:|");
    for (name, f, lo, hi) in [
        ("exp2", exp2 as fn(f64) -> f64, -1016.0, 1016.0),
        ("exp2", exp2, -1.0, 1.0),
        ("exp2", exp2, -1075.0, 1024.0),
        ("expm1", expm1 as fn(f64) -> f64, -37.0, 704.0),
        ("expm1", expm1, -37.0, -0.03125),
        ("expm1", expm1, -1.0, -0.03125),
        ("expm1", expm1, 0.03125, 1.0),
        ("expm1", expm1, -0.03125, 0.03125),
    ] {
        let xs: Vec<f64> = (0..N).map(|_| lo + (hi - lo) * unit(&mut words)).collect();
        let ns = median_ns(&xs, &mut out, &|xs, out| {
            for (y, &x) in out.iter_mut().zip(xs) {
                *y = f(x);
            }
        });
        println!("| {name} | ({lo}, {hi}) | {ns:.2} |");
    }
}
