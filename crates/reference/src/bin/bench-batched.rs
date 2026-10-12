//! Same-host timing of the batched functions against a loop of the scalar
//! function, per argument range (docs/lanes.md §7):
//!
//! ```sh
//! cargo run --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-batched
//! ```
//!
//! Each figure is the median over 31 rounds of the time per element on 4,096
//! arguments, the loop repeated to about 10 ms per round. Timing is a local
//! measurement, never a CI result.

use std::hint::black_box;
use std::time::Instant;

use morphiq_numerics::elementary::{
    exp, exp_slice, exp2, exp2_slice, expm1, expm1_slice, ln, ln_1p, ln_1p_slice, ln_slice,
};
use morphiq_numerics_reference::Words;

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

fn row(
    name: &str,
    range: &str,
    xs: &[f64],
    scalar: fn(f64) -> f64,
    batched: fn(&[f64], &mut [f64]),
) {
    let mut out = vec![0.0; xs.len()];
    let looped = |x: &[f64], o: &mut [f64]| {
        for (o, &x) in o.iter_mut().zip(x) {
            *o = scalar(x);
        }
    };
    let s = median_ns(xs, &mut out, &looped);
    let b = median_ns(xs, &mut out, &|x, o| batched(x, o));
    println!("| `{name}` | {range} | {s:.2} | {b:.2} | {:.2}× |", s / b);
}

fn main() {
    if let Some(arg) = std::env::args().nth(1) {
        if arg == "--help" || arg == "-h" {
            println!(
                "bench-batched: median ns per element, scalar loop against the batched function"
            );
            return;
        }
        if arg == "--version" || arg == "-V" {
            println!("bench-batched {}", env!("CARGO_PKG_VERSION"));
            return;
        }
    }
    let mut words = Words::new(0x6265_6e63_685f_6c61);
    let d: Vec<f64> = (0..N).map(|_| -30.0 * unit(&mut words)).collect();
    let domain: Vec<f64> = (0..N).map(|_| -745.0 + 1454.0 * unit(&mut words)).collect();
    let near_one: Vec<f64> = (0..N).map(|_| 0.5 + 1.5 * unit(&mut words)).collect();
    let positive: Vec<f64> = (0..N)
        .map(|_| f64::from_bits(1 + words.next_word() % 0x7fef_ffff_ffff_ffff))
        .collect();
    let t: Vec<f64> = d.iter().map(|&d| exp(d)).collect();
    let z: Vec<f64> = (0..N)
        .map(|_| {
            let z = 12.0 * unit(&mut words) - 6.0;
            z * z / 4.0
        })
        .collect();
    let wide: Vec<f64> = (0..N)
        .map(|_| -1.0 + morphiq_numerics::elementary::exp2(62.0 * unit(&mut words) - 2.0))
        .collect();
    let exp2_domain: Vec<f64> = (0..N)
        .map(|_| -1075.0 + 2099.0 * unit(&mut words))
        .collect();
    let small: Vec<f64> = (0..N).map(|_| (unit(&mut words) - 0.5) / 16.0).collect();
    let expm1_domain: Vec<f64> = (0..N).map(|_| -37.4 + 746.4 * unit(&mut words)).collect();
    println!("| Function | Arguments | Scalar loop (ns) | Batched (ns) | Speed-up |");
    println!("|---|---|---|---|---|");
    row("exp", "`[−30, 0]`", &d, exp, exp_slice);
    row("exp", "`[−745, 709]`", &domain, exp, exp_slice);
    row("ln", "`[0.5, 2)`", &near_one, ln, ln_slice);
    row("ln", "positive encodings", &positive, ln, ln_slice);
    row("ln_1p", "`e^d`, `d ∈ [−30, 0]`", &t, ln_1p, ln_1p_slice);
    row("ln_1p", "`z²/4`, `z ∈ [−6, 6]`", &z, ln_1p, ln_1p_slice);
    row(
        "ln_1p",
        "`[−1, 2^60]`, log-uniform",
        &wide,
        ln_1p,
        ln_1p_slice,
    );
    row("exp2", "`[−30, 0]`", &d, exp2, exp2_slice);
    row("exp2", "`[−1075, 1024]`", &exp2_domain, exp2, exp2_slice);
    row("expm1", "`[−30, 0]`", &d, expm1, expm1_slice);
    row("expm1", "`[−1/32, 1/32]`", &small, expm1, expm1_slice);
    row("expm1", "`[−37.4, 709]`", &expm1_domain, expm1, expm1_slice);
}
