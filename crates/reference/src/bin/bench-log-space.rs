//! Same-host scalar log-sum-exp measurements, using the fixed-seed inputs,
//! black-box boundaries and monotonic clock of `bench-batched`.
//!
//! Build this identical harness at both revisions; alternate fresh processes
//! without concurrent benchmarks or builds. CSV retains every sample. The
//! `dependent` loop uses the preceding result's low bit to select one of two
//! adjacent inputs, so calls cannot overlap. It includes that dependency's
//! indexing cost. `independent` measures a loop of independent scalar calls.
//! Neither mode batches calls into SIMD lanes.

use morphiq_numerics::log_space::log_sum_exp;
use morphiq_numerics_reference::Words;
use std::hint::black_box;
use std::time::Instant;

const N: usize = 4096;

fn unit(words: &mut Words) -> f64 {
    #[allow(clippy::cast_precision_loss)] // exactly representable 53-bit integer
    let u = (words.next_word() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
    u
}

fn inputs(kind: &str) -> Vec<[f64; 8]> {
    let mut words = Words::new(0x6c6f_675f_7370_6163);
    (0..N)
        .map(|i| {
            let u = unit(&mut words);
            let v = unit(&mut words);
            let (a, b) = match kind {
                "near_equal" => (-4.0, -4.0 - 1e-12 * u),
                "separated" | "eight_terms" => (40.0 * u - 20.0, -30.0 * v - 20.0),
                // m + ln(2) nearly cancels; both inputs are neighbours of
                // RN(-ln(2)). These are inputs, not expected answers.
                "cancellation" => (
                    f64::from_bits(0xbfe6_2e42_fefa_39e8 + (words.next_word() & 15)),
                    f64::from_bits(0xbfe6_2e42_fefa_39e8 + (words.next_word() & 15)),
                ),
                "compensation" => (1e-8 * u, -30.0 * v),
                // |d| > 704 fails exp's stage screen, and exp(d) is below
                // ln_1p's stage screens: explicitly fallback-heavy inputs.
                "fallback" => (0.0, -710.0 - 30.0 * u),
                "underflow" => (-0.0, -746.0 - 54.0 * u),
                _ => unreachable!(),
            };
            let mut x = [f64::NEG_INFINITY; 8];
            (x[0], x[1]) = if i & 1 == 0 { (a, b) } else { (b, a) };
            if kind == "eight_terms" {
                for term in &mut x[2..] {
                    *term = -40.0 * unit(&mut words);
                }
            }
            x
        })
        .collect()
}

fn run(xs: &[[f64; 8]], len: usize, calls: usize, dependent: bool) -> u64 {
    let mut bits = 0u64;
    for i in 0..calls {
        // Both members of the indexed pair come from the same distribution.
        // The outer index progresses even if the feedback bit is constant.
        let feedback = if dependent { (bits & 1) as usize } else { 0 };
        let at = (2 * i + feedback) & (N - 1);
        bits = log_sum_exp(black_box(&xs[at][..len])).to_bits();
        black_box(bits);
    }
    bits
}

fn main() {
    let mut calls = 100_000usize;
    let mut rounds = 1usize;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                println!(
                    "bench-log-space [--calls N] [--rounds N]: every sample as CSV; build identically at each revision"
                );
                return;
            }
            "--version" | "-V" => {
                println!("bench-log-space {}", env!("CARGO_PKG_VERSION"));
                return;
            }
            "--calls" => calls = args.next().expect("--calls N").parse().expect("integer N"),
            "--rounds" => rounds = args.next().expect("--rounds N").parse().expect("integer N"),
            _ => panic!("unknown argument: {arg}; see --help"),
        }
    }
    assert!(calls > 0 && rounds > 0);
    println!("case,mode,round,calls,elapsed_ns,final_bits");
    for kind in [
        "near_equal",
        "separated",
        "cancellation",
        "compensation",
        "fallback",
        "underflow",
        "eight_terms",
    ] {
        let xs = inputs(kind);
        let len = if kind == "eight_terms" { 8 } else { 2 };
        for dependent in [false, true] {
            black_box(run(&xs, len, N, dependent));
            for round in 0..rounds {
                let start = Instant::now();
                let bits = run(&xs, len, calls, dependent);
                let elapsed = start.elapsed().as_nanos();
                let mode = if dependent {
                    "dependent"
                } else {
                    "independent"
                };
                println!("{kind},{mode},{round},{calls},{elapsed},{bits:016x}");
            }
        }
    }
}
