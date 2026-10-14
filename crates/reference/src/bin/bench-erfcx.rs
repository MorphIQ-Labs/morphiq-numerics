//! Local scalar/SIMD erfcx throughput and dependency-chain latency.
//! Run with --release --features simd,std. CSV reports all 31 rounds;
//! metadata (host, revision, toolchain, flags and load) belongs beside it.
use morphiq_numerics::{
    normal::{erfcx, erfcx_slice},
    random::{SplitMix64, unit_closed_open},
};
use std::{hint::black_box, time::Instant};

const N: usize = 4096;
const REPS: usize = 64;
const ROUNDS: usize = 31;

fn run(kind: usize, xs: &[f64], out: &mut [f64]) -> f64 {
    let start = Instant::now();
    let mut previous = 0.0_f64;
    for _ in 0..REPS {
        match kind {
            0 => {
                for (o, &x) in out.iter_mut().zip(black_box(xs)) {
                    *o = erfcx(x);
                }
            }
            1 => erfcx_slice(black_box(xs), out),
            _ => {
                for &x in black_box(xs) {
                    // Each call depends on the prior result. Toggle one low input
                    // bit to keep the chain in its original workload region.
                    let arg = f64::from_bits(x.to_bits() ^ (black_box(previous).to_bits() & 1));
                    previous = erfcx(arg);
                }
            }
        }
        black_box(&mut *out);
    }
    black_box(previous);
    start.elapsed().as_secs_f64() * 1e9 / (REPS * xs.len()) as f64
}

fn main() {
    if std::env::args().any(|a| a == "--help" || a == "-h") {
        println!("bench-erfcx: raw CSV ns/call, 31 alternating rounds, 4096 inputs × 64 repeats");
        return;
    }
    if std::env::args().any(|a| a == "--version" || a == "-V") {
        println!("bench-erfcx {}", env!("CARGO_PKG_VERSION"));
        return;
    }
    let mut rng = SplitMix64::new(0x34_beac);
    let mut ranges = Vec::new();
    for (name, low, width) in [
        ("table", -0.5, 16.5),
        ("positive_common", 0., 6.),
        ("asymptotic", 16., 496.),
        ("reciprocal", 512., 4096.),
        ("negative", -26.6, 26.1),
    ] {
        let xs: Vec<f64> = (0..N)
            .map(|_| low + width * unit_closed_open(rng.next_u64()))
            .collect();
        ranges.push((name, xs));
    }
    let tail: Vec<f64> = (0..N)
        .map(|_| f64::from_bits(0x7fc2_0dd7_5042_9b6e + rng.next_u64() % 0x002d_f228_afbd_6491))
        .collect();
    ranges.push(("subnormal", tail));
    let mixed: Vec<f64> = (0..N).map(|i| ranges[i % 5].1[i]).collect();
    ranges.push(("mixed", mixed));
    println!("range,round,mode,ns_per_call");
    for (name, xs) in ranges {
        let mut out = vec![0.; N];
        erfcx_slice(&xs, &mut out);
        for (&x, &y) in xs.iter().zip(&out) {
            assert_eq!(y.to_bits(), erfcx(x).to_bits());
        }
        for kind in 0..3 {
            black_box(run(kind, &xs, &mut out));
        }
        for round in 0..ROUNDS {
            for offset in 0..3 {
                let kind = (offset + round) % 3;
                let ns = run(kind, &xs, &mut out);
                println!(
                    "{name},{round},{},{ns:.4}",
                    ["scalar", "simd", "latency"][kind]
                );
            }
        }
    }
}
