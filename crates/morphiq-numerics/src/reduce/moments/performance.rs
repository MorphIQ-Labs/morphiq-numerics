//! Native comparison methodology; ignored in correctness CI. No timing gates.
use super::{Bounded, Moments2};
use crate::reduce::{sum_squares2, sum2};
use std::{hint::black_box, println, time::Instant, vec::Vec};

// Original implementation of the shifted Welford recurrence using exactly the
// same checked arithmetic and error propagation as the selected accumulator.
#[derive(Clone, Copy)]
struct Welford {
    n: u64,
    anchor: f64,
    mean: Bounded,
    m2: Bounded,
}
impl Welford {
    fn new() -> Self {
        Self {
            n: 0,
            anchor: 0.0,
            mean: Bounded::point(0.0),
            m2: Bounded::point(0.0),
        }
    }
    fn push(&mut self, x: f64) {
        assert!(x.is_finite() && self.n < (1_u64 << 53));
        if self.n == 0 {
            self.anchor = x;
            self.n = 1;
            return;
        }
        let x = Bounded::difference(x, self.anchor).unwrap();
        let delta = x.sub(self.mean).unwrap();
        let mean = self
            .mean
            .add(delta.div((self.n + 1) as f64).unwrap())
            .unwrap();
        let m2 = self
            .m2
            .add(delta.mul(x.sub(mean).unwrap()).unwrap())
            .unwrap();
        self.mean = mean;
        self.m2 = m2;
        self.n += 1;
    }
    fn variance(self) -> (f64, f64) {
        let v = self
            .m2
            .div((self.n - 1) as f64)
            .unwrap()
            .estimate()
            .unwrap();
        (v.value(), v.absolute_error())
    }
}

fn public(xs: &[f64], streams: usize) -> f64 {
    let mut state = [Moments2::new(); 4];
    for &x in xs {
        for s in &mut state[..streams] {
            s.push(black_box(x)).unwrap();
        }
    }
    state[..streams]
        .iter()
        .map(|s| {
            let v = s.variance().unwrap();
            black_box(v.absolute_error());
            v.value()
        })
        .sum()
}
fn checked_welford(xs: &[f64], streams: usize) -> f64 {
    let mut state = [Welford::new(); 4];
    for &x in xs {
        for s in &mut state[..streams] {
            s.push(black_box(x));
        }
    }
    state[..streams]
        .iter()
        .map(|s| {
            let (v, error) = s.variance();
            black_box(error);
            v
        })
        .sum()
}
fn ordinary_welford(xs: &[f64], streams: usize) -> f64 {
    let mut mean = [0.0; 4];
    let mut m2 = [0.0; 4];
    for (i, &x) in xs.iter().enumerate() {
        for s in 0..streams {
            let x = black_box(x);
            let d = x - mean[s];
            mean[s] += d / (i + 1) as f64;
            m2[s] += d * (x - mean[s]);
        }
    }
    m2[..streams].iter().sum::<f64>() / (xs.len() - 1) as f64
}
fn corrected_two_pass(xs: &[f64], streams: usize) -> f64 {
    let mut result = 0.0;
    for _ in 0..streams {
        let mean = sum2(black_box(xs)) / xs.len() as f64;
        let centered: Vec<_> = xs.iter().map(|x| x - mean).collect();
        let residual = sum2(&centered);
        result += (sum_squares2(&centered) - residual * (residual / xs.len() as f64))
            / (xs.len() - 1) as f64;
    }
    result
}

fn inputs(region: usize, n: usize) -> Vec<f64> {
    let mut word = 0x285_0000_0000_0001_u64;
    (0..n)
        .map(|i| {
            word ^= word << 13;
            word ^= word >> 7;
            word ^= word << 17;
            match region {
                0 => (word % 65536) as f64 / 256.0,
                1 => 1e16 + 2.0 * (word % 17) as f64,
                2 => {
                    if i == 0 {
                        0.0
                    } else {
                        1.0
                    }
                }
                _ => ((word % 65536) as f64 - 32768.0) / 256.0,
            }
        })
        .collect()
}

#[test]
#[ignore = "native release measurement; see scripts/bench_moments/README.md"]
fn native_moments_performance() {
    type Candidate = (&'static str, fn(&[f64], usize) -> f64);
    let candidates: [Candidate; 4] = [
        ("moments", public),
        ("checked_welford", checked_welford),
        ("ordinary_welford", ordinary_welford),
        ("corrected_two_pass", corrected_two_pass),
    ];
    println!("moments,region,n,streams,round,implementation,repetitions,ns_per_observation");
    for region in 0..4 {
        for n in [3, 65, 4096] {
            let xs = inputs(region, n);
            for streams in [1, 4] {
                let reps = (65536 / (n * streams)).max(8);
                for round in 0..18 {
                    for offset in 0..candidates.len() {
                        let (name, run) = candidates[(round + offset) % candidates.len()];
                        let start = Instant::now();
                        for _ in 0..reps {
                            black_box(run(black_box(&xs), streams));
                        }
                        let ns = start.elapsed().as_nanos() as f64 / (reps * n * streams) as f64;
                        // The first three rounds are retained warmups.
                        println!("moments,{region},{n},{streams},{round},{name},{reps},{ns:.6}");
                    }
                }
            }
        }
    }
    // Public merge and readout cost, with input generation outside timing.
    let mut batch = Moments2::new();
    for x in inputs(0, 65) {
        batch.push(x).unwrap();
    }
    println!("moments_operation,round,operation,repetitions,ns_per_operation");
    for round in 0..18 {
        for operation in 0..4 {
            let reps = 65536;
            let mut total = batch;
            let start = Instant::now();
            for _ in 0..reps {
                match operation {
                    0 => {
                        total.merge(black_box(&batch)).unwrap();
                        black_box(total);
                    }
                    1 => {
                        black_box(black_box(&batch).mean().unwrap());
                    }
                    2 => {
                        black_box(black_box(&batch).variance().unwrap());
                    }
                    _ => {
                        black_box(black_box(&batch).standard_error().unwrap());
                    }
                }
            }
            let ns = start.elapsed().as_nanos() as f64 / reps as f64;
            println!("moments_operation,{round},{operation},{reps},{ns:.6}");
        }
    }
}

#[test]
#[ignore = "emit the exact timed input/output population for independent oracle checking"]
fn moment_benchmark_observations() {
    println!("moment_observation,region,n,implementation,value_bits,error_bits");
    for region in 0..4 {
        for n in [3, 65, 4096] {
            let xs = inputs(region, n);
            let mut moments = Moments2::new();
            let mut welford = Welford::new();
            for (index, &x) in xs.iter().enumerate() {
                println!("moment_input,{region},{n},{index},{:016x}", x.to_bits());
                moments.push(x).unwrap();
                welford.push(x);
            }
            let estimate = moments.variance().unwrap();
            for (name, (value, error)) in [
                ("moments", (estimate.value(), estimate.absolute_error())),
                ("checked_welford", welford.variance()),
                ("ordinary_welford", (ordinary_welford(&xs, 1), f64::NAN)),
                ("corrected_two_pass", (corrected_two_pass(&xs, 1), f64::NAN)),
            ] {
                println!(
                    "moment_observation,{region},{n},{name},{:016x},{:016x}",
                    value.to_bits(),
                    error.to_bits()
                );
            }
        }
    }
}
