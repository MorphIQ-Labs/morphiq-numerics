//! Same-host contract comparison and scalar/slice observations; not CI timing.
//! `MORPHIQ_FAST_BENCH_ITERATIONS` sets timed calls per sample (default 10,000).
use morphiq_numerics::{elementary, fast, normal};
use std::{hint::black_box, time::Instant};

type Scalar = fn(f64) -> f64;
type Slice = fn(&[f64], &mut [f64]);

fn main() {
    if let Some(path) = std::env::args().nth(1) {
        for line in std::fs::read_to_string(path).unwrap().lines() {
            let (name, word) = line.split_once(' ').unwrap();
            let x = f64::from_bits(u64::from_str_radix(word, 16).unwrap());
            let (scalar, slice): (Scalar, Slice) = match name {
                "exp" => (fast::elementary::exp, fast::elementary::exp_slice),
                "ln" => (fast::elementary::ln, fast::elementary::ln_slice),
                "erfcx" => (fast::normal::erfcx, fast::normal::erfcx_slice),
                "cdf" => (fast::normal::norm_cdf, fast::normal::norm_cdf_slice),
                _ => panic!("unknown primitive"),
            };
            let mut out = [0.0; 53];
            slice(&[x; 53], &mut out);
            assert!(out.iter().all(|y| y.to_bits() == scalar(x).to_bits()));
            println!("{name},{word},{:016x}", out[0].to_bits());
        }
        return;
    }
    let iterations = std::env::var_os("MORPHIQ_FAST_BENCH_ITERATIONS").map_or(10_000, |value| {
        value
            .into_string()
            .expect("MORPHIQ_FAST_BENCH_ITERATIONS must be a positive u32")
            .parse::<u32>()
            .expect("MORPHIQ_FAST_BENCH_ITERATIONS must be a positive u32")
    });
    assert!(
        iterations > 0,
        "MORPHIQ_FAST_BENCH_ITERATIONS must be positive"
    );
    eprintln!("timed_iterations={iterations}; values_per_call=52; warmup_calls=100");
    let functions: [(&str, Scalar, Slice, Scalar, Slice, f64, f64); 4] = [
        (
            "ln",
            elementary::ln,
            elementary::ln_slice,
            fast::elementary::ln,
            fast::elementary::ln_slice,
            0.5,
            2.0,
        ),
        (
            "exp",
            elementary::exp,
            elementary::exp_slice,
            fast::elementary::exp,
            fast::elementary::exp_slice,
            -0.2,
            0.2,
        ),
        (
            "erfcx",
            normal::erfcx,
            normal::erfcx_slice,
            fast::normal::erfcx,
            fast::normal::erfcx_slice,
            0.0,
            6.0,
        ),
        (
            "cdf",
            normal::norm_cdf,
            normal::norm_cdf_slice,
            fast::normal::norm_cdf,
            fast::normal::norm_cdf_slice,
            -3.0,
            3.0,
        ),
    ];
    for (name, strong, strong_slice, approximate, approximate_slice, lo, hi) in functions {
        let xs: Vec<_> = (0..65537)
            .map(|i| lo + (hi - lo) * f64::from(i) / 65536.0)
            .collect();
        let mut out = vec![0.0; xs.len()];
        approximate_slice(&xs, &mut out);
        for (&x, &y) in xs.iter().zip(&out) {
            assert_eq!(
                y.to_bits(),
                approximate(x).to_bits(),
                "{name} scalar/lane mismatch at {x:?}"
            );
        }
        let packet: Vec<_> = (0..52)
            .map(|i| lo + (hi - lo) * f64::from(i) / 51.0)
            .collect();
        let mut out = [0.0; 52];
        for mode in [0, 1, 2, 3, 3, 2, 1, 0, 0, 1, 2, 3, 3, 2, 1, 0] {
            let evaluate = |out: &mut [f64]| match mode {
                0 | 1 => {
                    let f = if mode == 0 { strong } else { approximate };
                    for (y, &x) in out.iter_mut().zip(black_box(&packet)) {
                        *y = f(x);
                    }
                }
                2 => strong_slice(black_box(&packet), out),
                3 => approximate_slice(black_box(&packet), out),
                _ => unreachable!(),
            };
            for _ in 0..100 {
                evaluate(&mut out);
            }
            let start = Instant::now();
            for _ in 0..iterations {
                evaluate(black_box(&mut out));
                black_box(&out);
            }
            let elapsed = start.elapsed();
            println!(
                "{name},{mode},{}",
                elapsed.as_secs_f64() * 1e9 / f64::from(iterations)
            );
            eprintln!("{name},{mode},elapsed_ns={}", elapsed.as_nanos());
        }
    }
}
