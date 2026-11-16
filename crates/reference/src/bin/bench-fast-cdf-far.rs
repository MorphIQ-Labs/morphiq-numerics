//! Far-tail `fast::normal::norm_cdf` (8 < |x| <= 22.5) against the strong entry
//! and the consumer's interim composition (#302). Same-host, paired, alternating
//! rounds; every sample is printed. Not CI timing.
//! `MORPHIQ_FAR_ROUNDS` (default 15) and `MORPHIQ_FAR_REPS` (default 200) tune it.
use morphiq_numerics::{fast, normal};
use std::{hint::black_box, time::Instant};

const N: usize = 4096;

fn bank(lo: f64, hi: f64, signs: u8) -> Vec<f64> {
    let mut word = 0x9e37_79b9_7f4a_7c15_u64;
    (0..N)
        .map(|i| {
            word ^= word << 13;
            word ^= word >> 7;
            word ^= word << 17;
            let u = (word >> 11) as f64 / (1u64 << 53) as f64;
            let a = lo + (hi - lo) * u;
            match signs {
                0 => -a,
                1 => a,
                _ => {
                    if i % 2 == 0 {
                        -a
                    } else {
                        a
                    }
                }
            }
        })
        .collect()
}

fn composition(x: f64) -> f64 {
    let a = x.abs();
    let scaled = a * core::f64::consts::FRAC_1_SQRT_2;
    if a <= 8.0 || scaled >= 16.0 {
        return fast::normal::norm_cdf(x);
    }
    let lower = 0.5 * fast::elementary::exp(-0.5 * a * a) * fast::normal::erfcx(scaled);
    if x < 0.0 { lower } else { 1.0 - lower }
}

fn throughput(f: fn(f64) -> f64, xs: &[f64], reps: u32) -> f64 {
    let t = Instant::now();
    let mut acc = 0.0;
    for _ in 0..reps {
        for &x in xs {
            acc += f(black_box(x));
        }
    }
    black_box(acc);
    t.elapsed().as_secs_f64() * 1e9 / (f64::from(reps) * xs.len() as f64)
}

fn latency(f: fn(f64) -> f64, xs: &[f64], reps: u32) -> f64 {
    let t = Instant::now();
    let mut y = 0.0;
    for _ in 0..reps {
        for &x in xs {
            // The result feeds the next argument through a value-preserving
            // dependency (y*0 is 0 for finite y).
            y = f(black_box(x) + y * 0.0);
        }
    }
    black_box(y);
    t.elapsed().as_secs_f64() * 1e9 / (f64::from(reps) * xs.len() as f64)
}

fn slice_time(f: fn(&[f64], &mut [f64]), xs: &[f64], reps: u32) -> f64 {
    let mut out = vec![0.0; xs.len()];
    let t = Instant::now();
    for _ in 0..reps {
        f(black_box(xs), &mut out);
        black_box(&out);
    }
    t.elapsed().as_secs_f64() * 1e9 / (f64::from(reps) * xs.len() as f64)
}

fn slice_strong(xs: &[f64], out: &mut [f64]) {
    normal::norm_cdf_slice(xs, out);
}
fn slice_comp(xs: &[f64], out: &mut [f64]) {
    for (o, &x) in out.iter_mut().zip(xs) {
        *o = composition(x);
    }
}

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn main() {
    let rounds: usize = std::env::var("MORPHIQ_FAR_ROUNDS").map_or(15, |v| v.parse().unwrap());
    let reps: u32 = std::env::var("MORPHIQ_FAR_REPS").map_or(200, |v| v.parse().unwrap());
    let banks = [
        ("far_neg_8_22.5", bank(8.0, 22.5, 0)),
        ("far_pos_8_22.5", bank(8.0, 22.5, 1)),
        ("far_mixed_8_22.5", bank(8.0, 22.5, 2)),
        ("far_mixed_8_16", bank(8.0, 16.0, 2)),
    ];
    // Accuracy observation (not a proof): new entry and composition vs strong.
    for (name, xs) in &banks {
        let (mut en, mut ec) = (0.0_f64, 0.0_f64);
        for &x in xs {
            let s = normal::norm_cdf(x);
            let d = if x < 0.0 { s } else { 1.0 };
            en = en.max((fast::normal::norm_cdf(x) - s).abs() / d);
            ec = ec.max((composition(x) - s).abs() / d);
        }
        println!(
            "accuracy,{name},new_max_rel_to_2^-53={:.1},composition_max={:.1}",
            en * 9007199254740992.0,
            ec * 9007199254740992.0
        );
    }
    println!("cell,candidate,round,ns_per_value_candidate,ns_per_value_reference");
    for (name, xs) in &banks {
        for (kind, candidates) in [
            ("scalar_throughput", ["strong", "composition"]),
            ("dependent_latency", ["strong", "composition"]),
            ("slice_4096", ["strong", "composition"]),
        ] {
            for reference in candidates {
                let mut ratios = Vec::new();
                for r in 0..rounds {
                    let run = |which: &str| -> f64 {
                        match (kind, which) {
                            ("scalar_throughput", "new") => {
                                throughput(fast::normal::norm_cdf, xs, reps)
                            }
                            ("scalar_throughput", "strong") => {
                                throughput(normal::norm_cdf, xs, reps)
                            }
                            ("scalar_throughput", _) => throughput(composition, xs, reps),
                            ("dependent_latency", "new") => {
                                latency(fast::normal::norm_cdf, xs, reps)
                            }
                            ("dependent_latency", "strong") => latency(normal::norm_cdf, xs, reps),
                            ("dependent_latency", _) => latency(composition, xs, reps),
                            (_, "new") => slice_time(fast::normal::norm_cdf_slice, xs, reps),
                            (_, "strong") => slice_time(slice_strong, xs, reps),
                            _ => slice_time(slice_comp, xs, reps),
                        }
                    };
                    let (a, b) = if r % 2 == 0 {
                        let a = run("new");
                        (a, run(reference))
                    } else {
                        let b = run(reference);
                        (run("new"), b)
                    };
                    println!("{name}/{kind},vs_{reference},{r},{a:.3},{b:.3}");
                    ratios.push(a / b);
                }
                let med = median(&mut ratios.clone());
                let (lo, hi) = (
                    ratios.iter().cloned().fold(f64::MAX, f64::min),
                    ratios.iter().cloned().fold(0.0, f64::max),
                );
                println!(
                    "summary,{name}/{kind},new/{reference},median={med:.3},min={lo:.3},max={hi:.3}"
                );
            }
        }
    }
}
