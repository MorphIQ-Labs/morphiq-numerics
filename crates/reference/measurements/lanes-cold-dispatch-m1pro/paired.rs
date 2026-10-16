use std::{hint::black_box, time::Instant};
type Batch = fn(&[f64], &mut [f64]);
fn measure(f: Batch, xs: &[f64], out: &mut [f64], length: usize) -> f64 {
    let start = Instant::now();
    let mut rounds = 0;
    loop {
        for (input, output) in black_box(xs).chunks(length).zip(out.chunks_mut(length)) {
            f(input, output);
        }
        black_box(&mut *out);
        rounds += 1;
        if start.elapsed().as_millis() >= 5 {
            break;
        }
    }
    start.elapsed().as_secs_f64() * 1e9 / (rounds * xs.len()) as f64
}
fn bench(function: &str, workload: &str, xs: &[f64], functions: [Batch; 3]) {
    let mut output = vec![0.; xs.len()];
    let mut expected = vec![0.; xs.len()];
    functions[0](xs, &mut expected);
    for length in [2, 8, 4096] {
        for f in functions {
            for (input, out) in xs.chunks(length).zip(output.chunks_mut(length)) {
                f(input, out);
            }
            for (i, (&a, &b)) in output.iter().zip(&expected).enumerate() {
                assert!(
                    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan()),
                    "{function}/{workload} {length} {i}: {a} {b}"
                );
            }
        }
        for round in 0..12 {
            for offset in 0..3 {
                let side = (round + offset) % 3;
                let ns = measure(functions[side], xs, &mut output, length);
                if round > 0 {
                    println!("{function},{workload},{length},{round},{side},{ns:.5}");
                }
            }
        }
    }
}
fn main() {
    println!("function,workload,length,round,variant,ns");
    let screened = [f64::NAN, f64::INFINITY, -1., -2., 0., -0., 1e-300];
    for workload in ["exp_neg", "huge", "screened", "mixed"] {
        let mut rng = before::random::SplitMix64::new(0x34beac);
        let xs: Vec<_> = (0..4096)
            .map(|i| {
                let bits = rng.next_u64();
                let u = (bits >> 11) as f64 / 9007199254740992.;
                match workload {
                    "exp_neg" => {
                        before::elementary::exp2((-30. + 30. * u) * std::f64::consts::LOG2_E)
                    }
                    "huge" => f64::from_bits(0x7fb0_0000_0000_0000 + bits % (1 << 54)),
                    "screened" => screened[i % screened.len()],
                    _ => match i % 4 {
                        0 => before::elementary::exp2((-30. + 30. * u) * std::f64::consts::LOG2_E),
                        1 => before::elementary::exp2(-2. + 62. * u) - 1.,
                        2 => screened[(i / 4) % screened.len()],
                        _ => -1. / 128. + u / 64.,
                    },
                }
            })
            .collect();
        bench(
            "ln_1p",
            workload,
            &xs,
            [
                original::elementary::ln_1p_slice,
                before::elementary::ln_1p_slice,
                after::elementary::ln_1p_slice,
            ],
        );
    }
    for (function, workload, low, width, fs) in [
        (
            "ln",
            "common",
            0.5,
            1.5,
            [
                original::elementary::ln_slice as Batch,
                before::elementary::ln_slice,
                after::elementary::ln_slice,
            ],
        ),
        (
            "ln",
            "close_to_one",
            1. - 1. / 281474976710656.,
            1. / 140737488355328.,
            [
                original::elementary::ln_slice as Batch,
                before::elementary::ln_slice,
                after::elementary::ln_slice,
            ],
        ),
        (
            "log_norm_cdf",
            "central",
            -0.5,
            1.,
            [
                original::normal::log_norm_cdf_slice as Batch,
                before::normal::log_norm_cdf_slice,
                after::normal::log_norm_cdf_slice,
            ],
        ),
    ] {
        let mut rng = before::random::SplitMix64::new(0x34beac);
        let xs: Vec<_> = (0..4096)
            .map(|_| low + width * ((rng.next_u64() >> 11) as f64 / 9007199254740992.))
            .collect();
        bench(function, workload, &xs, fs);
    }
}
