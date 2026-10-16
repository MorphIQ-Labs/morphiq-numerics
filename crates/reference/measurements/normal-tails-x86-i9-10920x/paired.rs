use std::{hint::black_box, time::Instant};
type Scalar = fn(f64) -> f64;
type Batch = fn(&[f64], &mut [f64]);
fn measure(
    f: Scalar,
    batch: Batch,
    xs: &[f64],
    out: &mut [f64],
    length: usize,
    mode: usize,
) -> f64 {
    let start = Instant::now();
    let mut rounds = 0;
    loop {
        if mode == 0 {
            for (o, &x) in out.iter_mut().zip(black_box(xs)) {
                *o = f(x);
            }
        } else {
            for (x, o) in black_box(xs).chunks(length).zip(out.chunks_mut(length)) {
                batch(x, o);
            }
        }
        black_box(&*out);
        rounds += 1;
        if start.elapsed().as_millis() >= 5 {
            break;
        }
    }
    start.elapsed().as_secs_f64() * 1e9 / (rounds * xs.len()) as f64
}
fn main() {
    println!("function,workload,length,mode,round,variant,ns");
    let functions: [(&str, [Scalar; 2], [Batch; 2]); 5] = [
        (
            "cdf",
            [before::normal::norm_cdf, after::normal::norm_cdf],
            [
                before::normal::norm_cdf_slice,
                after::normal::norm_cdf_slice,
            ],
        ),
        (
            "ccdf",
            [before::normal::norm_ccdf, after::normal::norm_ccdf],
            [
                before::normal::norm_ccdf_slice,
                after::normal::norm_ccdf_slice,
            ],
        ),
        (
            "centered",
            [
                before::normal::norm_cdf_centered,
                after::normal::norm_cdf_centered,
            ],
            [
                before::normal::norm_cdf_centered_slice,
                after::normal::norm_cdf_centered_slice,
            ],
        ),
        (
            "pdf",
            [before::normal::norm_pdf, after::normal::norm_pdf],
            [
                before::normal::norm_pdf_slice,
                after::normal::norm_pdf_slice,
            ],
        ),
        (
            "log_cdf",
            [before::normal::log_norm_cdf, after::normal::log_norm_cdf],
            [
                before::normal::log_norm_cdf_slice,
                after::normal::log_norm_cdf_slice,
            ],
        ),
    ];
    for workload in ["negative_far_tail", "negative_first_table", "underflow", "positive_tail", "ordinary", "mixed"] {
        let mut seed = 0x34beac_u64;
        let xs: Vec<_> = (0..4096)
            .map(|i| {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                let u = (seed >> 11) as f64 / 9007199254740992.;
                match workload {
                    "negative_far_tail" => -37. - u,
                    "negative_first_table" => -37. - 27.*u,
                    "underflow" => 37. + 2.*u,
                    "positive_tail" => 8. + 28.*u,
                    "central" => u - 0.5,
                    "ordinary" => 10. * u - 5.,
                    _ => match i % 5 {
                        0 => u - 0.5,
                        1 => -3. * u,
                        2 => 6. * u,
                        3 => -8. - 28. * u,
                        _ => 20. * u,
                    },
                }
            })
            .collect();
        for (name, fs, bs) in functions {
            let expected: Vec<_> = xs.iter().map(|&x| fs[0](x).to_bits()).collect();
            let mut out = vec![0.; xs.len()];
            for length in [1, 2, 8, 1024] {
                for side in 0..2 {
                    for (&x, &y) in xs.iter().zip(&expected) {
                        if matches!(workload, "ordinary" | "mixed" | "positive_tail") { assert_eq!(fs[side](x).to_bits(), y); }
                    }
                    for (x, o) in xs.chunks(length).zip(out.chunks_mut(length)) {
                        bs[side](x, o);
                    }
                    let expected_side: Vec<_> = xs.iter().map(|&x| fs[side](x).to_bits()).collect();
                    for (&x, &y) in out.iter().zip(&expected_side) {
                        assert_eq!(x.to_bits(), y, "{name}/{workload}/{length}");
                    }
                }
                for round in 0..12 {
                    for offset in 0..2 {
                        let side = (round + offset) % 2;
                        for mode in 0..2 {
                            let ns = measure(fs[side], bs[side], &xs, &mut out, length, mode);
                            if round > 0 {
                                println!(
                                    "{name},{workload},{length},{mode},{round},{side},{ns:.5}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
