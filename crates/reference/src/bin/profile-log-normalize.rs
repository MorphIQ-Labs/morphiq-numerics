//! Native component-cost and dependent-call diagnostics, separate from the
//! uninstrumented paired throughput experiment in bench-log-normalize.
use morphiq_numerics::{
    elementary::{exp, ln_1p},
    log_space::{log_sum_exp_and_normalize, normalize_log_weights},
};
use std::{hint::black_box, time::Instant};

fn main() {
    println!("gap_bits,method,round,calls,elapsed_ns");
    for gap in [0.0_f64, 4.625, 741.0, 756.0] {
        // Component inputs are computed outside timing. These costs are
        // diagnostic, not an additive decomposition of optimized assembly.
        let tail = exp(-gap);
        for method in [
            "exp",
            "ln_1p",
            "checked_pair",
            "checked_chain",
            "legacy_chain",
        ] {
            for round in 0..10 {
                let calls = if round == 0 { 1000 } else { 20_000 };
                let mut carry = 0.0;
                let mut output = [0.0; 2];
                let start = Instant::now();
                for _ in 0..calls {
                    match method {
                        "exp" => {
                            black_box(exp(black_box(-gap)));
                        }
                        "ln_1p" => {
                            black_box(ln_1p(black_box(tail)));
                        }
                        "checked_pair" => {
                            black_box(
                                normalize_log_weights(
                                    black_box(&[0.0, -gap]),
                                    black_box(&mut output),
                                )
                                .unwrap(),
                            );
                            black_box(output);
                        }
                        "checked_chain" => {
                            let input = [carry, carry - black_box(gap)];
                            black_box(
                                normalize_log_weights(black_box(&input), black_box(&mut output))
                                    .unwrap(),
                            );
                            carry = black_box(output[0]);
                        }
                        "legacy_chain" => {
                            let input = [[carry, carry - black_box(gap)]];
                            let [(_, normalized)] = log_sum_exp_and_normalize(black_box(&input));
                            carry = black_box(normalized.unwrap()[0]);
                        }
                        _ => unreachable!(),
                    }
                }
                let elapsed = start.elapsed().as_nanos();
                black_box(carry);
                if round != 0 {
                    println!("{:016x},{method},{round},{calls},{elapsed}", gap.to_bits());
                }
            }
        }
    }
}
