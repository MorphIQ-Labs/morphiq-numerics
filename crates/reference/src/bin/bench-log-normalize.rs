//! Paired native measurements for docs/log_normalize.md. The shifted-scratch
//! alternative has the same contract on these exact-difference dyadic inputs.
//! All buffers are allocated before timing; every call includes validation,
//! normalization and radius construction. No oracle runs inside timed loops.

use morphiq_numerics::log_space::{
    MAX_NORMALIZE_TERMS, NormalizeError, log_sum_exp, log_sum_exp_and_normalize,
    normalize_log_weights,
};
use std::{hint::black_box, time::Instant};

// A stable composition of existing APIs. This comparison is restricted to
// inputs with exact x-max differences (the generated dyadics and equal huge
// offsets). A general implementation would need an additional shift-error
// budget. Its scratch is caller-owned and reused, not allocated per call.
fn shifted(x: &[f64], out: &mut [f64], scratch: &mut [f64]) -> Result<(f64, f64), NormalizeError> {
    if x.len() != out.len() || x.len() != scratch.len() {
        return Err(NormalizeError::LengthMismatch);
    }
    let mut maximum = f64::NEG_INFINITY;
    let mut finite = 0;
    for (i, &v) in x.iter().enumerate() {
        if v == f64::NEG_INFINITY {
            continue;
        }
        if !v.is_finite() {
            return Err(NormalizeError::InvalidWeight(i));
        }
        finite += 1;
        if finite > MAX_NORMALIZE_TERMS {
            return Err(NormalizeError::TooManyFiniteTerms);
        }
        if v > maximum {
            maximum = v;
        }
    }
    if finite == 0 {
        return Err(NormalizeError::ZeroMass);
    }
    for (slot, &v) in scratch.iter_mut().zip(x) {
        *slot = v - maximum;
    }
    let correction = log_sum_exp(scratch);
    let mut magnitude = 0.0_f64;
    for (i, &v) in scratch.iter().enumerate() {
        if x[i] == f64::NEG_INFINITY {
            continue;
        }
        let p = v - correction;
        if !p.is_finite() {
            return Err(NormalizeError::Unrepresentable(i));
        }
        magnitude = magnitude.max(-p);
    }
    for (p, &v) in out.iter_mut().zip(scratch.iter()) {
        *p = v - correction;
    }
    let radius = if finite == 1 {
        0.0
    } else {
        ((8.0 * (f64::EPSILON / 2.0) * magnitude).next_up() + f64::from_bits((4 * finite) as u64))
            .next_up()
    };
    Ok((
        if correction == 0.0 {
            maximum
        } else {
            maximum + correction
        },
        radius,
    ))
}

fn run(name: &str, x: &[f64], out: &mut [f64], scratch: &mut [f64], calls: usize) {
    for _ in 0..calls {
        match name {
            "checked" => {
                black_box(normalize_log_weights(black_box(x), black_box(out)).unwrap());
            }
            "shifted_scratch" => {
                black_box(shifted(black_box(x), black_box(out), black_box(scratch)).unwrap());
            }
            "legacy_pair" => {
                black_box(log_sum_exp_and_normalize(black_box(&[[x[0], x[1]]])));
            }
            _ => unreachable!(),
        }
        black_box(&out);
    }
}

fn main() {
    let pairs_only = std::env::args().any(|arg| arg == "--pairs-only");
    println!("case,k,method,round,calls,elapsed_ns");
    for n in [1, 2, 3, 8, 32, 128, 1024, 65536] {
        if pairs_only && n != 2 {
            continue;
        }
        for kind in ["ordinary", "zeros_tails", "common_offset"] {
            let x: Vec<_> = (0..n)
                .map(|i| match kind {
                    "ordinary" => -f64::from(((i * 37) % 257) as u16) * 0.125,
                    "zeros_tails" => {
                        if i == 0 {
                            0.0
                        } else if i % 7 == 0 {
                            f64::NEG_INFINITY
                        } else {
                            -740.0 - f64::from((i % 17) as u8)
                        }
                    }
                    "common_offset" => f64::from_bits(0x7e70_0000_0000_0000),
                    _ => unreachable!(),
                })
                .collect();
            let mut output = vec![0.0; n];
            let mut alternative = vec![0.0; n];
            let mut scratch = vec![0.0; n];
            let checked = normalize_log_weights(&x, &mut output).unwrap();
            let other = shifted(&x, &mut alternative, &mut scratch).unwrap();
            assert!(
                output
                    .iter()
                    .zip(&alternative)
                    .all(|(a, b)| a.to_bits() == b.to_bits())
            );
            assert_eq!(checked.log_sum().to_bits(), other.0.to_bits());
            assert_eq!(checked.max_absolute_error().to_bits(), other.1.to_bits());
            let methods = if n == 2 {
                &['c', 's', 'p'][..]
            } else {
                &['c', 's'][..]
            };
            let calls = (1_000_000 / n).clamp(16, 100_000);
            for &method in methods {
                let name = match method {
                    'c' => "checked",
                    's' => "shifted_scratch",
                    _ => "legacy_pair",
                };
                run(name, &x, &mut output, &mut scratch, calls / 4 + 1);
            }
            for round in 0..9 {
                for i in 0..methods.len() {
                    let at = if round % 2 == 0 {
                        i
                    } else {
                        methods.len() - i - 1
                    };
                    let name = match methods[at] {
                        'c' => "checked",
                        's' => "shifted_scratch",
                        _ => "legacy_pair",
                    };
                    let start = Instant::now();
                    run(name, &x, &mut output, &mut scratch, calls);
                    println!(
                        "{kind},{n},{name},{round},{calls},{}",
                        start.elapsed().as_nanos()
                    );
                }
            }
        }
    }
}
