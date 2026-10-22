//! Unpublished reciprocal-pivot experiment, qualification owned by #152.
//! Inputs, allocation and oracle/certificate qualification are outside timing,
//! except explicitly timed setup/certificate work. No public API is changed.
#[path = "tridiagonal_reciprocal/mod.rs"]
mod reciprocal;
use morphiq_numerics::linalg::tridiagonal::{DominantTridiagonal, ThomasFactors};
use std::{hint::black_box, time::Instant};

fn certify(
    f: &ThomasFactors<'_, '_>,
    count: usize,
    rhs: &[f64],
    out: &[f64],
    b: &mut [f64],
    x: &mut [f64],
) {
    for column in 0..count {
        for row in 0..b.len() {
            b[row] = rhs[row * count + column];
            x[row] = out[row * count + column];
        }
        black_box(f.certify(black_box(b), black_box(x)).unwrap());
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 6, "n kind method calls rhs_count");
    let n: usize = args[1].parse().unwrap();
    let kind = &args[2];
    let method = &args[3];
    let calls: usize = args[4].parse().unwrap();
    let count: usize = args[5].parse().unwrap();
    assert!(n > 0 && count > 0 && calls > 0);
    let scale = match kind.as_str() {
        "tiny" => f64::from_bits(16),
        "large" => 1e300,
        _ => 1.0,
    };
    let lower = vec![-scale; n - 1];
    let upper: Vec<_> = (0..n - 1)
        .map(|i| {
            if kind == "mixed" && i % 2 == 0 {
                scale
            } else {
                -scale
            }
        })
        .collect();
    let diagonal = vec![
        (if kind == "near" {
            2.0 + 4.0 * f64::EPSILON
        } else {
            4.0
        }) * scale;
        n
    ];
    // Same RHS as the pinned LAPACK harness, repeated across columns.
    let rhs: Vec<_> = (0..n * count)
        .map(|at| f64::from(u32::try_from(at / count % 13).unwrap()) * scale)
        .collect();
    let mut out = vec![0.0; rhs.len()];
    let mut expected = vec![0.0; rhs.len()];
    let a = DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap();
    let mut p = vec![0.0; n];
    let mut u = vec![0.0; n - 1];
    a.factor_into(&mut p, &mut u).unwrap();
    let mut inv = vec![0.0; n];
    reciprocal::prepare(&p, &mut inv);
    let mut base_p = vec![0.0; n];
    let mut base_u = vec![0.0; n - 1];
    let baseline = a.factor_into(&mut base_p, &mut base_u).unwrap();
    let fast = reciprocal::Factors {
        lower: &lower,
        pivots: &p,
        normalized_upper: &u,
        reciprocal: &inv,
    };
    baseline
        .solve_many_into(count, &rhs, &mut expected)
        .unwrap();
    fast.solve_many_into(count, &rhs, &mut out).unwrap();
    let mut b = vec![0.0; n];
    let mut x = vec![0.0; n];
    // A failed certificate is recorded during numerical qualification, not
    // silently timed as a successful certified solve.
    if kind != "tiny" && kind != "large" {
        certify(&baseline, count, &rhs, &expected, &mut b, &mut x);
        certify(&baseline, count, &rhs, &out, &mut b, &mut x);
    }
    let mut work_p = vec![0.0; n];
    let mut work_u = vec![0.0; n - 1];
    let mut work_inv = vec![0.0; n];
    let start = Instant::now();
    for _ in 0..calls {
        match method.as_str() {
            "division" | "division_certified" => {
                if count == 1 {
                    baseline
                        .solve_into(black_box(&rhs), black_box(&mut out))
                        .unwrap();
                } else {
                    baseline
                        .solve_many_into(count, black_box(&rhs), black_box(&mut out))
                        .unwrap();
                }
                if method == "division_certified" {
                    certify(&baseline, count, &rhs, &out, &mut b, &mut x);
                }
            }
            "reciprocal" | "reciprocal_certified" => {
                fast.solve_many_into(count, black_box(&rhs), black_box(&mut out))
                    .unwrap();
                if method == "reciprocal_certified" {
                    certify(&baseline, count, &rhs, &out, &mut b, &mut x);
                }
            }
            "division_group" | "division_setup" => {
                let f = a
                    .factor_into(black_box(&mut work_p), black_box(&mut work_u))
                    .unwrap();
                if method == "division_group" {
                    f.solve_many_into(count, black_box(&rhs), black_box(&mut out))
                        .unwrap();
                }
                black_box(f);
            }
            "reciprocal_group" | "reciprocal_setup" => {
                a.factor_into(black_box(&mut work_p), black_box(&mut work_u))
                    .unwrap();
                reciprocal::prepare(black_box(&work_p), black_box(&mut work_inv));
                let f = reciprocal::Factors {
                    lower: &lower,
                    pivots: &work_p,
                    normalized_upper: &work_u,
                    reciprocal: &work_inv,
                };
                if method == "reciprocal_group" {
                    f.solve_many_into(count, black_box(&rhs), black_box(&mut out))
                        .unwrap();
                }
                black_box(f);
            }
            "copy_control" => {
                black_box(&mut out).copy_from_slice(black_box(&rhs));
            }
            _ => panic!("unknown method"),
        }
        black_box(&out);
    }
    println!("{}", start.elapsed().as_nanos());
    if std::env::var_os("TRIDIAGONAL_DUMP").is_some() {
        for x in out {
            println!("{:016x}", x.to_bits());
        }
    }
}
