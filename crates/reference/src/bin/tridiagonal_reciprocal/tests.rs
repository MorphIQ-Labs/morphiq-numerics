use super::*;
use morphiq_numerics::linalg::tridiagonal::DominantTridiagonal;
use morphiq_numerics_reference::Exact;
use serde_json::Value;

fn vector(case: &Value, name: &str) -> Vec<f64> {
    case[name]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| f64::from_bits(u64::from_str_radix(x.as_str().unwrap(), 16).unwrap()))
        .collect()
}
fn integer(s: &str) -> Exact {
    let mut value = Exact::integer(0);
    for digit in s.trim_start_matches('-').bytes() {
        value = &(&value * &Exact::integer(10)) + &Exact::integer(i64::from(digit - b'0'));
    }
    if s.starts_with('-') { -&value } else { value }
}

#[test]
fn independently_certified_fixture_candidates_and_batch_bits() {
    let fixtures: Value =
        serde_json::from_str(include_str!("../../../fixtures/tridiagonal.json")).unwrap();
    let mut report = Vec::new();
    for case in fixtures["cases"].as_array().unwrap() {
        let lower = vector(case, "lower");
        let d = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let b = vector(case, "rhs");
        let n = d.len();
        let off = n.saturating_sub(1);
        let a = DominantTridiagonal::new(&lower, &d, &upper).unwrap();
        let mut p = vec![0.0; n];
        let mut u = vec![0.0; off];
        a.factor_into(&mut p, &mut u).unwrap();
        let mut inv = vec![0.0; n];
        prepare(&p, &mut inv);
        let f = Factors {
            lower: &lower,
            pivots: &p,
            normalized_upper: &u,
            reciprocal: &inv,
        };
        let mut bp = vec![0.0; n];
        let mut bu = vec![0.0; off];
        let baseline = a.factor_into(&mut bp, &mut bu).unwrap();
        let mut result = vec![0.0; n];
        let mut original = vec![0.0; n];
        f.solve_many_into(1, &b, &mut result).unwrap();
        baseline.solve_into(&b, &mut original).unwrap();
        let bound = baseline.certify(&b, &result).unwrap();
        let old_bound = baseline.certify(&b, &original).unwrap();
        for (row, &x) in result.iter().enumerate() {
            let numerator = integer(case["solution"][row][0].as_str().unwrap());
            let denominator = integer(case["solution"][row][1].as_str().unwrap());
            let error = &(&Exact::of(x) * &denominator) - &numerator;
            assert!(
                error.abs() <= &Exact::of(bound.max_solution_error()) * &denominator,
                "{} row={row}",
                case["name"]
            );
            let mut residual = &Exact::of(d[row]) * &Exact::of(x);
            if row > 0 {
                residual = &residual + &(&Exact::of(lower[row - 1]) * &Exact::of(result[row - 1]));
            }
            if row + 1 < n {
                residual = &residual + &(&Exact::of(upper[row]) * &Exact::of(result[row + 1]));
            }
            residual = &residual - &Exact::of(b[row]);
            assert!(residual.abs() <= Exact::of(bound.max_residual()));
        }
        for count in [1, 2, 3, 4, 7, 8, 9, 17] {
            let rhs: Vec<_> = (0..n * count)
                .map(|at| {
                    if at % count % 2 == 0 {
                        b[at / count]
                    } else {
                        -b[at / count]
                    }
                })
                .collect();
            let mut out = vec![0.0; rhs.len()];
            f.solve_many_into(count, &rhs, &mut out).unwrap();
            for column in 0..count {
                let single: Vec<_> = (0..n).map(|row| rhs[row * count + column]).collect();
                let mut scalar = vec![0.0; n];
                f.solve_columns(1, &single, &mut scalar, 0).unwrap();
                for row in 0..n {
                    assert_eq!(out[row * count + column].to_bits(), scalar[row].to_bits());
                }
            }
        }
        report.push(serde_json::json!({"case":case["name"],"n":n,
            "baseline_bits":original.iter().map(|x|format!("{:016x}",x.to_bits())).collect::<Vec<_>>(),
            "candidate_bits":result.iter().map(|x|format!("{:016x}",x.to_bits())).collect::<Vec<_>>(),
            "changed_components":result.iter().zip(&original).filter(|(a,b)|a.to_bits()!=b.to_bits()).count(),
            "fallback_pivots":inv.iter().filter(|&&r|r==0.0).count(),
            "baseline_solution_bound":old_bound.max_solution_error(),"candidate_solution_bound":bound.max_solution_error(),
            "baseline_residual_bound":old_bound.max_residual(),"candidate_residual_bound":bound.max_residual()}));
    }
    if let Ok(path) = std::env::var("RECIPROCAL_REPORT") {
        std::fs::write(path, serde_json::to_string_pretty(&report).unwrap() + "\n").unwrap();
    }
    println!("{} independently certified systems", report.len());
}

#[test]
fn reciprocal_range_fallback_and_argument_contract() {
    for d in [
        f64::from_bits(1),
        -f64::from_bits(1),
        f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
    ] {
        let p = [d];
        let mut inv = [0.0];
        prepare(&p, &mut inv);
        let f = Factors {
            lower: &[],
            pivots: &p,
            normalized_upper: &[],
            reciprocal: &inv,
        };
        let rhs = [d, -d, 0.0, -0.0, d, -d, 0.0, -0.0, d];
        let mut out = [42.0; 9];
        f.solve_many_into(9, &rhs, &mut out).unwrap();
        for i in 0..9 {
            let expected = if inv[0] == 0.0 {
                rhs[i] / d
            } else {
                rhs[i] * inv[0]
            };
            assert_eq!(out[i].to_bits(), expected.to_bits());
        }
        if d.abs() == f64::from_bits(1) {
            assert_eq!(inv, [0.0]);
            assert_eq!(out[0], 1.0);
        }
        assert_eq!(f.solve_many_into(8, &rhs, &mut out), Err(Error::Shape));
        for at in [0, 7, 8] {
            let mut bad = rhs;
            bad[at] = f64::NAN;
            let previous = out;
            assert_eq!(f.solve_many_into(9, &bad, &mut out), Err(Error::NonFinite));
            assert_eq!(out, previous);
        }
    }
    let f = Factors {
        lower: &[],
        pivots: &[],
        normalized_upper: &[],
        reciprocal: &[],
    };
    f.solve_many_into(usize::MAX, &[], &mut []).unwrap();
    let p = [f64::from_bits(1); 2];
    let inv = [0.0; 2];
    let f = Factors {
        lower: &[0.0],
        pivots: &p,
        normalized_upper: &[0.0],
        reciprocal: &inv,
    };
    assert_eq!(
        f.solve_many_into(usize::MAX, &[], &mut []),
        Err(Error::Shape)
    );
    assert_eq!(
        f.solve_many_into(1, &[1.0, 1.0], &mut [0.0; 2]),
        Err(Error::Range)
    );
}

#[test]
fn reciprocal_rounding_can_overflow_where_division_succeeds() {
    let p = [0.9];
    let rhs = [f64::from_bits(0x7fec_cccc_cccc_cccc)];
    assert_eq!(rhs[0] / p[0], f64::MAX);
    let mut inv = [0.0];
    prepare(&p, &mut inv);
    let f = Factors {
        lower: &[],
        pivots: &p,
        normalized_upper: &[],
        reciprocal: &inv,
    };
    assert_eq!(f.solve_many_into(1, &rhs, &mut [0.0]), Err(Error::Range));
}

// Exactly manufactured dyadic recurrence: all pivots are 4 and normalized
// upper entries are 1/2. Integer intermediates are exactly representable.
// This catches a missing/wrong solve even if its loose certificate is valid.
#[test]
fn distinct_batched_integer_solutions_are_exact() {
    for n in [2_usize, 3, 17, 401] {
        let off = vec![2.0; n - 1];
        let mut diagonal = vec![5.0; n];
        diagonal[0] = 4.0;
        let a = DominantTridiagonal::new(&off, &diagonal, &off).unwrap();
        let mut p = vec![0.0; n];
        let mut u = vec![0.0; n - 1];
        a.factor_into(&mut p, &mut u).unwrap();
        let mut inv = vec![0.0; n];
        prepare(&p, &mut inv);
        let f = Factors {
            lower: &off,
            pivots: &p,
            normalized_upper: &u,
            reciprocal: &inv,
        };
        for count in [1, 2, 3, 4, 7, 8, 9, 17] {
            let exact: Vec<_> = (0..n * count)
                .map(|at| f64::from(i32::try_from((at * 7 + at / count * 3) % 23).unwrap() - 11))
                .collect();
            let rhs: Vec<_> = (0..n * count)
                .map(|at| {
                    let row = at / count;
                    diagonal[row] * exact[at]
                        + if row > 0 {
                            2.0 * exact[at - count]
                        } else {
                            0.0
                        }
                        + if row + 1 < n {
                            2.0 * exact[at + count]
                        } else {
                            0.0
                        }
                })
                .collect();
            let mut out = vec![0.0; n * count];
            f.solve_many_into(count, &rhs, &mut out).unwrap();
            assert_eq!(out, exact, "n={n} count={count}");
        }
    }
}
