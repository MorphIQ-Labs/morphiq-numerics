//! Independent exact-rational solution, residual and dominance checks.
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
fn tridiagonal_exact_solutions_and_residuals_are_inside_the_reported_bounds() {
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/tridiagonal.json")).unwrap();
    for case in fixture["cases"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let lower = vector(case, "lower");
        let diagonal = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let rhs = vector(case, "rhs");
        let a = DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap();
        let n = a.len();
        let mut pivots = vec![0.0; n];
        let mut normalized_upper = vec![0.0; n.saturating_sub(1)];
        let f = a.factor_into(&mut pivots, &mut normalized_upper).unwrap();
        let mut out = vec![0.0; n];
        f.solve_into(&rhs, &mut out).unwrap();
        // Check both the solver result and an unrelated candidate. The
        // certificate's theorem cannot depend on the candidate's algorithm.
        let mut candidates = vec![out, vec![0.25; n]];
        // Unrelated, nonconstant candidates are essential: an indexing error
        // can enlarge an almost-zero solver residual and still enclose it,
        // while a constant candidate hides which neighbour was selected.
        for seed in 0..20 {
            candidates.push(
                (0..n)
                    .map(|i| f64::from(i32::try_from((i * 17 + seed * 7) % 31).unwrap() - 15) / 8.0)
                    .collect(),
            );
        }
        for candidate in &candidates {
            let bound = f.certify(&rhs, candidate).unwrap();
            if n > 0 {
                assert!(
                    &Exact::of(bound.max_solution_error()) * &Exact::of(a.dominance_margin())
                        >= Exact::of(bound.max_residual()),
                    "outward quotient: {name}"
                );
            }
            for i in 0..n {
                let mut residual = &Exact::of(diagonal[i]) * &Exact::of(candidate[i]);
                let mut margin = Exact::of(diagonal[i]).abs();
                if i > 0 {
                    residual =
                        &residual + &(&Exact::of(lower[i - 1]) * &Exact::of(candidate[i - 1]));
                    margin = &margin - &Exact::of(lower[i - 1]).abs();
                }
                if i + 1 < n {
                    residual = &residual + &(&Exact::of(upper[i]) * &Exact::of(candidate[i + 1]));
                    margin = &margin - &Exact::of(upper[i]).abs();
                }
                assert!(Exact::of(a.dominance_margin()) <= margin, "{name}, row {i}");
                residual = &residual - &Exact::of(rhs[i]);
                assert!(
                    residual.abs() <= Exact::of(bound.max_residual()),
                    "residual: {name}, row {i}"
                );
                let numerator = integer(case["solution"][i][0].as_str().unwrap());
                let denominator = integer(case["solution"][i][1].as_str().unwrap());
                let error = &(&Exact::of(candidate[i]) * &denominator) - &numerator;
                assert!(
                    error.abs() <= &Exact::of(bound.max_solution_error()) * &denominator,
                    "solution: {name}, row {i}"
                );
            }
        }
    }
}

#[test]
fn tridiagonal_batched_solutions_have_independent_exact_error_bounds() {
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/tridiagonal.json")).unwrap();
    for case in fixture["cases"].as_array().unwrap() {
        let lower = vector(case, "lower");
        let diagonal = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let rhs = vector(case, "rhs");
        let n = diagonal.len();
        let mut p = vec![0.0; n];
        let mut c = vec![0.0; n.saturating_sub(1)];
        let f = DominantTridiagonal::new(&lower, &diagonal, &upper)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        // Signs and zero transform the independent exact solutions without
        // rounding the fixture inputs, including its subnormal cases.
        for count in [2, 3, 4, 7, 8, 9, 17] {
            let sign = |column: usize| i64::try_from(column % 3).unwrap() - 1;
            let interleaved: Vec<_> = (0..n * count)
                .map(|at| rhs[at / count] * (sign(at % count) as f64))
                .collect();
            let mut out = vec![0.0; interleaved.len()];
            f.solve_many_into(count, &interleaved, &mut out).unwrap();
            for column in 0..count {
                let b: Vec<_> = (0..n)
                    .map(|row| interleaved[row * count + column])
                    .collect();
                let x: Vec<_> = (0..n).map(|row| out[row * count + column]).collect();
                let mut scalar = vec![0.0; n];
                f.solve_into(&b, &mut scalar).unwrap();
                assert_eq!(
                    x.iter().map(|x| x.to_bits()).collect::<Vec<_>>(),
                    scalar.iter().map(|x| x.to_bits()).collect::<Vec<_>>()
                );
                let bound = f.certify(&b, &x).unwrap();
                for (row, &value) in x.iter().enumerate() {
                    let numerator = &integer(case["solution"][row][0].as_str().unwrap())
                        * &Exact::integer(sign(column));
                    let denominator = integer(case["solution"][row][1].as_str().unwrap());
                    let error = &(&Exact::of(value) * &denominator) - &numerator;
                    assert!(
                        error.abs() <= &Exact::of(bound.max_solution_error()) * &denominator,
                        "{} row={row} column={column} count={count}",
                        case["name"]
                    );
                }
            }
        }
    }
}

#[test]
fn sign_tridiagonal_exact_manufactured_results_and_arbitrary_residuals() {
    use morphiq_numerics::linalg::tridiagonal::SignTridiagonal;
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/tridiagonal_sign.json")).unwrap();
    for case in fixture["cases"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let lower = vector(case, "lower");
        let diagonal = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let rhs = vector(case, "rhs");
        let n = diagonal.len();
        let mut p = vec![0.; n];
        let mut c = vec![0.; n.saturating_sub(1)];
        let f = SignTridiagonal::new(&lower, &diagonal, &upper)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        for count in [1, 2, 3, 4, 7, 8, 9, 17] {
            let sign = |col: usize| i64::try_from(col % 3).unwrap() - 1;
            let b: Vec<_> = (0..n * count)
                .map(|at| rhs[at / count] * sign(at % count) as f64)
                .collect();
            let mut out = vec![0.; b.len()];
            f.solve_many_into(count, &b, &mut out).unwrap();
            for col in 0..count {
                let r: Vec<_> = (0..n).map(|i| b[i * count + col]).collect();
                let x: Vec<_> = (0..n).map(|i| out[i * count + col]).collect();
                let mut scalar = vec![0.; n];
                f.solve_into(&r, &mut scalar).unwrap();
                assert_eq!(
                    x.iter().map(|v| v.to_bits()).collect::<Vec<_>>(),
                    scalar.iter().map(|v| v.to_bits()).collect::<Vec<_>>()
                );
                if name.starts_with("exact-manufactured") {
                    for (i, &value) in x.iter().enumerate() {
                        let numerator = &integer(case["solution"][i][0].as_str().unwrap())
                            * &Exact::integer(sign(col));
                        let denominator = integer(case["solution"][i][1].as_str().unwrap());
                        assert_eq!(
                            &Exact::of(value) * &denominator,
                            numerator,
                            "{name}/{col}/{i}"
                        );
                    }
                }
                for candidate in [
                    x,
                    (0..n)
                        .map(|i| f64::from(i32::try_from(i % 13).unwrap()) / 4. - 1.)
                        .collect(),
                ] {
                    let cert = f.certify_residual(&r, &candidate).unwrap();
                    for i in 0..n {
                        let mut residual = &Exact::of(diagonal[i]) * &Exact::of(candidate[i]);
                        if i > 0 {
                            residual = &residual
                                + &(&Exact::of(lower[i - 1]) * &Exact::of(candidate[i - 1]));
                        }
                        if i + 1 < n {
                            residual =
                                &residual + &(&Exact::of(upper[i]) * &Exact::of(candidate[i + 1]));
                        }
                        residual = &residual - &Exact::of(r[i]);
                        assert!(
                            residual.abs() <= Exact::of(cert.max_residual()),
                            "{name}/{col}/{i}"
                        );
                    }
                }
            }
        }
        // Once immutable factors cease being used, their buffers are observable.
        for (pivot, d) in p.iter().zip(&diagonal) {
            assert!(pivot >= d, "{name}");
        }
    }
}

#[test]
fn unpivoted_tridiagonal_exact_manufactured_results_and_arbitrary_residuals() {
    use morphiq_numerics::linalg::tridiagonal::UnpivotedTridiagonal;
    let fixture: Value =
        serde_json::from_str(include_str!("../fixtures/tridiagonal_unpivoted.json")).unwrap();
    for case in fixture["cases"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let lower = vector(case, "lower");
        let diagonal = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let rhs = vector(case, "rhs");
        let n = diagonal.len();
        let mut p = vec![0.; n];
        let mut c = vec![0.; n.saturating_sub(1)];
        let f = UnpivotedTridiagonal::new(&lower, &diagonal, &upper)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        for count in [1, 2, 3, 4, 7, 8, 9, 17] {
            let sign = |col: usize| i64::try_from(col % 3).unwrap() - 1;
            let b: Vec<_> = (0..n * count)
                .map(|at| rhs[at / count] * sign(at % count) as f64)
                .collect();
            let mut out = vec![0.; b.len()];
            f.solve_many_into(count, &b, &mut out).unwrap();
            for col in 0..count {
                let r: Vec<_> = (0..n).map(|i| b[i * count + col]).collect();
                let x: Vec<_> = (0..n).map(|i| out[i * count + col]).collect();
                let mut scalar = vec![0.; n];
                f.solve_into(&r, &mut scalar).unwrap();
                assert_eq!(
                    x.iter().map(|v| v.to_bits()).collect::<Vec<_>>(),
                    scalar.iter().map(|v| v.to_bits()).collect::<Vec<_>>()
                );
                if name.starts_with("exact-manufactured") {
                    for (i, &value) in x.iter().enumerate() {
                        let numerator = &integer(case["solution"][i][0].as_str().unwrap())
                            * &Exact::integer(sign(col));
                        let denominator = integer(case["solution"][i][1].as_str().unwrap());
                        assert_eq!(
                            &Exact::of(value) * &denominator,
                            numerator,
                            "{name}/{col}/{i}"
                        );
                    }
                }
                for candidate in [
                    x,
                    (0..n)
                        .map(|i| f64::from(i32::try_from(i % 13).unwrap()) / 4. - 1.)
                        .collect(),
                ] {
                    let cert = f.certify_residual(&r, &candidate).unwrap();
                    for i in 0..n {
                        let mut residual = &Exact::of(diagonal[i]) * &Exact::of(candidate[i]);
                        if i > 0 {
                            residual = &residual
                                + &(&Exact::of(lower[i - 1]) * &Exact::of(candidate[i - 1]));
                        }
                        if i + 1 < n {
                            residual =
                                &residual + &(&Exact::of(upper[i]) * &Exact::of(candidate[i + 1]));
                        }
                        residual = &residual - &Exact::of(r[i]);
                        assert!(
                            residual.abs() <= Exact::of(cert.max_residual()),
                            "{name}/{col}/{i}"
                        );
                    }
                }
            }
        }
        let minimum = f.min_abs_pivot();
        assert_eq!(minimum, p.iter().map(|p| p.abs()).reduce(f64::min));
    }
    for case in fixture["refused"].as_array().unwrap() {
        let lower = vector(case, "lower");
        let diagonal = vector(case, "diagonal");
        let upper = vector(case, "upper");
        let matrix = UnpivotedTridiagonal::new(&lower, &diagonal, &upper).unwrap();
        assert_eq!(
            matrix.factor_into(&mut [0.; 2], &mut [0.]).unwrap_err(),
            morphiq_numerics::linalg::tridiagonal::Error::ZeroPivot(0)
        );
    }
}
