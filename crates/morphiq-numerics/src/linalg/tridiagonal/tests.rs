use super::*;

#[test]
fn empty_and_singleton_include_signed_zero_and_subnormals() {
    let a = DominantTridiagonal::new(&[], &[], &[]).unwrap();
    assert!(a.is_empty());
    assert_eq!(a.dominance_margin(), 0.0);
    let factors = a.factor_into(&mut [], &mut []).unwrap();
    factors.solve_into(&[], &mut []).unwrap();
    assert_eq!(
        factors.certify(&[], &[]).unwrap(),
        Certificate {
            residual: 0.0,
            error: 0.0
        }
    );
    for d in [f64::from_bits(1), f64::MIN_POSITIVE, 1.0, -1.0, f64::MAX] {
        let diagonal = [d];
        let a = DominantTridiagonal::new(&[], &diagonal, &[]).unwrap();
        assert_eq!(a.dominance_margin(), d.abs());
        let mut pivots = [0.0];
        let factors = a.factor_into(&mut pivots, &mut []).unwrap();
        let mut out = [42.0];
        factors.solve_into(&[d], &mut out).unwrap();
        assert_eq!(out, [1.0]);
        factors.solve_into(&[-0.0], &mut out).unwrap();
        assert_eq!(out[0].to_bits(), (-0.0 / d).to_bits());
    }
}

#[test]
fn repeated_right_hand_sides_use_the_same_factors() {
    let a = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
    let mut pivots = [0.0; 2];
    let mut upper = [0.0];
    let factors = a.factor_into(&mut pivots, &mut upper).unwrap();
    for (rhs, expected) in [
        ([3.0, 3.0], [1.0, 1.0]),
        ([0.0, 3.0], [-1.0, 2.0]),
        ([-3.0, -3.0], [-1.0, -1.0]),
    ] {
        let mut out = [f64::NAN; 2];
        factors.solve_into(&rhs, &mut out).unwrap();
        assert_eq!(out, expected);
        let bound = factors.certify(&rhs, &out).unwrap();
        assert!(bound.max_residual() > 0.0);
        assert!(bound.max_solution_error() >= bound.max_residual());
        let mut fresh_pivots = [0.0; 2];
        let mut fresh_upper = [0.0];
        let fresh = a.factor_into(&mut fresh_pivots, &mut fresh_upper).unwrap();
        let mut direct = [0.0; 2];
        fresh.solve_into(&rhs, &mut direct).unwrap();
        assert_eq!(out.map(f64::to_bits), direct.map(f64::to_bits));
    }
}

#[test]
fn exact_integer_systems_exercise_unequal_off_diagonals_and_interior_rows() {
    let a = DominantTridiagonal::new(&[2.0], &[4.0, 4.0], &[1.0]).unwrap();
    let mut p = [0.0; 2];
    let mut c = [0.0];
    let f = a.factor_into(&mut p, &mut c).unwrap();
    let mut out = [0.0; 2];
    f.solve_into(&[6.0, 10.0], &mut out).unwrap();
    assert_eq!(out, [1.0, 2.0]);

    // The exact pivots are all 4 and normalized upper entries are 1/2.
    // Integer solutions and dyadic intermediates fit binary64 exactly;
    // equality here is justified, not a sampled accuracy tolerance.
    for n in [3, 17, 401] {
        let lower = std::vec![2.0; n - 1];
        let upper = std::vec![2.0; n - 1];
        let mut diagonal = std::vec![5.0; n];
        diagonal[0] = 4.0;
        let expected: std::vec::Vec<_> = (0..n)
            .map(|i| f64::from(i32::try_from(i % 13).unwrap() - 6))
            .collect();
        let rhs: std::vec::Vec<_> = (0..n)
            .map(|i| {
                diagonal[i] * expected[i]
                    + if i > 0 { 2.0 * expected[i - 1] } else { 0.0 }
                    + if i + 1 < n {
                        2.0 * expected[i + 1]
                    } else {
                        0.0
                    }
            })
            .collect();
        let a = DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap();
        let mut p = std::vec![0.0; n];
        let mut c = std::vec![0.0; n - 1];
        let f = a.factor_into(&mut p, &mut c).unwrap();
        let mut out = std::vec![0.0; n];
        f.solve_into(&rhs, &mut out).unwrap();
        assert_eq!(out, expected);
    }
}

#[test]
fn new_matrix_requires_new_factors_after_borrows_end() {
    let mut diagonal = [2.0];
    let mut pivots = [0.0];
    let mut out = [0.0];
    DominantTridiagonal::new(&[], &diagonal, &[])
        .unwrap()
        .factor_into(&mut pivots, &mut [])
        .unwrap()
        .solve_into(&[6.0], &mut out)
        .unwrap();
    assert_eq!(out, [3.0]);
    diagonal[0] = 3.0;
    DominantTridiagonal::new(&[], &diagonal, &[])
        .unwrap()
        .factor_into(&mut pivots, &mut [])
        .unwrap()
        .solve_into(&[6.0], &mut out)
        .unwrap();
    assert_eq!(out, [2.0]);
}

#[test]
fn admission_distinguishes_shape_nonfinite_and_unsupported_domain() {
    // An irrelevant upper interval endpoint must not reject a finite lower
    // dominance bound at the largest finite diagonal.
    assert!(DominantTridiagonal::new(&[1.0], &[f64::MAX; 2], &[1.0]).is_ok());
    // 1 - 2^-54 rounds upward to 1 in nearest mode. A raw subtraction is
    // therefore not a valid lower bound on this exact row margin.
    let tiny = [f64::EPSILON / 4.0];
    assert_eq!(
        DominantTridiagonal::new(&tiny, &[1.0; 2], &tiny)
            .unwrap()
            .dominance_margin(),
        1.0_f64.next_down()
    );
    for (l, d, u) in [
        (&[1.0][..], &[][..], &[][..]),
        (&[][..], &[2.0, 2.0][..], &[1.0][..]),
        (&[1.0][..], &[2.0, 2.0][..], &[][..]),
    ] {
        assert_eq!(DominantTridiagonal::new(l, d, u).unwrap_err(), Error::Shape);
    }
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        for (l, d, u) in [
            ([bad], [2.0, 2.0], [1.0]),
            ([1.0], [2.0, bad], [1.0]),
            ([1.0], [2.0, 2.0], [bad]),
        ] {
            assert_eq!(
                DominantTridiagonal::new(&l, &d, &u).unwrap_err(),
                Error::NonFinite
            );
        }
    }
    for zero in [0.0, -0.0] {
        assert_eq!(
            DominantTridiagonal::new(&[], &[zero], &[]).unwrap_err(),
            Error::NotDominant(0)
        );
    }
    // Nonsingular, but requires pivoting; equality and an interior failing row.
    assert_eq!(
        DominantTridiagonal::new(&[1.0], &[0.0, 1.0], &[1.0]).unwrap_err(),
        Error::NotDominant(0)
    );
    assert_eq!(
        DominantTridiagonal::new(&[1.0], &[2.0, 1.0], &[1.0]).unwrap_err(),
        Error::NotDominant(1)
    );
    assert_eq!(
        DominantTridiagonal::new(&[1.0, 1.0], &[2.0, 2.0, 2.0], &[1.0, 1.0]).unwrap_err(),
        Error::NotDominant(1)
    );
    assert!(
        DominantTridiagonal::new(&[1.0], &[1.0_f64.next_up(), 1.0_f64.next_up()], &[1.0]).is_ok()
    );
    // Conservative subtraction loses the one-subnormal margin.
    assert_eq!(
        DominantTridiagonal::new(
            &[f64::from_bits(1)],
            &[f64::from_bits(2); 2],
            &[f64::from_bits(1)]
        )
        .unwrap_err(),
        Error::NotDominant(0)
    );
}

#[test]
fn argument_errors_leave_workspaces_unchanged() {
    let a = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
    for (np, nu) in [(1, 1), (3, 1), (2, 0), (2, 2)] {
        let mut p = std::vec![42.0; np];
        let mut u = std::vec![43.0; nu];
        assert_eq!(a.factor_into(&mut p, &mut u).unwrap_err(), Error::Shape);
        assert!(p.iter().all(|&x| x == 42.0));
        assert!(u.iter().all(|&x| x == 43.0));
    }
    let mut p = [0.0; 2];
    let mut u = [0.0];
    let f = a.factor_into(&mut p, &mut u).unwrap();
    let mut out = [42.0; 2];
    assert_eq!(f.solve_into(&[1.0], &mut out), Err(Error::Shape));
    assert_eq!(out, [42.0; 2]);
    assert_eq!(f.solve_into(&[1.0; 2], &mut out[..1]), Err(Error::Shape));
    assert_eq!(out, [42.0; 2]);
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(f.solve_into(&[1.0, bad], &mut out), Err(Error::NonFinite));
        assert_eq!(out, [42.0; 2]);
        assert_eq!(f.certify(&[1.0, bad], &[0.0; 2]), Err(Error::NonFinite));
        assert_eq!(f.certify(&[1.0; 2], &[0.0, bad]), Err(Error::NonFinite));
    }
    assert_eq!(f.certify(&[1.0], &[0.0; 2]), Err(Error::Shape));
    assert_eq!(f.certify(&[1.0; 2], &[0.0]), Err(Error::Shape));
}

#[test]
fn intermediate_overflow_is_an_explicit_error() {
    let a = DominantTridiagonal::new(&[-f64::MAX / 2.0], &[2.0, f64::MAX], &[1.0]).unwrap();
    assert_eq!(
        a.factor_into(&mut [0.0; 2], &mut [0.0]).unwrap_err(),
        Error::Range
    );
    let tiny = [f64::from_bits(1)];
    let a = DominantTridiagonal::new(&[], &tiny, &[]).unwrap();
    let mut p = [0.0];
    let f = a.factor_into(&mut p, &mut []).unwrap();
    assert_eq!(f.solve_into(&[1.0], &mut [0.0]), Err(Error::Range));
    assert_eq!(f.certify(&[1.0], &[0.0]), Err(Error::Range));
    let a = DominantTridiagonal::new(&[], &[f64::MAX], &[]).unwrap();
    let mut p = [0.0];
    let f = a.factor_into(&mut p, &mut []).unwrap();
    assert_eq!(f.certify(&[f64::MAX], &[1.0]), Err(Error::Range));
}

#[test]
fn certificate_is_for_the_candidate_and_can_report_large_error() {
    let a = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
    let mut p = [0.0; 2];
    let mut u = [0.0];
    let f = a.factor_into(&mut p, &mut u).unwrap();
    let certificate = f.certify(&[3.0, 3.0], &[0.0, 0.0]).unwrap();
    assert!(certificate.max_residual() >= 3.0);
    assert!(certificate.max_solution_error() >= 3.0);
}

// Every column has a different exactly manufactured integer solution. Exact
// dyadic pivots (4) and upper coefficients (1/2) make equality an independent
// oracle, rather than a second transcription of the floating-point solver.
fn batch_integer_case(n: usize, count: usize) -> (std::vec::Vec<f64>, std::vec::Vec<f64>) {
    let expected: std::vec::Vec<_> = (0..n * count)
        .map(|i| f64::from(i32::try_from((i * 7 + i / count * 3) % 23).unwrap() - 11))
        .collect();
    let rhs = (0..n * count)
        .map(|at| {
            let row = at / count;
            (if row == 0 { 4.0 } else { 5.0 }) * expected[at]
                + if row > 0 {
                    2.0 * expected[at - count]
                } else {
                    0.0
                }
                + if row + 1 < n {
                    2.0 * expected[at + count]
                } else {
                    0.0
                }
        })
        .collect();
    (rhs, expected)
}

#[test]
fn batches_have_independent_exact_solutions_and_scalar_bits() {
    for n in [0_usize, 1, 2, 3, 17, 401] {
        let off = std::vec![2.0; n.saturating_sub(1)];
        let mut diagonal = std::vec![5.0; n];
        if n > 0 {
            diagonal[0] = 4.0;
        }
        let mut p = std::vec![0.0; n];
        let mut c = std::vec![0.0; n.saturating_sub(1)];
        let f = DominantTridiagonal::new(&off, &diagonal, &off)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        for count in [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 65] {
            let (rhs, expected) = batch_integer_case(n, count);
            let mut out = std::vec![f64::NAN; rhs.len()];
            f.solve_many_into(count, &rhs, &mut out).unwrap();
            assert_eq!(out, expected, "n={n}, count={count}");
        }
    }
}

#[test]
fn batch_validation_is_atomic_and_handles_empty_dimensions() {
    let mut p = [0.0; 2];
    let mut c = [0.0];
    let f = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0])
        .unwrap()
        .factor_into(&mut p, &mut c)
        .unwrap();
    let mut out = [42.0; 18];
    assert_eq!(
        f.solve_many_into(usize::MAX, &[], &mut out),
        Err(Error::Shape)
    );
    assert_eq!(
        f.solve_many_into(9, &[1.0; 17], &mut out),
        Err(Error::Shape)
    );
    assert_eq!(
        f.solve_many_into(9, &[1.0; 18], &mut out[..17]),
        Err(Error::Shape)
    );
    assert_eq!(out, [42.0; 18]);
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        for at in [0, 7, 8, 17] {
            let mut rhs = [1.0; 18];
            rhs[at] = bad;
            assert_eq!(f.solve_many_into(9, &rhs, &mut out), Err(Error::NonFinite));
            assert_eq!(out, [42.0; 18]);
        }
    }
    f.solve_many_into(0, &[], &mut []).unwrap();
    assert_eq!(f.solve_many_into(0, &[], &mut out), Err(Error::Shape));
    DominantTridiagonal::new(&[], &[], &[])
        .unwrap()
        .factor_into(&mut [], &mut [])
        .unwrap()
        .solve_many_into(usize::MAX, &[], &mut [])
        .unwrap();
}

#[test]
fn batch_signed_zero_subnormal_and_mixed_lane_overflow() {
    for d in [1.0, -1.0, f64::from_bits(1), -f64::from_bits(1)] {
        let diagonal = [d];
        let mut p = [0.0];
        let f = DominantTridiagonal::new(&[], &diagonal, &[])
            .unwrap()
            .factor_into(&mut p, &mut [])
            .unwrap();
        let rhs = [0.0, -0.0, d, -d, d, -0.0, d, 0.0, -d];
        let mut out = [0.0; 9];
        f.solve_many_into(9, &rhs, &mut out).unwrap();
        assert_eq!(out.map(f64::to_bits), rhs.map(|x| (x / d).to_bits()));
        if d.abs() < f64::MIN_POSITIVE {
            for at in 0..9 {
                let mut bad = rhs;
                bad[at] = 1.0;
                assert_eq!(f.solve_many_into(9, &bad, &mut out), Err(Error::Range));
            }
        }
    }
    // Forward sweep is finite; subtraction in back substitution overflows.
    let mut p = [0.0; 2];
    let mut c = [0.0];
    let f = DominantTridiagonal::new(&[0.0], &[1.0, 1.0], &[0.5])
        .unwrap()
        .factor_into(&mut p, &mut c)
        .unwrap();
    for column in 0..9 {
        let mut rhs = [0.0; 18];
        rhs[column] = f64::MAX;
        rhs[9 + column] = -f64::MAX;
        assert_eq!(
            f.solve_many_into(9, &rhs, &mut [0.0; 18]),
            Err(Error::Range)
        );
    }
}

#[cfg(feature = "simd")]
#[test]
fn lanes_batches_match_each_forced_backend() {
    use morphiq_numerics_arch::{Simd, WithSimd};
    struct Check;
    impl WithSimd for Check {
        type Output = ();
        fn with<K: Simd>(self, k: K) {
            for n in [0_usize, 1, 2, 17, 401] {
                for scale in [1.0, -1.0, f64::MIN_POSITIVE / 16.0, 1e270] {
                    let lower = std::vec![-scale; n.saturating_sub(1)];
                    let upper = std::vec![0.5 * scale; n.saturating_sub(1)];
                    let diagonal = std::vec![4.0 * scale; n];
                    let mut p = std::vec![0.0; n];
                    let mut c = std::vec![0.0; n.saturating_sub(1)];
                    let f = DominantTridiagonal::new(&lower, &diagonal, &upper)
                        .unwrap()
                        .factor_into(&mut p, &mut c)
                        .unwrap();
                    for count in [1, 2, 3, 4, 5, 7, 8, 9, 17] {
                        let rhs: std::vec::Vec<_> = (0..n * count)
                            .map(|i| f64::from(i32::try_from((i * 7) % 19).unwrap() - 9) * scale)
                            .collect();
                        let mut out = std::vec![f64::NAN; rhs.len()];
                        let end = k
                            .vectorize(&mut lanes::Batch {
                                factors: &f.factors,
                                count,
                                rhs: &rhs,
                                out: &mut out,
                                start: 0,
                            })
                            .unwrap();
                        f.factors.solve_columns(count, &rhs, &mut out, end).unwrap();
                        for column in 0..count {
                            let single: std::vec::Vec<_> =
                                (0..n).map(|row| rhs[row * count + column]).collect();
                            let mut expected = std::vec![0.0; n];
                            f.solve_into(&single, &mut expected).unwrap();
                            for row in 0..n {
                                assert_eq!(
                                    out[row * count + column].to_bits(),
                                    expected[row].to_bits(),
                                    "{}: n={n} count={count} row={row} column={column}",
                                    K::NAME
                                );
                            }
                        }
                    }
                }
            }
            // A non-dominant sign-domain system with exact manufactured solutions.
            for n in [2_usize, 3, 17, 401] {
                let lower = std::vec![-2.0; n-1];
                let upper = std::vec![1.0; n-1];
                let mut diagonal = std::vec![1.0; n];
                diagonal[0] = 2.0;
                let mut p = std::vec![0.0; n];
                let mut c = std::vec![0.0; n-1];
                let f = SignTridiagonal::new(&lower, &diagonal, &upper)
                    .unwrap()
                    .factor_into(&mut p, &mut c)
                    .unwrap();
                for count in [1, 2, 3, 4, 7, 8, 9, 17] {
                    let exact = |row: usize, col: usize| {
                        f64::from(i32::try_from((row * 7 + col * 3) % 19).unwrap() - 9)
                    };
                    let rhs: std::vec::Vec<_> = (0..n * count)
                        .map(|at| {
                            let row = at / count;
                            let col = at % count;
                            diagonal[row] * exact(row, col)
                                + if row > 0 {
                                    -2. * exact(row - 1, col)
                                } else {
                                    0.
                                }
                                + if row + 1 < n { exact(row + 1, col) } else { 0. }
                        })
                        .collect();
                    let mut out = std::vec![f64::NAN;rhs.len()];
                    let end = k
                        .vectorize(&mut lanes::Batch {
                            factors: &f.factors,
                            count,
                            rhs: &rhs,
                            out: &mut out,
                            start: 0,
                        })
                        .unwrap();
                    f.factors.solve_columns(count, &rhs, &mut out, end).unwrap();
                    for row in 0..n {
                        for col in 0..count {
                            assert_eq!(out[row * count + col], exact(row, col), "{}", K::NAME);
                        }
                    }
                }
            }
            // Negative pivots exercise the general contract on each forced backend.
            for n in [2_usize, 3, 17, 401] {
                let lower = std::vec![2.0; n-1];
                let upper = std::vec![-1.0; n-1];
                let mut diagonal = std::vec![-1.0; n];
                diagonal[0] = -2.0;
                let mut p = std::vec![0.0; n];
                let mut c = std::vec![0.0; n-1];
                let f = UnpivotedTridiagonal::new(&lower, &diagonal, &upper)
                    .unwrap()
                    .factor_into(&mut p, &mut c)
                    .unwrap();
                for count in [1, 2, 3, 4, 7, 8, 9, 17] {
                    let exact = |row: usize, col: usize| {
                        f64::from(i32::try_from((row * 7 + col * 3) % 19).unwrap() - 9)
                    };
                    let rhs: std::vec::Vec<_> = (0..n * count)
                        .map(|at| {
                            let row = at / count;
                            let col = at % count;
                            diagonal[row] * exact(row, col)
                                + if row > 0 {
                                    2. * exact(row - 1, col)
                                } else {
                                    0.
                                }
                                + if row + 1 < n {
                                    -exact(row + 1, col)
                                } else {
                                    0.
                                }
                        })
                        .collect();
                    let mut out = std::vec![f64::NAN;rhs.len()];
                    let end = k
                        .vectorize(&mut lanes::Batch {
                            factors: &f.factors,
                            count,
                            rhs: &rhs,
                            out: &mut out,
                            start: 0,
                        })
                        .unwrap();
                    f.factors.solve_columns(count, &rhs, &mut out, end).unwrap();
                    for row in 0..n {
                        for col in 0..count {
                            assert_eq!(out[row * count + col], exact(row, col), "{}", K::NAME);
                        }
                    }
                }
            }
            // One failing lane must reject the group on every backend, even
            // if other lanes have finite results. Include every lane position.
            let mut p = [0.0];
            let diagonal = [f64::from_bits(1)];
            let f = DominantTridiagonal::new(&[], &diagonal, &[])
                .unwrap()
                .factor_into(&mut p, &mut [])
                .unwrap();
            for at in 0..K::LANES {
                let mut rhs = std::vec![0.0; K::LANES];
                rhs[at] = 1.0;
                let mut out = std::vec![0.0; K::LANES];
                assert_eq!(
                    k.vectorize(&mut lanes::Batch {
                        factors: &f.factors,
                        count: K::LANES,
                        rhs: &rhs,
                        out: &mut out,
                        start: 0,
                    }),
                    Err(Error::Range)
                );
            }
        }
    }
    for backend in crate::lanes::tests::backends() {
        backend.vectorize(Check);
    }
}

#[test]
fn sign_domain_checks_exact_signs_without_product_underflow_or_overflow() {
    for n in 0_usize..4 {
        let diagonal = [1.0; 3];
        let off = [0.0; 2];
        let a = SignTridiagonal::new(
            &off[..n.saturating_sub(1)],
            &diagonal[..n],
            &off[..n.saturating_sub(1)],
        )
        .unwrap();
        assert_eq!(a.len(), n);
        assert_eq!(a.is_empty(), n == 0);
    }

    let tiny = f64::from_bits(1);
    for d in [-1.0, -tiny, 0.0, -0.0] {
        assert!(matches!(
            SignTridiagonal::new(&[], &[d], &[]),
            Err(Error::NonPositiveDiagonal(0))
        ));
    }
    for (l, u) in [
        (tiny, tiny),
        (-tiny, -tiny),
        (f64::MAX, f64::MAX),
        (-1., -2.),
    ] {
        assert!(matches!(
            SignTridiagonal::new(&[l], &[1.; 2], &[u]),
            Err(Error::SameSignLink(0))
        ));
    }
    for (l, u) in [
        (tiny, -tiny),
        (-tiny, tiny),
        (f64::MAX, -f64::MAX),
        (0., 2.),
        (-0., -2.),
        (2., -0.),
        (-2., 0.),
        (2., 0.),
        (-2., -0.),
    ] {
        assert!(SignTridiagonal::new(&[l], &[1.; 2], &[u]).is_ok());
    }
    assert!(matches!(
        SignTridiagonal::new(&[], &[1.; 2], &[]),
        Err(Error::Shape)
    ));
    for bad in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        for (l, d, u) in [(bad, 1., -1.), (-1., bad, 1.), (-1., 1., bad)] {
            assert!(matches!(
                SignTridiagonal::new(&[l], &[1., d], &[u]),
                Err(Error::NonFinite)
            ));
        }
    }
    assert!(matches!(
        SignTridiagonal::new(&[-1., 1.], &[1.; 3], &[1., 1.]),
        Err(Error::SameSignLink(1))
    ));
    assert!(matches!(
        SignTridiagonal::new(&[-1.; 2], &[1., 0., 1.], &[1.; 2]),
        Err(Error::NonPositiveDiagonal(1))
    ));
}

#[test]
fn sign_factors_range_validation_empty_and_subnormal_behavior() {
    let tiny = f64::from_bits(1);
    let mut p = [7.; 2];
    let mut c = [7.];
    let a = SignTridiagonal::new(&[-1.], &[1.; 2], &[1.]).unwrap();
    assert!(matches!(
        a.factor_into(&mut p[..1], &mut c),
        Err(Error::Shape)
    ));
    assert_eq!(p, [7.; 2]);
    assert_eq!(c, [7.]);
    for (l, d, u) in [
        (-1., [tiny, 1.], 1.),
        (-f64::MAX, [1., f64::MAX], 1.),
        (-f64::MAX, [1., 1.], 2.),
    ] {
        assert!(matches!(
            SignTridiagonal::new(&[l], &d, &[u])
                .unwrap()
                .factor_into(&mut p, &mut c),
            Err(Error::Range)
        ));
    }
    let diag = [tiny];
    let mut p = [0.];
    let f = SignTridiagonal::new(&[], &diag, &[])
        .unwrap()
        .factor_into(&mut p, &mut [])
        .unwrap();
    let mut out = [9.];
    for r in [tiny, 0., -0.] {
        f.solve_into(&[r], &mut out).unwrap();
        assert_eq!(out[0].to_bits(), (r / tiny).to_bits());
    }
    assert_eq!(f.solve_into(&[1.], &mut out), Err(Error::Range));
    assert!(
        f.certify_residual(&[0.], &[f64::MAX])
            .unwrap()
            .max_residual()
            .is_finite()
    );
    out = [9.];
    assert_eq!(
        f.solve_many_into(1, &[f64::NAN], &mut out),
        Err(Error::NonFinite)
    );
    assert_eq!(out, [9.]);
    assert_eq!(f.solve_into(&[], &mut out), Err(Error::Shape));
    assert_eq!(out, [9.]);
    assert_eq!(f.certify_residual(&[], &out), Err(Error::Shape));
    assert_eq!(f.certify_residual(&[f64::NAN], &out), Err(Error::NonFinite));
    let mut p = [];
    let f = SignTridiagonal::new(&[], &[], &[])
        .unwrap()
        .factor_into(&mut p, &mut [])
        .unwrap();
    f.solve_many_into(usize::MAX, &[], &mut []).unwrap();
    assert_eq!(f.certify_residual(&[], &[]).unwrap().max_residual(), 0.);
    let mut p = [0.];
    let f = SignTridiagonal::new(&[], &[f64::MAX], &[])
        .unwrap()
        .factor_into(&mut p, &mut [])
        .unwrap();
    assert_eq!(f.certify_residual(&[0.], &[2.]), Err(Error::Range));
}

#[test]
fn domains_share_result_bits_and_residual_enclosures_on_their_intersection() {
    for scale in [f64::MIN_POSITIVE / 16., 1., 1e270] {
        let lower = [-scale, 0.5 * scale];
        let upper = [0.5 * scale, -scale];
        let diagonal = [4. * scale; 3];
        let mut p = [0.; 3];
        let mut c = [0.; 2];
        let mut q = p;
        let mut d = c;
        let dominant = DominantTridiagonal::new(&lower, &diagonal, &upper)
            .unwrap()
            .factor_into(&mut p, &mut c)
            .unwrap();
        let sign = SignTridiagonal::new(&lower, &diagonal, &upper)
            .unwrap()
            .factor_into(&mut q, &mut d)
            .unwrap();
        for rhs in [[scale, -scale, 2. * scale], [0., -0., scale]] {
            let mut x = [0.; 3];
            let mut y = x;
            dominant.solve_into(&rhs, &mut x).unwrap();
            sign.solve_into(&rhs, &mut y).unwrap();
            assert_eq!(x.map(f64::to_bits), y.map(f64::to_bits));
            assert_eq!(
                dominant.certify(&rhs, &x).unwrap().max_residual(),
                sign.certify_residual(&rhs, &x).unwrap().max_residual()
            );
        }
        assert_eq!(p.map(f64::to_bits), q.map(f64::to_bits));
        assert_eq!(c.map(f64::to_bits), d.map(f64::to_bits));
    }
}

#[test]
fn unpivoted_admission_is_finite_shape_only_and_factorization_checks_breakdown() {
    for (l, d, u, error) in [
        (&[1.][..], &[][..], &[][..], Error::Shape),
        (&[][..], &[][..], &[1.][..], Error::Shape),
        (&[][..], &[f64::NAN][..], &[][..], Error::NonFinite),
        (
            &[f64::INFINITY][..],
            &[1., 2.][..],
            &[1.][..],
            Error::NonFinite,
        ),
        (
            &[1.][..],
            &[1., 2.][..],
            &[f64::NEG_INFINITY][..],
            Error::NonFinite,
        ),
    ] {
        assert_eq!(UnpivotedTridiagonal::new(l, d, u).unwrap_err(), error);
    }
    for (l, d, u, error) in [
        ([1.], [0., 1.], [1.], Error::ZeroPivot(0)),
        ([1.], [1., 1.], [1.], Error::ZeroPivot(1)),
        ([0.], [f64::from_bits(1), 1.], [f64::MAX], Error::Range),
        ([f64::MAX], [1., 1.], [2.], Error::Range),
    ] {
        let matrix = UnpivotedTridiagonal::new(&l, &d, &u).unwrap();
        assert_eq!(
            matrix.factor_into(&mut [0.; 2], &mut [0.]).unwrap_err(),
            error
        );
    }
    let matrix = UnpivotedTridiagonal::new(&[], &[], &[]).unwrap();
    assert!(matrix.is_empty());
    let f = matrix.factor_into(&mut [], &mut []).unwrap();
    assert_eq!(f.min_abs_pivot(), None);
    f.solve_many_into(usize::MAX, &[], &mut []).unwrap();
    assert_eq!(f.certify_residual(&[], &[]).unwrap().max_residual(), 0.);
}

#[test]
fn unpivoted_negative_pivots_repeated_rhs_and_refusals_are_explicit() {
    let matrix = UnpivotedTridiagonal::new(&[1.], &[-2., 0.], &[1.]).unwrap();
    assert_eq!(matrix.len(), 2);
    assert!(!matrix.is_empty());
    let mut p = [42.; 2];
    let mut c = [42.];
    assert_eq!(
        matrix.factor_into(&mut p, &mut []).unwrap_err(),
        Error::Shape
    );
    assert_eq!(p, [42.; 2]);
    let f = matrix.factor_into(&mut p, &mut c).unwrap();
    assert_eq!(f.min_abs_pivot(), Some(0.5));
    for (rhs, expected) in [([0., 1.], [1., 2.]), ([1., -2.], [-2., -3.])] {
        let mut out = [42.; 2];
        f.solve_into(&rhs, &mut out).unwrap();
        assert_eq!(out, expected);
    }
    let mut out = [42.; 2];
    assert_eq!(f.solve_into(&[], &mut out), Err(Error::Shape));
    assert_eq!(out, [42.; 2]);
    assert_eq!(
        f.solve_into(&[0., f64::NAN], &mut out),
        Err(Error::NonFinite)
    );
    assert_eq!(out, [42.; 2]);
    assert_eq!(
        f.solve_many_into(usize::MAX, &[], &mut out),
        Err(Error::Shape)
    );
    assert_eq!(
        f.solve_many_into(1, &[f64::INFINITY, 0.], &mut out),
        Err(Error::NonFinite)
    );
    assert_eq!(f.certify_residual(&[], &[]), Err(Error::Shape));
    assert_eq!(
        f.certify_residual(&[0.; 2], &[f64::NAN, 0.]),
        Err(Error::NonFinite)
    );
    let tiny = [f64::from_bits(1)];
    let mut p = [0.];
    let f = UnpivotedTridiagonal::new(&[], &tiny, &[])
        .unwrap()
        .factor_into(&mut p, &mut [])
        .unwrap();
    assert_eq!(f.min_abs_pivot(), Some(tiny[0]));
    assert_eq!(f.solve_into(&[1.], &mut [0.]), Err(Error::Range));
    assert_eq!(
        f.solve_many_into(9, &[1.; 9], &mut [0.; 9]),
        Err(Error::Range)
    );
}

#[test]
fn finite_preflight_covers_vector_tails_and_preserves_outputs() {
    const N: usize = 33;
    for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        for band in 0..3 {
            for index in 0..if band == 1 { N } else { N - 1 } {
                let mut lower = [0.; N - 1];
                let mut diagonal = [2.; N];
                let mut upper = [0.; N - 1];
                match band {
                    0 => lower[index] = invalid,
                    1 => diagonal[index] = invalid,
                    _ => upper[index] = invalid,
                }
                assert_eq!(
                    DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap_err(),
                    Error::NonFinite
                );
                assert_eq!(
                    SignTridiagonal::new(&lower, &diagonal, &upper).unwrap_err(),
                    Error::NonFinite
                );
                assert_eq!(
                    UnpivotedTridiagonal::new(&lower, &diagonal, &upper).unwrap_err(),
                    Error::NonFinite
                );
            }
        }
        let mut pivots = [0.; N];
        let mut upper = [0.; N - 1];
        let lower = [0.; N - 1];
        let diagonal = [2.; N];
        let factors = UnpivotedTridiagonal::new(&lower, &diagonal, &lower)
            .unwrap()
            .factor_into(&mut pivots, &mut upper)
            .unwrap();
        for index in 0..N {
            let mut rhs = [1.; N];
            rhs[index] = invalid;
            let mut out = [-7.25; N];
            assert_eq!(factors.solve_into(&rhs, &mut out), Err(Error::NonFinite));
            assert_eq!(out, [-7.25; N]);
        }
        // Seven columns exercise vector groups and scalar tails. No column
        // may be written before admission of the entire RHS batch succeeds.
        for index in 0..N * 7 {
            let mut rhs = [1.; N * 7];
            rhs[index] = invalid;
            let mut out = [-7.25; N * 7];
            assert_eq!(
                factors.solve_many_into(7, &rhs, &mut out),
                Err(Error::NonFinite)
            );
            assert_eq!(out, [-7.25; N * 7]);
        }
    }
}

/// A deterministic generator for the obstacle cases (SplitMix64).
struct Mix(u64);

impl Mix {
    fn unit(&mut self) -> f64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        ((z ^ (z >> 31)) >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// A strictly row-dominant M-matrix of `n` rows: positive diagonal,
/// nonpositive off-diagonals.
fn m_matrix(
    rng: &mut Mix,
    n: usize,
) -> (std::vec::Vec<f64>, std::vec::Vec<f64>, std::vec::Vec<f64>) {
    let lower: std::vec::Vec<f64> = (1..n).map(|_| -rng.unit()).collect();
    let upper: std::vec::Vec<f64> = (1..n).map(|_| -rng.unit()).collect();
    let diagonal = (0..n)
        .map(|i| {
            let left = if i > 0 { -lower[i - 1] } else { 0.0 };
            let right = if i + 1 < n { -upper[i] } else { 0.0 };
            left + right + 0.1 + rng.unit()
        })
        .collect();
    (lower, diagonal, upper)
}

/// The complementarity solution by enumeration of every contact set, each
/// solved densely: the unique `x` with `x >= g`, `A x >= b` and equality in one
/// of each pair. An independent reference for small `n`, and its contact set.
fn brute_force_lcp(
    lower: &[f64],
    diagonal: &[f64],
    upper: &[f64],
    rhs: &[f64],
    obstacle: &[f64],
) -> (std::vec::Vec<f64>, std::vec::Vec<bool>) {
    let n = diagonal.len();
    let entry = |i: usize, j: usize| {
        if i == j {
            diagonal[i]
        } else if j + 1 == i {
            lower[j]
        } else if i + 1 == j {
            upper[i]
        } else {
            0.0
        }
    };
    for mask in 0u32..(1 << n) {
        let contact = |i: usize| mask & (1 << i) != 0;
        let mut a = std::vec![std::vec![0.0; n + 1]; n];
        for i in 0..n {
            if contact(i) {
                a[i][i] = 1.0;
                a[i][n] = obstacle[i];
            } else {
                for (j, value) in a[i].iter_mut().take(n).enumerate() {
                    *value = entry(i, j);
                }
                a[i][n] = rhs[i];
            }
        }
        // Gaussian elimination with partial pivoting on the augmented rows.
        for col in 0..n {
            let pivot = (col..n)
                .max_by(|&p, &q| a[p][col].abs().total_cmp(&a[q][col].abs()))
                .unwrap();
            a.swap(col, pivot);
            for row in col + 1..n {
                let factor = a[row][col] / a[col][col];
                let pivot_row = a[col].clone();
                for (value, &above) in a[row].iter_mut().zip(&pivot_row).skip(col) {
                    *value -= factor * above;
                }
            }
        }
        let mut x = std::vec![0.0; n];
        for i in (0..n).rev() {
            let tail: f64 = (i + 1..n).map(|j| a[i][j] * x[j]).sum();
            x[i] = (a[i][n] - tail) / a[i][i];
        }
        let tolerance = 1e-12;
        let feasible = (0..n).all(|i| {
            let residual: f64 = (0..n).map(|j| entry(i, j) * x[j]).sum::<f64>() - rhs[i];
            x[i] >= obstacle[i] - tolerance && residual >= -tolerance
        });
        if feasible {
            return (x, (0..n).map(contact).collect());
        }
    }
    unreachable!("an M-matrix complementarity problem has a solution")
}

#[test]
fn an_obstacle_below_every_value_keeps_the_solve_bits() {
    let mut rng = Mix(289);
    for n in 0..12 {
        let (lower, diagonal, upper) = m_matrix(&mut rng, n);
        let rhs: std::vec::Vec<f64> = (0..n).map(|_| rng.unit() - 0.5).collect();
        let matrix = DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap();
        let mut pivots = std::vec![0.0; n];
        let mut normalized = std::vec![0.0; n.saturating_sub(1)];
        let factors = matrix.factor_into(&mut pivots, &mut normalized).unwrap();
        let (mut free, mut bounded) = (std::vec![0.0; n], std::vec![0.0; n]);
        factors.solve_into(&rhs, &mut free).unwrap();
        factors
            .solve_obstacle_into(&rhs, &std::vec![-f64::MAX; n], &mut bounded)
            .unwrap();
        assert_eq!(
            free.iter()
                .map(|x| x.to_bits())
                .collect::<std::vec::Vec<_>>(),
            bounded
                .iter()
                .map(|x| x.to_bits())
                .collect::<std::vec::Vec<_>>()
        );
    }
}

#[test]
fn the_obstacle_sweep_solves_one_sided_contact_and_refuses_every_other() {
    let mut rng = Mix(1977);
    let (mut upper_cases, mut lower_cases, mut refused) = (0, 0, 0);
    for case in 0..4000 {
        let n = 1 + case % 9;
        let (lower, diagonal, upper) = m_matrix(&mut rng, n);
        let rhs: std::vec::Vec<f64> = (0..n).map(|_| rng.unit() - 0.5).collect();
        // A rising obstacle tends to be met at the last rows; a falling one at
        // the first.
        let rising = case % 2 == 0;
        let obstacle: std::vec::Vec<f64> = (0..n)
            .map(|i| {
                let t = i as f64 / n as f64;
                (if rising { t } else { 1.0 - t }) - 0.6 + 0.3 * rng.unit()
            })
            .collect();
        let (expected, contact) = brute_force_lcp(&lower, &diagonal, &upper, &rhs, &obstacle);
        let first = contact.iter().position(|&c| c).unwrap_or(n);
        let last = contact.iter().rposition(|&c| c).map_or(0, |i| i + 1);
        let at_end = contact[first..].iter().all(|&c| c);
        let at_start = contact[..last].iter().all(|&c| c);
        let close = |x: &[f64]| {
            x.iter()
                .zip(&expected)
                .all(|(a, b)| (a - b).abs() <= 1e-12 * (1.0 + b.abs()))
        };
        let reverse = |v: &[f64]| v.iter().rev().copied().collect::<std::vec::Vec<_>>();
        // The reversed system, row i becoming row n - 1 - i, sweeps a contact
        // set that begins at the first row.
        for reversed in [false, true] {
            let (l, d, u, b, g) = if reversed {
                let (l, d, u) = (reverse(&upper), reverse(&diagonal), reverse(&lower));
                (l, d, u, reverse(&rhs), reverse(&obstacle))
            } else {
                let (l, d, u) = (lower.clone(), diagonal.clone(), upper.clone());
                (l, d, u, rhs.clone(), obstacle.clone())
            };
            let mut pivots = std::vec![0.0; n];
            let mut normalized = std::vec![0.0; n.saturating_sub(1)];
            let matrix = DominantTridiagonal::new(&l, &d, &u).unwrap();
            let factors = matrix.factor_into(&mut pivots, &mut normalized).unwrap();
            let mut x = std::vec![0.0; n];
            let solved = factors.solve_obstacle_into(&b, &g, &mut x);
            let x = if reversed { reverse(&x) } else { x };
            let one_sided = if reversed { at_start } else { at_end };
            match solved {
                Ok(()) => assert!(
                    close(&x),
                    "case {case} {reversed}: accepted a non-solution {x:?} {expected:?}"
                ),
                Err(Error::NotComplementary(_)) => {
                    assert!(!one_sided, "case {case} {reversed}: refused");
                    assert!(x.iter().zip(&obstacle).all(|(v, g)| v >= g));
                    refused += 1;
                }
                Err(error) => panic!("case {case} {reversed}: {error:?}"),
            }
            if one_sided {
                if reversed {
                    lower_cases += 1;
                } else {
                    upper_cases += 1;
                }
            }
            if !at_end && !at_start {
                assert!(
                    solved.is_err(),
                    "case {case} {reversed}: two-sided accepted"
                );
            }
        }
    }
    assert!(
        upper_cases > 500 && lower_cases > 500 && refused > 500,
        "{upper_cases} {lower_cases} {refused}"
    );
}

/// A long, graded M-matrix of the kind a parabolic stage produces, with an
/// obstacle met over its last rows: the check admits a sweep whose rows carry
/// thousands of eliminations, and refuses the same sweep's output once one
/// continuation row is moved by a few rounding bounds.
#[test]
fn a_long_one_sided_sweep_is_admitted_and_a_perturbed_row_is_not() {
    let n = 2049;
    let (mut lower, mut diagonal, mut upper) = (
        std::vec![0.0; n - 1],
        std::vec![0.0; n],
        std::vec![0.0; n - 1],
    );
    for i in 0..n {
        let spacing = 1.0 + (i as f64 / n as f64);
        let coupling = 40.0 / spacing;
        if i > 0 {
            lower[i - 1] = -coupling;
        }
        if i + 1 < n {
            upper[i] = -coupling;
        }
        diagonal[i] = 1.0 + 2.0 * coupling;
    }
    let rhs: std::vec::Vec<f64> = (0..n).map(|i| 1.0 - i as f64 / n as f64).collect();
    let obstacle: std::vec::Vec<f64> = (0..n).map(|i| 2.0 * i as f64 / n as f64 - 0.9).collect();
    let matrix = DominantTridiagonal::new(&lower, &diagonal, &upper).unwrap();
    let mut pivots = std::vec![0.0; n];
    let mut normalized = std::vec![0.0; n - 1];
    let factors = matrix.factor_into(&mut pivots, &mut normalized).unwrap();
    let mut x = std::vec![0.0; n];
    factors
        .solve_obstacle_into(&rhs, &obstacle, &mut x)
        .unwrap();
    let contact = x.iter().zip(&obstacle).filter(|(v, g)| v == g).count();
    assert!(contact > 100 && contact < n - 100, "{contact}");
    // One continuation row's right-hand side moved by about ten thousand
    // rounding units: the sweep's own output no longer solves it.
    let free = 10;
    assert!(x[free] > obstacle[free]);
    let mut moved = rhs.clone();
    moved[free] += 1e4 * f64::EPSILON * (1.0 + rhs[free].abs());
    assert_eq!(
        factors.factors.check_complementarity(&moved, &obstacle, &x),
        Err(Error::NotComplementary(free))
    );
}

#[test]
fn obstacle_arguments_are_checked_before_any_output_is_written() {
    let matrix = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
    let mut pivots = [0.0; 2];
    let mut normalized = [0.0];
    let factors = matrix.factor_into(&mut pivots, &mut normalized).unwrap();
    let mut out = [7.0; 2];
    assert_eq!(
        factors.solve_obstacle_into(&[1.0, 1.0], &[0.0], &mut out),
        Err(Error::Shape)
    );
    assert_eq!(
        factors.solve_obstacle_into(&[1.0, 1.0], &[0.0, f64::NAN], &mut out),
        Err(Error::NonFinite)
    );
    assert_eq!(out, [7.0; 2]);
    factors
        .solve_obstacle_into(&[3.0, 3.0], &[0.0, 1.5], &mut out)
        .unwrap();
    // Unconstrained [1, 1]; the last row is raised to 1.5 and the first
    // reads it: (3 - 1.5) / 2.
    assert_eq!(out, [0.75, 1.5]);
}
