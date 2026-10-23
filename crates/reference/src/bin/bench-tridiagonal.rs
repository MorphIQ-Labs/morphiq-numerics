//! Native paired tridiagonal timings. Protocol and native qualification are in #152 under epic #149.
//! Exact synthetic inputs; preallocated buffers; no oracle in timed loops.
use morphiq_numerics::linalg::tridiagonal::{
    DominantTridiagonal, SignTridiagonal, UnpivotedTridiagonal,
};
use std::{hint::black_box, time::Instant};

// Adapted from the same original MIT FerroRisk recurrence as the library.
// See crates/morphiq-numerics/THIRD_PARTY_NOTICES.md. Compact off-diagonals;
// successful finite-domain benchmark only. The original absolute 1e-300
// pivot threshold is deliberately retained: subnormal cases are not timed
// against this baseline, since its domain excludes them.
fn legacy(l: &[f64], d: &[f64], u: &[f64], rhs: &[f64], out: &mut [f64], c: &mut [f64]) {
    let n = d.len();
    if n == 0 {
        return;
    }
    assert!(d[0].is_finite() && d[0].abs() >= 1e-300);
    if n > 1 {
        c[0] = u[0] / d[0];
    }
    out[0] = rhs[0] / d[0];
    for i in 1..n {
        let p = d[i] - l[i - 1] * c[i - 1];
        assert!(p.is_finite() && p.abs() >= 1e-300);
        if i + 1 < n {
            c[i] = u[i] / p;
        }
        out[i] = (rhs[i] - l[i - 1] * out[i - 1]) / p;
    }
    for i in (0..n - 1).rev() {
        out[i] -= c[i] * out[i + 1];
    }
}

struct Work {
    lower: Vec<f64>,
    diagonal: Vec<f64>,
    upper: Vec<f64>,
    rhs: Vec<f64>,
    pivots: Vec<f64>,
    normalized: Vec<f64>,
    out: Vec<f64>,
    old_scratch: Vec<f64>,
}

impl Work {
    fn new(n: usize, kind: &str) -> Self {
        let scale = if kind == "subnormal" || kind == "sign-subnormal" {
            f64::MIN_POSITIVE / 16.0
        } else {
            1.0
        };
        let lower = vec![-scale; n.saturating_sub(1)];
        let upper = (0..n.saturating_sub(1))
            .map(|i| {
                if kind.starts_with("sign") || (kind == "mixed" && i % 2 == 0) {
                    scale
                } else {
                    -scale
                }
            })
            .collect();
        let mut diagonal = vec![
            (if kind.starts_with("sign") && kind != "sign-intersection" {
                0.5
            } else if kind == "near" {
                2.0 + f64::EPSILON * 4.0
            } else {
                4.0
            }) * scale;
            n
        ];
        let rhs = (0..n)
            .map(|i| f64::from(u32::try_from(i % 13).unwrap()) * scale)
            .collect();
        // A row-sum-one M-matrix keeps a constant vector stationary in exact
        // arithmetic, so the dependence-chain workload does not decay to zero.
        if kind == "conservative" {
            diagonal.fill(3.0);
            diagonal[0] = 2.0;
            diagonal[n - 1] = if n == 1 { 1.0 } else { 2.0 };
        }
        Self {
            lower,
            diagonal,
            upper,
            rhs: if kind == "conservative" {
                vec![1.0; n]
            } else {
                rhs
            },
            pivots: vec![0.0; n],
            normalized: vec![0.0; n.saturating_sub(1)],
            out: vec![0.0; n],
            old_scratch: vec![0.0; n],
        }
    }

    fn run(&mut self, method: &str, count: usize, rhs_count: usize) -> u128 {
        let a = DominantTridiagonal::new(&self.lower, &self.diagonal, &self.upper).unwrap();
        let f = a
            .factor_into(&mut self.pivots, &mut self.normalized)
            .unwrap();
        f.solve_into(&self.rhs, &mut self.out).unwrap();
        // Independent RHS/output pairs for eight systems sharing one matrix.
        // Both allocation and construction are outside the timed interval.
        let bank_count = if method == "independent8" {
            8
        } else {
            rhs_count
        };
        let bank: Vec<Vec<f64>> = if matches!(method, "independent8" | "independent" | "batched") {
            (1..=bank_count)
                .map(|k| {
                    self.rhs
                        .iter()
                        .map(|x| x * f64::from(u32::try_from(k).unwrap()))
                        .collect()
                })
                .collect()
        } else {
            Vec::new()
        };
        let mut results: Vec<Vec<f64>> = bank.iter().map(|_| vec![0.0; self.out.len()]).collect();
        // Both layouts are prepared before timing. This comparison measures
        // solve APIs; callers that need packing must measure that cost too.
        let interleaved: Vec<_> = if bank.is_empty() {
            Vec::new()
        } else {
            (0..self.rhs.len() * bank_count)
                .map(|at| bank[at % bank_count][at / bank_count])
                .collect()
        };
        let mut batch_out = vec![0.0; interleaved.len()];
        if !bank.is_empty() {
            f.solve_many_into(bank_count, &interleaved, &mut batch_out)
                .unwrap();
            for (column, (rhs, out)) in bank.iter().zip(&mut results).enumerate() {
                f.solve_into(rhs, out).unwrap();
                for (row, &x) in out.iter().enumerate() {
                    assert_eq!(x.to_bits(), batch_out[row * bank_count + column].to_bits());
                }
            }
        }
        let start = Instant::now();
        match method {
            "chain" => {
                for _ in 0..count {
                    f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                        .unwrap();
                    core::mem::swap(&mut self.rhs, &mut self.out);
                    black_box(&self.rhs);
                }
            }
            "batched" => {
                for _ in 0..count {
                    f.solve_many_into(
                        bank_count,
                        black_box(&interleaved),
                        black_box(&mut batch_out),
                    )
                    .unwrap();
                    black_box(&batch_out);
                }
            }
            "independent8" | "independent" => {
                for _ in 0..count {
                    for (rhs, out) in bank.iter().zip(&mut results) {
                        f.solve_into(black_box(rhs), black_box(out)).unwrap();
                        black_box(out);
                    }
                }
            }
            "solve" => {
                for _ in 0..count {
                    for _ in 0..rhs_count {
                        f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                            .unwrap();
                        black_box(&self.out);
                    }
                }
            }
            "certify" => {
                for _ in 0..count {
                    black_box(
                        f.certify(black_box(&self.rhs), black_box(&self.out))
                            .unwrap(),
                    );
                }
            }
            "legacy" | "legacy_certified" => {
                for _ in 0..count {
                    for _ in 0..rhs_count {
                        legacy(
                            black_box(&self.lower),
                            black_box(&self.diagonal),
                            black_box(&self.upper),
                            black_box(&self.rhs),
                            black_box(&mut self.out),
                            black_box(&mut self.old_scratch),
                        );
                        if method == "legacy_certified" {
                            black_box(
                                f.certify(black_box(&self.rhs), black_box(&self.out))
                                    .unwrap(),
                            );
                        }
                        black_box(&self.out);
                    }
                }
            }
            "admit" => {
                for _ in 0..count {
                    black_box(
                        DominantTridiagonal::new(
                            black_box(&self.lower),
                            black_box(&self.diagonal),
                            black_box(&self.upper),
                        )
                        .unwrap(),
                    );
                }
            }
            "factor" | "reused" | "reused_certified" => {
                for _ in 0..count {
                    let f = a
                        .factor_into(black_box(&mut self.pivots), black_box(&mut self.normalized))
                        .unwrap();
                    if method != "factor" {
                        for _ in 0..rhs_count {
                            f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                                .unwrap();
                            if method == "reused_certified" {
                                black_box(
                                    f.certify(black_box(&self.rhs), black_box(&self.out))
                                        .unwrap(),
                                );
                            }
                            black_box(&self.out);
                        }
                    }
                    black_box(f);
                }
            }
            "copy_control" => {
                for _ in 0..count {
                    black_box(&mut self.out).copy_from_slice(black_box(&self.rhs));
                    black_box(&self.out);
                }
            }
            _ => panic!("unknown method"),
        }
        let elapsed = start.elapsed().as_nanos();
        if method == "chain" {
            // This is a workload-validity screen, not a solver error bound:
            // retain the unit-scale regime rather than timing underflow/zero.
            assert!(self.rhs.iter().all(|&x| (0.5..2.0).contains(&x)));
        }
        elapsed
    }

    fn measure_unpivoted(&mut self, method: &str, count: usize) -> u128 {
        let a = UnpivotedTridiagonal::new(&self.lower, &self.diagonal, &self.upper).unwrap();
        let f = a
            .factor_into(&mut self.pivots, &mut self.normalized)
            .unwrap();
        f.solve_into(&self.rhs, &mut self.out).unwrap();
        let mut old = vec![0.; self.out.len()];
        legacy(
            &self.lower,
            &self.diagonal,
            &self.upper,
            &self.rhs,
            &mut old,
            &mut self.old_scratch,
        );
        assert!(
            old.iter()
                .zip(&self.out)
                .all(|(x, y)| x.to_bits() == y.to_bits())
        );
        if method == "total" || method == "factor" {
            let start = Instant::now();
            for _ in 0..count {
                let a = UnpivotedTridiagonal::new(
                    black_box(&self.lower),
                    black_box(&self.diagonal),
                    black_box(&self.upper),
                )
                .unwrap();
                let f = a
                    .factor_into(black_box(&mut self.pivots), black_box(&mut self.normalized))
                    .unwrap();
                if method == "total" {
                    assert!(f.min_abs_pivot().is_none_or(|p| p >= 1e-300));
                    f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                        .unwrap();
                }
                black_box(f);
            }
            return start.elapsed().as_nanos();
        }
        let f = a
            .factor_into(&mut self.pivots, &mut self.normalized)
            .unwrap();
        let start = Instant::now();
        for _ in 0..count {
            match method {
                "admit" => {
                    black_box(
                        UnpivotedTridiagonal::new(
                            black_box(&self.lower),
                            black_box(&self.diagonal),
                            black_box(&self.upper),
                        )
                        .unwrap(),
                    );
                }
                "minimum" => {
                    black_box(f.min_abs_pivot());
                }
                "solve" => {
                    f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                        .unwrap();
                }
                "residual" => {
                    black_box(
                        f.certify_residual(black_box(&self.rhs), black_box(&self.out))
                            .unwrap(),
                    );
                }
                "legacy" => legacy(
                    black_box(&self.lower),
                    black_box(&self.diagonal),
                    black_box(&self.upper),
                    black_box(&self.rhs),
                    black_box(&mut self.out),
                    black_box(&mut self.old_scratch),
                ),
                _ => panic!("unknown unpivoted method"),
            }
        }
        start.elapsed().as_nanos()
    }

    // Separate sign-domain entry point; the existing dominant campaign is unchanged.
    // Layout preparation and qualification are outside every timed phase.
    fn measure_sign(&mut self, method: &str, count: usize, rhs_count: usize) -> u128 {
        let a = SignTridiagonal::new(&self.lower, &self.diagonal, &self.upper).unwrap();
        let f = a
            .factor_into(&mut self.pivots, &mut self.normalized)
            .unwrap();
        f.solve_into(&self.rhs, &mut self.out).unwrap();
        f.certify_residual(&self.rhs, &self.out).unwrap();
        if self.diagonal.iter().all(|d| *d >= 1e-300) {
            let mut old = vec![0.0; self.out.len()];
            legacy(
                &self.lower,
                &self.diagonal,
                &self.upper,
                &self.rhs,
                &mut old,
                &mut self.old_scratch,
            );
            assert!(
                old.iter()
                    .zip(&self.out)
                    .all(|(x, y)| x.to_bits() == y.to_bits())
            );
        } else {
            assert_ne!(method, "legacy");
        }
        let batch: Vec<_> = self
            .rhs
            .iter()
            .flat_map(|&x| std::iter::repeat_n(x, rhs_count))
            .collect();
        let mut batch_out = vec![0.0; batch.len()];
        f.solve_many_into(rhs_count, &batch, &mut batch_out)
            .unwrap();
        for (row, values) in batch_out.chunks(rhs_count.max(1)).enumerate() {
            assert!(
                values
                    .iter()
                    .all(|x| x.to_bits() == self.out[row].to_bits())
            );
        }
        let start = Instant::now();
        match method {
            "admit" => {
                for _ in 0..count {
                    black_box(
                        SignTridiagonal::new(
                            black_box(&self.lower),
                            black_box(&self.diagonal),
                            black_box(&self.upper),
                        )
                        .unwrap(),
                    );
                }
            }
            "factor" | "reused" => {
                for _ in 0..count {
                    let f = a
                        .factor_into(black_box(&mut self.pivots), black_box(&mut self.normalized))
                        .unwrap();
                    if method == "reused" {
                        for _ in 0..rhs_count {
                            f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                                .unwrap();
                            black_box(&self.out);
                        }
                    }
                    black_box(f);
                }
            }
            "solve" | "certified" => {
                for _ in 0..count {
                    for _ in 0..rhs_count {
                        f.solve_into(black_box(&self.rhs), black_box(&mut self.out))
                            .unwrap();
                        if method == "certified" {
                            black_box(
                                f.certify_residual(black_box(&self.rhs), black_box(&self.out))
                                    .unwrap(),
                            );
                        }
                        black_box(&self.out);
                    }
                }
            }
            "batch" => {
                for _ in 0..count {
                    f.solve_many_into(rhs_count, black_box(&batch), black_box(&mut batch_out))
                        .unwrap();
                    black_box(&batch_out);
                }
            }
            "certify" => {
                for _ in 0..count {
                    black_box(
                        f.certify_residual(black_box(&self.rhs), black_box(&self.out))
                            .unwrap(),
                    );
                }
            }
            "legacy" => {
                for _ in 0..count {
                    for _ in 0..rhs_count {
                        legacy(
                            black_box(&self.lower),
                            black_box(&self.diagonal),
                            black_box(&self.upper),
                            black_box(&self.rhs),
                            black_box(&mut self.out),
                            black_box(&mut self.old_scratch),
                        );
                        black_box(&self.out);
                    }
                }
            }
            "copy_control" => {
                for _ in 0..count {
                    black_box(&mut self.out).copy_from_slice(black_box(&self.rhs));
                    black_box(&self.out);
                }
            }
            _ => panic!("unknown sign-domain method"),
        }
        start.elapsed().as_nanos()
    }

    fn measure(&mut self, method: &str, count: usize, rhs_count: usize) -> u128 {
        self.run(method, count, rhs_count)
    }

    fn qualify(&mut self, legacy_supported: bool) {
        let a = DominantTridiagonal::new(&self.lower, &self.diagonal, &self.upper).unwrap();
        let f = a
            .factor_into(&mut self.pivots, &mut self.normalized)
            .unwrap();
        f.solve_into(&self.rhs, &mut self.out).unwrap();
        f.certify(&self.rhs, &self.out).unwrap();
        if legacy_supported {
            let mut old = vec![0.0; self.out.len()];
            legacy(
                &self.lower,
                &self.diagonal,
                &self.upper,
                &self.rhs,
                &mut old,
                &mut self.old_scratch,
            );
            assert!(
                old.iter()
                    .zip(&self.out)
                    .all(|(a, b)| a.to_bits() == b.to_bits())
            );
        }
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    // A single operation mode is useful for profiles/allocation instrumentation;
    // it is deliberately separate from uninstrumented paired timing.
    if args.get(1).is_some_and(|s| s == "--profile") {
        let method = args.get(2).expect("method");
        let count = args.get(3).expect("count").parse().unwrap();
        let mut work = Work::new(401, "ordinary");
        work.run(method, count, 8);
        return;
    }
    if args.get(1).is_some_and(|s| s == "--unpivoted-one") {
        let mut work = Work::new(args[2].parse().unwrap(), &args[3]);
        println!(
            "{}",
            work.measure_unpivoted(&args[4], args[5].parse().unwrap())
        );
        return;
    }
    if args.get(1).is_some_and(|s| s == "--sign-one") {
        let n = args[2].parse().unwrap();
        let mut work = Work::new(n, &args[3]);
        let calls = args[5].parse().unwrap();
        let rhs = args[6].parse().unwrap();
        println!("{}", work.measure_sign(&args[4], calls, rhs));
        return;
    }
    if args.get(1).is_some_and(|s| s == "--one") {
        let n = args[2].parse().unwrap();
        let mut work = Work::new(n, &args[3]);
        let calls = args[5].parse().unwrap();
        let rhs = args[6].parse().unwrap();
        println!("{}", work.measure(&args[4], calls, rhs));
        return;
    }
    println!("kind,n,rhs,pair,method,round,position,calls,elapsed_ns");
    let batches = args.get(1).is_some_and(|s| s == "--batches");
    let compositions = args.get(1).is_some_and(|s| s == "--compositions");
    for n in [1, 3, 17, 401, 4096] {
        let kinds: &[&str] = if compositions {
            &["conservative"]
        } else {
            &["ordinary", "mixed", "near", "subnormal"]
        };
        for &kind in kinds {
            let mut work = Work::new(n, kind);
            work.qualify(kind != "subnormal");
            let mut pairs = vec![
                ("admit", "copy_control", 1),
                ("factor", "solve", 1),
                ("certify", "copy_control", 1),
            ];
            if kind != "subnormal" {
                for rhs in [1, 8, 64] {
                    pairs.push(("reused", "legacy", rhs));
                    pairs.push(("reused_certified", "legacy_certified", rhs));
                }
            }
            if compositions {
                pairs = vec![("chain", "solve", 1), ("independent8", "solve", 8)];
            }
            if batches {
                pairs = [1, 2, 3, 4, 7, 8, 9, 17, 64]
                    .into_iter()
                    .map(|rhs| ("batched", "independent", rhs))
                    .collect();
            }
            for (a, b, rhs) in pairs {
                let counts = [a, b].map(|method| {
                    let calibration = work.measure(method, 16, rhs);
                    usize::try_from((160_000_000 / calibration.max(1)).max(1)).unwrap()
                });
                for index in [0, 1, 1, 0] {
                    work.run([a, b][index], counts[index], rhs);
                }
                for round in 0..21 {
                    for (position, index) in [0, 1, 1, 0].into_iter().enumerate() {
                        let method = [a, b][index];
                        let calls = counts[index];
                        let elapsed = work.measure(method, calls, rhs);
                        println!(
                            "{kind},{n},{rhs},{a}:{b},{method},{round},{position},{calls},{elapsed}"
                        );
                    }
                }
            }
        }
    }
}
