//! Compare the bivariate normal's scalar kernel (`bivariate_norm_cdf` and the
//! table `BivariateNormal::new` builds) with its Coq transcription
//! (`formal/bivariate/BvnKernel.v`), extracted and run by
//! `scripts/check_formal.sh`, so a difference in an operation, its order, a
//! constant or a branch shows in the bits.
//!
//! The library functions the kernel calls (`exp`, `sin`, `asin`, `norm_cdf`)
//! are verified elsewhere and are not part of the extraction. Each line carries
//! the calls the Rust made, `function/argument/result` with the function one of
//! `e` (`exp`), `s` (`sin`), `a` (`asin`), `n` (`norm_cdf`) and the other two
//! fields 16 hex digits, and the extracted kernel takes its library results from
//! them: a call it makes that the Rust did not (the argument is missing from
//! the line) or a call the Rust made that it does not is a mismatch.
//!
//! `bvn_table rho calls : regime asr (kw p q)*` and
//! `bvn_cdf x y rho calls : result`.
use super::SplitMix64;
use crate::bivariate_normal::trace::{self, Call, Function};
use crate::bivariate_normal::{BivariateNormal, bivariate_norm_cdf};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::string::String;
use std::vec::Vec;

fn unit(rng: &mut SplitMix64) -> f64 {
    super::unit(rng)
}

fn calls(out: &mut String, calls: &[Call]) {
    for call in calls {
        let tag = match call.function {
            Function::Exp => 'e',
            Function::Sin => 's',
            Function::Asin => 'a',
            Function::NormCdf => 'n',
        };
        write!(out, " {tag}/{:016x}/{:016x}", call.argument, call.result).unwrap();
    }
}

/// The table lines and, for each of `points`, a value line.
fn correlation_lines(
    out: &mut String,
    tally: &mut BTreeMap<String, usize>,
    rho: f64,
    points: &[(f64, f64)],
) {
    let (table, recorded) = trace::recording(|| BivariateNormal::new(rho));
    write!(out, "bvn_table {:016x}", rho.to_bits()).unwrap();
    calls(out, &recorded);
    match table {
        Ok(table) => {
            let (regime, asr, nodes) = trace::table_parts(&table);
            write!(out, " : {regime} {asr:016x}").unwrap();
            for [kw, p, q] in nodes {
                write!(out, " {kw:016x} {p:016x} {q:016x}").unwrap();
            }
        }
        Err(_) => out.push_str(" : none"),
    }
    out.push('\n');
    for &(x, y) in points {
        let (value, recorded) = trace::recording(|| bivariate_norm_cdf(x, y, rho));
        write!(
            out,
            "bvn_cdf {:016x} {:016x} {:016x}",
            x.to_bits(),
            y.to_bits(),
            rho.to_bits()
        )
        .unwrap();
        calls(out, &recorded);
        writeln!(out, " : {:016x}", value.to_bits()).unwrap();
        for tag in trace::branches(x, y, rho) {
            *tally.entry(tag).or_default() += 1;
        }
    }
}

/// `value` and its neighbours either side, in both signs.
fn around(value: f64) -> [f64; 6] {
    [
        value.next_down(),
        value,
        value.next_up(),
        -value.next_down(),
        -value,
        -value.next_up(),
    ]
}

/// A correlation of each regime and of each edge between them: the closed
/// forms and their ulp neighbours, every low rule's limit and the adjacent
/// doubles, the Genz split, the scale `a = sqrt(1 - rho^2)` at which the
/// panels change from 16 to 15 nodes (`0.095 2^j`) and stop (`0.003 2^j`), and
/// the unit edge; then draws across the low and the high ranges.
fn correlations(rng: &mut SplitMix64) -> Vec<f64> {
    let mut rhos = std::vec![
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        1.5,
        -2.0,
        1.0_f64.next_up(),
        -(1.0_f64.next_up()),
        0.0,
        -0.0,
        1.0,
        -1.0,
        1.0_f64.next_down(),
        -(1.0_f64.next_down()),
        1e-300,
        f64::from_bits(1),
        0.25,
        0.786_151_377_757_423_3,
        0.5,
        -0.5,
    ];
    rhos.extend(around(f64::EPSILON));
    for limit in [0.20, 0.29, 0.66, 0.75, 0.89] {
        rhos.extend(around(limit));
    }
    rhos.extend(around(0.925));
    for (floor, count) in [(0.095, 3), (0.003, 9)] {
        for j in 0..count {
            let a = floor * f64::from(1_u32 << j);
            let rho = crate::elementary::sqrt((1.0 - a) * (1.0 + a));
            rhos.extend(around(rho));
        }
    }
    for rho in [
        0.95,
        0.99,
        0.999,
        1.0 - 1e-6,
        1.0 - 1e-9,
        1.0 - 1e-12,
        1.0 - 1e-15,
    ] {
        rhos.push(rho);
        rhos.push(-rho);
    }
    for _ in 0..40 {
        rhos.push((unit(rng) * 2.0 - 1.0) * 0.925);
    }
    for _ in 0..40 {
        // `1 - rho` log-uniform from `2^-53` to `0.075`.
        let delta = 0.075
            * f64::from_bits(0x3ff0_0000_0000_0000 - ((rng.next_u64() % 50) << 52))
            * (0.5 + unit(rng) / 2.0);
        let rho = 1.0 - delta;
        let rho = if (0.925..1.0).contains(&rho) {
            rho
        } else {
            0.99
        };
        rhos.push(if rng.next_u64() & 1 == 1 { -rho } else { rho });
    }
    rhos
}

/// The thresholds every correlation is run at: the zeros and their signs, the
/// diagonal and anti-diagonal (where `x + y = 0`, `m = 0`), the high branch's
/// `hk` of 100 and its cutoff, the closed form's `b` skip on either side, the saturation
/// thresholds and their neighbours, the infinities and NaN.
fn structured_points() -> Vec<(f64, f64)> {
    let mut points = std::vec![
        (0.0, 0.0),
        (-0.0, -0.0),
        (0.0, -0.0),
        (-0.0, 0.0),
        (0.0, 1.0),
        (1.0, 0.0),
        (-0.5, -0.5),
        (-0.5, 0.5),
        (0.5, -0.5),
        (-1.3, -1.3000000000000003),
        (-3.0, 3.0),
        (-3.0, -3.0),
        (2.5, 1.0),
        (-6.0, -6.0000000001),
        (-6.0, 6.0),
        // hk = dh dk around 100.
        (-10.0, -10.0),
        (-10.0, (-10.0_f64).next_up()),
        (-10.0, 10.0),
        (-10.0, 10.0_f64.next_down()),
        (-11.0, -11.0),
        (-11.0, 11.0),
        (-9.0, -13.0),
        (-30.0, -30.0),
        (-30.0, 30.0),
        // hk = dh dk around 1400, the cutoff, and below it where the nodes' own
        // cutoff `phi = 700` falls inside the panels.
        (-37.0, -37.83783783783783),
        (-37.0, -37.83783783783784),
        (-37.0, 37.83783783783783),
        (-37.0, 37.83783783783784),
        (-36.0, -37.0),
        (-36.5, 36.5),
        (-20.0, -30.0),
        (-15.0, -20.0),
        // b = |dh - k| around 20 s.
        (-0.5, -0.5 - 1e-9),
        (-0.5, -0.5 + 0.01),
        (-0.5, -0.5 + 0.05),
        (-0.5, -0.5 + 0.059),
        (-0.5, -0.5 + 0.061),
        (-0.5, -0.5 + 0.2),
        (-0.5, 0.5 - 1e-9),
        (-0.5, 0.5 + 0.01),
        (-0.5, 0.5 + 0.05),
        (-0.5, 0.5 + 0.061),
        (-0.5, 0.5 + 0.2),
        (-2.0, -2.0 + 0.03),
        (-2.0, 2.0 - 0.03),
        // The saturation thresholds.
        (-39.0, 0.0),
        ((-39.0_f64).next_up(), 0.0),
        ((-39.0_f64).next_down(), 0.0),
        (-39.0, 39.0),
        (-38.0, 39.0),
        (-38.0, 39.0_f64.next_down()),
        (0.0, 39.0),
        (0.0, 39.0_f64.next_down()),
        (39.0, 39.0),
        (-39.0, -39.0),
        (38.5, 38.9),
        (-38.9, -38.5),
        (-38.9, 38.9),
        (f64::NEG_INFINITY, f64::INFINITY),
        (f64::INFINITY, f64::INFINITY),
        (f64::NEG_INFINITY, f64::NEG_INFINITY),
        (f64::NEG_INFINITY, 0.0),
        (1.0, f64::INFINITY),
        (f64::NAN, 0.0),
        (0.0, f64::NAN),
        (f64::NAN, f64::NAN),
        (1e300, -1e300),
        (f64::MAX, f64::MAX),
        (-f64::MAX, 0.0),
        (f64::from_bits(1), -f64::from_bits(1)),
        (f64::MIN_POSITIVE, 0.0),
    ];
    points.extend([
        (-0.21101192279835226, -0.0014549743776884816),
        (-0.0014549743776884816, -0.21101192279835226),
    ]);
    points
}

/// Draws: a bulk of moderate thresholds, thresholds at the same point or
/// mirrored, and a share in the tails.
fn drawn_points(rng: &mut SplitMix64, count: usize) -> Vec<(f64, f64)> {
    let mut points = Vec::new();
    for _ in 0..count {
        let scale = match rng.next_u64() % 4 {
            0 => 0.3,
            1 => 1.5,
            2 => 4.0,
            _ => 9.0,
        };
        let x = (unit(rng) * 2.0 - 1.0) * scale;
        let y = match rng.next_u64() % 4 {
            0 => x,
            1 => -x,
            2 => x + (unit(rng) - 0.5) * 0.1,
            _ => (unit(rng) * 2.0 - 1.0) * scale,
        };
        points.push((x, y));
    }
    points
}

pub(super) fn write(out: &mut String) {
    let mut rng = SplitMix64::new(0x6276_6e63_726f_7301);
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    let structured = structured_points();
    let rhos = correlations(&mut rng);
    let mut cases = 0;
    for (index, &rho) in rhos.iter().enumerate() {
        // Every correlation sees the structured thresholds when it is cheap, or
        // every fourth when it selects the high branch; every one sees draws.
        let high = rho.abs() >= 0.925 && rho.abs() < 1.0;
        let mut points: Vec<(f64, f64)> = if high && index % 4 != 0 {
            structured.iter().copied().step_by(3).collect()
        } else {
            structured.clone()
        };
        points.extend(drawn_points(&mut rng, if high { 6 } else { 8 }));
        cases += points.len();
        correlation_lines(out, &mut tally, rho, &points);
    }
    // The counterexample of docs/bivariate_normal_high.md, at the split and beside it.
    for rho in around(0.925).into_iter().chain([0.925]) {
        correlation_lines(
            out,
            &mut tally,
            rho,
            &[(-0.21101192279835226, -0.0014549743776884816)],
        );
        cases += 1;
    }
    std::println!(
        "bivariate cross-check: {} correlations, {cases} cases",
        rhos.len() + 7
    );
    for (tag, count) in &tally {
        std::println!("  {tag}: {count}");
    }
    let required = [
        "invalid-correlation",
        "independent",
        "comonotone",
        "countermonotone",
        "low-6",
        "low-8",
        "low-12",
        "low-14",
        "low-20",
        "low-24",
        "saturated-lower",
        "saturated-upper",
        "nan-threshold",
        "swapped",
        "signed-zero-threshold",
        "signed-zero-correlation",
        "high-positive",
        "high-negative",
        "negative-difference",
        "negative-zero",
        "hk-skip",
        "hk-large",
        "hk-split",
        "closed-remainder",
        "closed-form",
        "closed-form-skip",
        "panel-16-nodes",
        "panel-15-nodes",
        "panels-0",
        "panels-1",
        "panels-2",
        "panels-3",
    ];
    for tag in required {
        assert!(tally.contains_key(tag), "the corpus has no case for {tag}");
    }
}
