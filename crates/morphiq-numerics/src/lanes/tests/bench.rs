//! Same-host measurements of every lane kernel, per backend (docs/lanes.md
//! §7): never a timing assertion or a CI gate.
//!
//! ```sh
//! cargo test --release --locked -p morphiq-numerics --all-features --lib \
//!     native_performance -- --ignored --nocapture --test-threads=1
//! ```
//!
//! Each function's test module names its workloads and its `decided_by`
//! classifier in its own `native_performance` test; the standard-normal
//! functions and the cache experiment are here, `native_performance_normal`
//! and `native_performance_cache`. Proof-bound sources stay unchanged.
//!
//! Every function runs on fixed-seed workloads in each mode: the scalar
//! loop, the dispatched cascade (`map`), each backend this CPU has forced
//! alone (whole chunks, then the scalar function for the remainder), the
//! scalar dependency chain and the same chain through the identity. A slice
//! length `L` shorter than the pool is timed as the pool in consecutive calls
//! of `L` elements, so short batches see the pool's arguments rather than one
//! repeated slice. Each round times every mode and length once, in an order
//! rotated per round, after one discarded warm-up round. Outside timing, each
//! mode's output is checked against the scalar bits, and each function's
//! classifier, checked against the same bits, counts which stage
//! decided each argument.
//!
//! Output is CSV on stdout, one record per line, its first field the kind:
//! `time,function,workload,length,mode,round,ns_per_element,ns_per_call`,
//! `path,function,workload,label,count,total`, `table,name,bytes` and
//! `cache,function,working_set,mode,round,ns_per_element`.
//!
//! Environment: `MORPHIQ_LANES_BENCH_FUNCTIONS` and
//! `MORPHIQ_LANES_BENCH_WORKLOADS` (comma-separated names) select cases;
//! `MORPHIQ_LANES_BENCH_LENGTHS` (comma-separated, default
//! `1,…,17,32,64,256,4096,65536`); `MORPHIQ_LANES_BENCH_ROUNDS` (default 11);
//! `MORPHIQ_LANES_BENCH_MS`, each sample's minimum milliseconds (default 2).

use core::hint::black_box;
use std::string::String;
use std::time::Instant;
use std::vec::Vec;
use std::{println, vec};

use super::{Backend, backends};
use crate::erfcx::lanes::Erfcx;
use crate::exp::lanes::Exp;
use crate::lanes::{Kernel, map};
use crate::ln::lanes::Ln;
use crate::normal_distribution::lanes::Normal;
use crate::normal_distribution::{
    Operation, evaluate as normal, fast_decide, first_decide, special,
};
use crate::random::{SplitMix64, unit_closed_open};

/// The pool every slice length up to its size is cut from.
const POOL: usize = 4096;
/// Arguments searched for a fallback workload before it is cycled.
const SEARCH: u64 = 1 << 27;

pub(crate) type Path = fn(f64) -> (&'static str, f64);
type Batched = fn(&[f64], &mut [f64]);

/// How a workload's arguments are drawn.
#[derive(Clone, Copy)]
pub(crate) enum Draw {
    /// Uniform on `[low, low + width)`.
    Uniform(f64, f64),
    /// `2^e` with `e` uniform on `[low, low + width)`, then `offset` added.
    LogUniform(f64, f64, f64),
    /// Encodings uniform on `[low, low + width)`.
    Bits(u64, u64),
    /// Cycled through these values.
    Values(&'static [f64]),
    /// From the given draw, kept only where `path` gives `"accurate"` or a
    /// label ending in `_accurate`.
    Fallback(&'static Draw),
    /// Element `i` from draw `i mod n`.
    Mixed(&'static [Draw]),
}

struct Settings {
    functions: Option<Vec<String>>,
    workloads: Option<Vec<String>>,
    lengths: Vec<usize>,
    rounds: usize,
    seconds: f64,
}

fn list(name: &str) -> Option<Vec<String>> {
    std::env::var(name)
        .ok()
        .map(|v| v.split(',').map(|s| String::from(s.trim())).collect())
}

fn settings() -> Settings {
    let lengths = list("MORPHIQ_LANES_BENCH_LENGTHS").map_or_else(
        || (1..=17).chain([32, 64, 256, POOL, 65_536]).collect(),
        |v| {
            v.iter()
                .map(|s| s.parse().expect("integer length"))
                .collect()
        },
    );
    let number = |name: &str, default: f64| {
        std::env::var(name).map_or(default, |v| v.parse().expect("a number"))
    };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // a round count
    let rounds = number("MORPHIQ_LANES_BENCH_ROUNDS", 11.0) as usize;
    Settings {
        functions: list("MORPHIQ_LANES_BENCH_FUNCTIONS"),
        workloads: list("MORPHIQ_LANES_BENCH_WORKLOADS"),
        lengths,
        rounds,
        seconds: number("MORPHIQ_LANES_BENCH_MS", 2.0) / 1e3,
    }
}

fn selected(filter: Option<&Vec<String>>, name: &str) -> bool {
    filter.is_none_or(|v| v.iter().any(|s| s == name))
}

/// A seed from the workload's name, so each workload is fixed on its own.
fn seed(function: &str, workload: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in function.bytes().chain(*b"/").chain(workload.bytes()) {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
    }
    h
}

fn draw_one(draw: &Draw, rng: &mut SplitMix64, i: usize) -> f64 {
    match *draw {
        Draw::Uniform(low, width) => low + width * unit_closed_open(rng.next_u64()),
        Draw::LogUniform(low, width, offset) => {
            let e = low + width * unit_closed_open(rng.next_u64());
            offset + crate::exp2::exp2(e)
        }
        Draw::Bits(low, width) => f64::from_bits(low + rng.next_u64() % width),
        Draw::Values(values) => values[i % values.len()],
        Draw::Mixed(draws) => draw_one(&draws[i % draws.len()], rng, i / draws.len()),
        Draw::Fallback(_) => unreachable!("drawn by `arguments`"),
    }
}

/// `n` arguments of `draw`, and for a fallback workload how many distinct
/// arguments the search found (`n` otherwise).
fn arguments(draw: &Draw, path: Path, rng: &mut SplitMix64, n: usize) -> (Vec<f64>, usize) {
    if let Draw::Fallback(inner) = draw {
        let mut found = Vec::new();
        let mut tried = 0;
        while found.len() < n && tried < SEARCH {
            let x = draw_one(inner, rng, found.len());
            tried += 1;
            let label = path(x).0;
            if label == "accurate" || label.ends_with("_accurate") {
                found.push(x);
            }
        }
        assert!(!found.is_empty(), "no fallback argument in {SEARCH} draws");
        let distinct = found.len();
        let xs = (0..n).map(|i| found[i % distinct]).collect();
        return (xs, distinct);
    }
    ((0..n).map(|i| draw_one(draw, rng, i)).collect(), n)
}

/// Seconds per call of `run`, its repetitions calibrated to at least
/// `seconds` per sample.
fn sample(seconds: f64, run: &mut dyn FnMut()) -> f64 {
    let mut reps = 1_u32;
    loop {
        let start = Instant::now();
        for _ in 0..reps {
            run();
        }
        let elapsed = start.elapsed().as_secs_f64();
        if elapsed >= seconds {
            return elapsed / f64::from(reps);
        }
        reps = reps.saturating_mul(if elapsed * 8.0 < seconds { 8 } else { 2 });
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Scalar,
    Dispatch,
    Forced(usize),
    Chain,
    ChainIdentity,
}

/// `out[i] = G::scalar(xs[i])` in `mode`, in consecutive calls of `length`.
fn evaluate<G: Kernel>(mode: Mode, lanes: &[Backend], length: usize, xs: &[f64], out: &mut [f64]) {
    for (x, o) in xs.chunks(length).zip(out.chunks_mut(length)) {
        match mode {
            Mode::Scalar => {
                for (o, &x) in o.iter_mut().zip(x) {
                    *o = G::scalar(x);
                }
            }
            Mode::Dispatch => map::<G>(x, o),
            Mode::Forced(b) => {
                let done = lanes[b].chunks::<G>(x, o);
                for (o, &x) in o[done..].iter_mut().zip(&x[done..]) {
                    *o = G::scalar(x);
                }
            }
            Mode::Chain | Mode::ChainIdentity => unreachable!(),
        }
    }
}

/// Each call's argument depends on the preceding result: its last fraction
/// bit is toggled by the result's, keeping it in the workload's region.
fn chain(xs: &[f64], f: impl Fn(f64) -> f64) -> f64 {
    let mut previous = 0.0_f64;
    for &x in xs {
        previous = f(f64::from_bits(
            x.to_bits() ^ (black_box(previous).to_bits() & 1),
        ));
    }
    previous
}

/// The lane backends this CPU has, widest first, also recorded.
fn lanes() -> Vec<Backend> {
    let lanes: Vec<Backend> = backends()
        .into_iter()
        .filter(|b| !matches!(b, Backend::Scalar(_)))
        .collect();
    let names: Vec<&str> = lanes.iter().map(Backend::name).collect();
    println!("backends,{}", names.join(";"));
    lanes
}

/// Records each table's size in bytes.
pub(crate) fn tables(entries: &[(&str, usize)]) {
    for (name, bytes) in entries {
        println!("table,{name},{bytes}");
    }
}

fn mode_name(mode: Mode, lanes: &[Backend]) -> String {
    match mode {
        Mode::Scalar => String::from("scalar"),
        Mode::Dispatch => String::from("dispatch"),
        Mode::Forced(b) => String::from(lanes[b].name()),
        Mode::Chain => String::from("chain"),
        Mode::ChainIdentity => String::from("chain_identity"),
    }
}

/// Times `G` on each workload, in every mode and length, after checking each
/// mode's bits and counting which path, per `path`, decides each argument.
pub(crate) fn function<G: Kernel>(name: &str, path: Path, workloads: &[(&str, Draw)]) {
    let settings = &settings();
    let lanes = &lanes();
    if !selected(settings.functions.as_ref(), name) {
        return;
    }
    for &(workload, draw) in workloads {
        if !selected(settings.workloads.as_ref(), workload) {
            continue;
        }
        let largest = settings.lengths.iter().copied().max().unwrap_or(POOL);
        let mut rng = SplitMix64::new(seed(name, workload));
        let (all, distinct) = arguments(&draw, path, &mut rng, largest.max(POOL));
        // Paths and bit equality, outside timing.
        let pool = &all[..POOL];
        let mut counts: Vec<(&str, usize)> = Vec::new();
        for &x in pool {
            let (label, y) = path(x);
            assert_eq!(y.to_bits(), G::scalar(x).to_bits(), "{name} path({x:e})");
            match counts.iter_mut().find(|(l, _)| *l == label) {
                Some((_, c)) => *c += 1,
                None => counts.push((label, 1)),
            }
        }
        for (label, count) in counts {
            println!("path,{name},{workload},{label},{count},{POOL}");
        }
        if distinct < POOL {
            println!("path,{name},{workload},distinct_arguments,{distinct},{POOL}");
        }
        // Every (length, mode) cell, and the chains.
        let mut cells: Vec<(usize, Mode)> = vec![(POOL, Mode::Chain), (POOL, Mode::ChainIdentity)];
        for &length in &settings.lengths {
            cells.push((length, Mode::Scalar));
            cells.push((length, Mode::Dispatch));
            cells.extend((0..lanes.len()).map(|b| (length, Mode::Forced(b))));
        }
        let mut out = vec![0.0; all.len()];
        for &(length, mode) in &cells {
            if matches!(mode, Mode::Chain | Mode::ChainIdentity) {
                continue;
            }
            let xs = &all[..length.max(POOL)];
            let out = &mut out[..xs.len()];
            evaluate::<G>(mode, lanes, length, xs, out);
            for (&x, &y) in xs.iter().zip(out.iter()) {
                assert_eq!(y.to_bits(), G::scalar(x).to_bits(), "{name}({x:e})");
            }
        }
        for round in 0..=settings.rounds {
            for i in 0..cells.len() {
                let (length, mode) = cells[(i + round) % cells.len()];
                // Lengths up to the pool sweep it in whole calls; larger
                // ones are one call on their own arguments.
                let xs = if length <= POOL {
                    &all[..POOL - POOL % length]
                } else {
                    &all[..length]
                };
                let out = &mut out[..xs.len()];
                let seconds = sample(settings.seconds, &mut || match mode {
                    Mode::Chain => {
                        black_box(chain(black_box(xs), G::scalar));
                    }
                    Mode::ChainIdentity => {
                        black_box(chain(black_box(xs), |x| x));
                    }
                    _ => {
                        evaluate::<G>(mode, lanes, length, black_box(xs), out);
                        black_box(&mut *out);
                    }
                });
                if round == 0 {
                    continue; // warm-up
                }
                #[allow(clippy::cast_precision_loss)] // measurement sizes
                let per_element = seconds * 1e9 / xs.len() as f64;
                let calls = if matches!(mode, Mode::Chain | Mode::ChainIdentity) {
                    xs.len()
                } else {
                    xs.len().div_ceil(length)
                };
                #[allow(clippy::cast_precision_loss)] // measurement sizes
                let per_call = seconds * 1e9 / calls as f64;
                let length = if matches!(mode, Mode::Chain | Mode::ChainIdentity) {
                    1
                } else {
                    length
                };
                println!(
                    "time,{name},{workload},{length},{},{round},{per_element:.4},{per_call:.4}",
                    mode_name(mode, lanes)
                );
            }
        }
    }
}

/// Each of `exp`, `ln` and `erfcx` on its common
/// range alone and interleaved, each 64-element call followed by a walk of
/// 64 cache lines through a competing buffer of `working_set` bytes, cycled.
/// `walk` times the walks alone; its cost per element is not subtracted.
#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance_cache() {
    let settings = &settings();
    const CALL: usize = 64;
    const LINE: usize = 64;
    let mut rng = SplitMix64::new(seed("cache", "pools"));
    let mut pool = |low: f64, width: f64| -> Vec<f64> {
        (0..POOL)
            .map(|_| low + width * unit_closed_open(rng.next_u64()))
            .collect()
    };
    let exp_xs = pool(-30.0, 30.0);
    let ln_xs = pool(0.5, 1.5);
    let erfcx_xs = pool(-0.5, 16.5);
    let kernels: [(&str, Batched); 3] = [
        ("exp", map::<Exp>),
        ("ln", map::<Ln>),
        ("erfcx", map::<Erfcx>),
    ];
    let inputs = [&exp_xs, &ln_xs, &erfcx_xs];
    for working_set in [0_usize, 16 << 10, 64 << 10, 512 << 10, 4 << 20, 32 << 20] {
        let buffer: Vec<u8> = (0..working_set.max(LINE)).map(|i| i as u8).collect();
        let lines = working_set / LINE;
        let mut cursor = 0;
        let walk = |cursor: &mut usize| {
            if lines == 0 {
                return;
            }
            let mut sum = 0_u8;
            for _ in 0..CALL {
                sum = sum.wrapping_add(buffer[*cursor * LINE]);
                *cursor = (*cursor + 1) % lines;
            }
            black_box(sum);
        };
        let mut out = vec![0.0; POOL];
        // 0..3: one function alone; 3: all three interleaved; 4: walks alone.
        for round in 0..=settings.rounds {
            for i in 0..5 {
                let case = (i + round) % 5;
                let seconds = sample(settings.seconds, &mut || {
                    for c in 0..POOL / CALL {
                        let range = c * CALL..(c + 1) * CALL;
                        match case {
                            0..=2 => kernels[case].1(&inputs[case][range.clone()], &mut out[range]),
                            3 => {
                                for (k, xs) in kernels.iter().zip(inputs) {
                                    k.1(&xs[range.clone()], &mut out[range.clone()]);
                                }
                            }
                            _ => {}
                        }
                        walk(&mut cursor);
                    }
                    black_box(&mut out);
                });
                if round == 0 {
                    continue;
                }
                let (label, elements) = match case {
                    0..=2 => (kernels[case].0, POOL),
                    3 => ("interleaved", 3 * POOL),
                    _ => ("walk", POOL),
                };
                #[allow(clippy::cast_precision_loss)] // measurement sizes
                let ns = seconds * 1e9 / elements as f64;
                println!("cache,{label},{working_set},dispatch,{round},{ns:.4}");
            }
        }
    }
}

/// Which part of the standard-normal composition decides `x` for `op`, and
/// its value: `evaluate`'s branches, for the path counts.
fn decided_by(op: Operation, x: f64) -> (&'static str, f64) {
    if let Some(value) = special(op, x) {
        return ("screen", value);
    }
    if let Some(value) = first_decide(op, x) {
        return ("first", value);
    }
    match fast_decide(op, x) {
        Some(value) => ("fast", value),
        // No stage decided it: `evaluate` takes the accurate path.
        None => ("accurate", normal(op, x)),
    }
}

#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance_normal() {
    static NORMAL_MIXED: [Draw; 5] = [
        Draw::Uniform(-0.5, 1.0),
        Draw::Uniform(-3.0, 3.0),
        Draw::Uniform(0.0, 6.0),
        Draw::Uniform(-36.0, 28.0),
        Draw::Uniform(0.0, 20.0),
    ];
    static NORMAL_BROAD: Draw = Draw::Uniform(-40.0, 80.0);
    let normal_workloads = [
        ("central", Draw::Uniform(-0.5, 1.0)),
        ("ordinary", Draw::Uniform(-5.0, 10.0)),
        ("negative_tail", Draw::Uniform(-36.0, 28.0)),
        ("positive_tail", Draw::Uniform(8.0, 28.0)),
        ("underflow", Draw::Uniform(37.0, 2.0)),
        ("mixed", Draw::Mixed(&NORMAL_MIXED)),
        ("fallback", Draw::Fallback(&NORMAL_BROAD)),
    ];
    function::<Normal<0>>(
        "norm_pdf",
        |x| decided_by(Operation::Pdf, x),
        &normal_workloads,
    );
    function::<Normal<1>>(
        "norm_cdf",
        |x| decided_by(Operation::Cdf, x),
        &normal_workloads,
    );
    function::<Normal<2>>(
        "norm_ccdf",
        |x| decided_by(Operation::Cdf, if x.is_nan() { x } else { -x }),
        &normal_workloads,
    );
    function::<Normal<3>>(
        "norm_cdf_centered",
        |x| decided_by(Operation::Centered, x),
        &normal_workloads,
    );
    function::<Normal<4>>(
        "log_norm_cdf",
        |x| decided_by(Operation::LogCdf, x),
        &normal_workloads,
    );
}
