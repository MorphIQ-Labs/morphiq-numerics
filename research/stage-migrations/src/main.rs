//! Reproduce from the repository root:
//! cargo run --release --locked --manifest-path research/stage-migrations/Cargo.toml -- check /tmp/stage-cases.jsonl
//! target/generators-venv/bin/python research/stage-migrations/oracle_check.py /tmp/stage-cases.jsonl
//! cargo run --release --locked --manifest-path research/stage-migrations/Cargo.toml -- bench
//!
//! `check` compares every reference fixture, random encodings, stratified
//! domains and reduction/branch boundaries. Its optional JSONL export samples
//! each family for an independent interval-oracle check. `bench` alternates
//! candidate/baseline order and reports distributions, with rates counted in
//! a separate untimed pass. No consumer, platform libm, or CI timing required.

use morphiq_numerics::elementary;
use morphiq_stage_migrations::{self as candidate, Trial};
use std::hint::black_box;
use std::io::{BufWriter, Write};
use std::time::Instant;

type Function = fn(f64) -> f64;
type Stage = fn(f64) -> Trial;

struct Kernel {
    name: &'static str,
    baseline: Function,
    candidate: Function,
    stage: Stage,
}

const KERNELS: [Kernel; 3] = [
    Kernel {
        name: "ln",
        baseline: elementary::ln,
        candidate: candidate::ln,
        stage: candidate::ln_trial,
    },
    Kernel {
        name: "exp2",
        baseline: elementary::exp2,
        candidate: candidate::exp2,
        stage: candidate::exp2_trial,
    },
    Kernel {
        name: "expm1",
        baseline: elementary::expm1,
        candidate: candidate::expm1,
        stage: candidate::expm1_trial,
    },
];

struct Words(u64);
impl Words {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 * f64::from_bits(0x3ca0000000000000)
    }
}

fn agree(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}
fn word(v: &serde_json::Value) -> f64 {
    f64::from_bits(u64::from_str_radix(v.as_str().unwrap(), 16).unwrap())
}

fn fixtures(k: &Kernel) -> usize {
    let path = format!(
        "{}/../../crates/reference/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        k.name
    );
    let fixture: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let rows = fixture[if k.name == "ln" { "ln" } else { "cases" }]
        .as_array()
        .unwrap();
    for row in rows {
        let x = word(&row["x"]);
        let expected = word(&row[k.name]);
        let actual = (k.candidate)(x);
        assert!(
            agree(actual, expected),
            "fixture {}({:016x}): {:016x} != {:016x}",
            k.name,
            x.to_bits(),
            actual.to_bits(),
            expected.to_bits()
        );
    }
    rows.len()
}

#[derive(Default)]
struct Counts {
    n: usize,
    a: usize,
    b: usize,
    screened: usize,
    undecided: usize,
}
impl Counts {
    fn add(&mut self, t: Trial) {
        self.n += 1;
        match t {
            Trial::Decided(_, 1) => self.a += 1,
            Trial::Decided(_, 2) => self.b += 1,
            Trial::Decided(_, s) => panic!("unknown stage {s}"),
            Trial::Screened => self.screened += 1,
            Trial::Undecided => self.undecided += 1,
        }
    }
    fn print(&self, name: &str, family: &str) {
        println!(
            "{name}/{family}: n={} A={} B={} screened={} undecided={}",
            self.n, self.a, self.b, self.screened, self.undecided
        );
    }
}

fn neighbors(xs: &mut Vec<f64>, x: f64) {
    for offset in -2i64..=2 {
        xs.push(f64::from_bits(x.to_bits().wrapping_add_signed(offset)));
    }
}

fn corpus(k: &Kernel, name: &str, xs: &[f64], dump: &mut Option<BufWriter<std::fs::File>>) {
    let mut counts = Counts::default();
    let stride = (xs.len() / 512).max(1);
    let mut hard = 0;
    for (i, &x) in xs.iter().enumerate() {
        let stage = (k.stage)(x);
        counts.add(stage);
        let baseline = (k.baseline)(x);
        let actual = (k.candidate)(x);
        assert!(
            agree(actual, baseline),
            "{} {name}({:016x}): {:016x} != baseline {:016x}",
            k.name,
            x.to_bits(),
            actual.to_bits(),
            baseline.to_bits()
        );
        if let Trial::Decided(v, _) = stage {
            assert!(agree(v, actual));
        }
        let stage_b = matches!(stage, Trial::Decided(_, 2));
        let unresolved = matches!(stage, Trial::Undecided);
        let selected = i % stride == 0 || ((stage_b || unresolved) && hard < 128);
        if (stage_b || unresolved) && selected {
            hard += 1;
        }
        if selected && let Some(out) = dump {
            let row = serde_json::json!({"function": k.name, "family": name, "x": format!("{:016x}",x.to_bits()), "actual": format!("{:016x}", actual.to_bits()), "stage": format!("{stage:?}")});
            writeln!(out, "{row}").unwrap();
        }
    }
    counts.print(k.name, name);
}

fn check(path: Option<String>) {
    let mut dump = path.map(|p| BufWriter::new(std::fs::File::create(p).unwrap()));
    for (index, k) in KERNELS.iter().enumerate() {
        println!(
            "{}: {} independent reference fixtures passed",
            k.name,
            fixtures(k)
        );
        let mut words = Words(0x6d69677261746573 ^ index as u64);
        let xs: Vec<_> = (0..1_000_000)
            .map(|_| f64::from_bits(words.next()))
            .collect();
        corpus(k, "encodings", &xs, &mut dump);
        let xs: Vec<_> = (0..1_000_000)
            .map(|_| match k.name {
                "ln" => f64::from_bits(1 + words.next() % 0x7fefffffffffffff),
                "exp2" => -1076.0 + words.unit() * 2101.0,
                _ => -40.0 + words.unit() * 750.0,
            })
            .collect();
        corpus(k, "domain", &xs, &mut dump);
        let mut xs = Vec::new();
        match k.name {
            "ln" => {
                // Every new-table boundary at every normal exponent; the
                // scaling transition and subnormal encodings are separate.
                for e in -1022i64..=1023 {
                    for i in 0..=512u64 {
                        let b = (0x3fe6a00000000000u64 + (i << 43)).wrapping_add_signed(e << 52);
                        if b > 0 && b < 0x7ff0000000000000 {
                            neighbors(&mut xs, f64::from_bits(b));
                        }
                    }
                }
                for b in 1..=65536 {
                    xs.push(f64::from_bits(b));
                }
                neighbors(&mut xs, f64::MIN_POSITIVE);
                neighbors(&mut xs, f64::MAX);
            }
            "exp2" => {
                // All dyadic reduction grid points AND half-grid ties across
                // the whole live range, and both neighboring encodings.
                for n in -1_101_824..=1_049_600 {
                    neighbors(&mut xs, f64::from(n) / 1024.0);
                }
                for x in [-1075.0, -1074.0, -1022.0, -1016.0, 1016.0, 1024.0] {
                    neighbors(&mut xs, x);
                }
            }
            _ => {
                // Approximate real n*ln(2)/1024 boundaries, ±2 encodings;
                // this is input generation, not an output oracle.
                let ln2 = f64::from_bits(0x3fe62e42fefa39ef);
                for n in -56000..=1040000 {
                    neighbors(&mut xs, f64::from(n) * (ln2 / 1024.0));
                }
                for x in [
                    -37.0,
                    -0.03125,
                    0.03125,
                    704.0,
                    f64::from_bits(0xc042b708872320e2),
                    f64::from_bits(0x40862e42fefa39f0),
                ] {
                    neighbors(&mut xs, x);
                }
            }
        }
        corpus(k, "reduction-edges", &xs, &mut dump);
        let mut xs = Vec::new();
        for i in -200000i64..=200000 {
            let center = if k.name == "ln" {
                1.0f64.to_bits()
            } else {
                0.0f64.to_bits()
            };
            xs.push(f64::from_bits(center.wrapping_add_signed(i)));
        }
        if k.name != "ln" {
            for e in -1074..=9 {
                let magnitude = if e < -1022 {
                    f64::from_bits(1 << (e + 1074))
                } else {
                    f64::from_bits(((1023 + e) as u64) << 52)
                };
                neighbors(&mut xs, magnitude);
                neighbors(&mut xs, -magnitude);
            }
        }
        corpus(k, "near-zero-or-one", &xs, &mut dump);
    }
    if let Some(mut out) = dump {
        out.flush().unwrap();
    }
}

fn elapsed(f: Function, xs: &[f64], reps: usize) -> f64 {
    let start = Instant::now();
    for _ in 0..reps {
        for &x in xs {
            black_box(f(black_box(x)));
        }
    }
    start.elapsed().as_secs_f64() * 1e9 / (reps * xs.len()) as f64
}

#[inline(always)]
fn chain_input(prev: f64, anchor: f64, step: f64) -> f64 {
    // Mix all output bits. Using only the low fraction bits made the
    // ln workload at anchor=1 stick forever at ln(1)=0.
    let bits = prev
        .to_bits()
        .wrapping_mul(0xbf58476d1ce4e5b9)
        .wrapping_add(0x9e3779b97f4a7c15);
    anchor + (bits >> 11) as f64 * step
}

fn check_chain(k: &Kernel, name: &str, anchor: f64, step: f64) {
    let mut prev = 1.0;
    let mut seen = std::collections::HashSet::new();
    let mut counts = Counts::default();
    for _ in 0..4096 {
        let x = chain_input(prev, anchor, step);
        seen.insert(x.to_bits());
        let baseline = (k.baseline)(x);
        assert!(agree(baseline, (k.candidate)(x)));
        counts.add((k.stage)(x));
        prev = baseline;
    }
    assert!(
        seen.len() >= 256,
        "{} {name}: degenerate latency chain",
        k.name
    );
    counts.print(k.name, &format!("{name}-chain"));
}

fn latency(f: Function, anchor: f64, step: f64, n: usize) -> f64 {
    let mut prev = 1.0f64;
    let start = Instant::now();
    for _ in 0..n {
        let x = chain_input(prev, anchor, step);
        prev = black_box(f(black_box(x)));
    }
    black_box(prev);
    start.elapsed().as_secs_f64() * 1e9 / n as f64
}

fn summary(mut v: Vec<f64>) -> String {
    v.sort_by(f64::total_cmp);
    format!("{:.2} [{:.2}, {:.2}]", v[v.len() / 2], v[0], v[v.len() - 1])
}

fn bench() {
    println!(
        "ns/call: median [min, max], 9 alternating rounds; indirect scalar calls; 4096-element input; ~10 ms per throughput sample; no instrumentation in timing"
    );
    for (index, k) in KERNELS.iter().enumerate() {
        let workloads: &[(&str, f64, f64)] = match k.name {
            "ln" => &[("near-one", 0.5, 1.5), ("moderate", 1.0, 999.0)],
            "exp2" => &[
                ("negative", -30.0, 30.0),
                ("normal-domain", -1015.0, 2030.0),
            ],
            _ => &[
                ("negative", -30.0, 29.96875),
                ("cancellation", -0.25, 0.5),
                ("positive", 0.03125, 699.96875),
            ],
        };
        let mut words = Words(0x74696d656d696772 ^ index as u64);
        for &(name, anchor, width) in workloads {
            let xs: Vec<_> = (0..4096).map(|_| anchor + width * words.unit()).collect();
            for &x in &xs {
                assert!(agree((k.candidate)(x), (k.baseline)(x)));
            }
            let mut counts = Counts::default();
            for &x in &xs {
                counts.add((k.stage)(x));
            }
            counts.print(k.name, name);
            check_chain(k, name, anchor, width * f64::from_bits(0x3ca0000000000000));
            elapsed(k.baseline, &xs, 32);
            elapsed(k.candidate, &xs, 32);
            let once = elapsed(k.baseline, &xs, 128).max(0.1);
            let reps = (10_000_000.0 / (once * xs.len() as f64)) as usize + 1;
            let mut old = Vec::new();
            let mut new = Vec::new();
            let mut old_lat = Vec::new();
            let mut new_lat = Vec::new();
            for round in 0..9 {
                for which in if round % 2 == 0 { [0, 1] } else { [1, 0] } {
                    let f = if which == 0 { k.baseline } else { k.candidate };
                    let ns = elapsed(f, &xs, reps);
                    let lat = latency(
                        f,
                        anchor,
                        width * f64::from_bits(0x3ca0000000000000),
                        200_000,
                    );
                    if which == 0 {
                        old.push(ns);
                        old_lat.push(lat);
                    } else {
                        new.push(ns);
                        new_lat.push(lat);
                    }
                }
            }
            println!(
                "{}/{} throughput baseline={} candidate={}; chain latency baseline={} candidate={}",
                k.name,
                name,
                summary(old),
                summary(new),
                summary(old_lat),
                summary(new_lat)
            );
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("check") => check(args.next()),
        Some("bench") => bench(),
        _ => {
            eprintln!("usage: morphiq-stage-migrations check [oracle-export.jsonl] | bench");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidates_match_every_independent_reference_fixture() {
        for kernel in &KERNELS {
            fixtures(kernel);
        }
    }

    #[test]
    fn latency_chains_visit_distinct_inputs_and_preserve_baseline_outputs() {
        for (kernel, anchor, width) in [
            (&KERNELS[0], 0.5, 1.5),
            (&KERNELS[0], 1.0, 999.0),
            (&KERNELS[1], -30.0, 30.0),
            (&KERNELS[1], -1015.0, 2030.0),
            (&KERNELS[2], -30.0, 29.96875),
            (&KERNELS[2], -0.25, 0.5),
            (&KERNELS[2], 0.03125, 699.96875),
        ] {
            check_chain(
                kernel,
                "regression",
                anchor,
                width * f64::from_bits(0x3ca0000000000000),
            );
        }
    }
}
