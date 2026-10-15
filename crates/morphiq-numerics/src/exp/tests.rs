//! The stages and the fallback's fast path against the accurate path, their
//! pass rates, and every unrounded value against its certified bound
//! (docs/exp.md §7, §8, §10).

use super::{
    E_A, E_B, EPS, Reduced, Stages, X_OVERFLOW, X_ZERO, exp, fallback, small, small_parts,
};
use crate::q128::Q128;
use crate::random::{SplitMix64, unit_closed_open};
use crate::test_exact::{Exact, entries, field, word};

/// The analytic miss rate of the fallback's rounding test (§8.2): about `2^−15`.
const ANALYTIC_MISS_RATE: f64 = 1.0 / 32768.0;
/// The analytic miss rates of the stages' tests (§7): `2·E/ulp(1)`, about
/// `2^−7.4` for stage A and `2^−17` for stage B.
const ANALYTIC_MISS_RATE_A: f64 = 3.0 / 512.0;
const ANALYTIC_MISS_RATE_B: f64 = 1.0 / 131_072.0;

/// An argument the stages take, `|x| < 704`: uniform, or one in four of
/// magnitude `2^−e`, `0 ≤ e < 64`, either sign.
fn stage_argument(rng: &mut SplitMix64) -> f64 {
    let u = unit_closed_open(rng.next_u64());
    if rng.next_u64().is_multiple_of(4) {
        let e = rng.next_u64() % 64;
        let x = (1.0 + u) * f64::from_bits((1023 - e) << 52) * 0.5;
        if rng.next_u64() & 1 == 1 { -x } else { x }
    } else {
        // 704 itself is excluded: 1408·u − 704 < 704.
        1408.0 * u - 704.0
    }
}

/// Each stage, when its test passes, against the old algorithm, which is
/// the fallback (§8): equal bits. Both stages run on every argument, so
/// stage B is checked where stage A decides too.
fn stages_agree_with_the_fallback(seed: u64, samples: u64) -> (u64, u64) {
    let mut rng = SplitMix64::new(seed);
    let (mut missed_a, mut missed_b) = (0, 0);
    for _ in 0..samples {
        let x = stage_argument(&mut rng);
        let reference = fallback(x).to_bits();
        let stages = Stages::of(x);
        match stages.a() {
            Some(y) => assert_eq!(y.to_bits(), reference, "stage A, exp({x:e})"),
            None => missed_a += 1,
        }
        match stages.b() {
            Some(y) => assert_eq!(y.to_bits(), reference, "stage B, exp({x:e})"),
            None => missed_b += 1,
        }
        assert_eq!(exp(x).to_bits(), reference, "exp({x:e})");
    }
    (missed_a, missed_b)
}

#[test]
fn stages_agree_with_the_fallback_and_mostly_decide() {
    let samples = 1 << 20;
    let (missed_a, missed_b) = stages_agree_with_the_fallback(0x6578_705f_7374_6167, samples);
    #[allow(clippy::cast_precision_loss)] // counts below 2^53
    let (rate_a, rate_b) = (
        missed_a as f64 / samples as f64,
        missed_b as f64 / samples as f64,
    );
    std::eprintln!("exp stage A: {missed_a} of {samples} undecided ({rate_a:.3e})");
    std::eprintln!("exp stage B: {missed_b} of {samples} undecided ({rate_b:.3e})");
    assert!(
        rate_a <= 2.0 * ANALYTIC_MISS_RATE_A,
        "stage A miss rate {rate_a:e}"
    );
    assert!(
        rate_b <= 4.0 * ANALYTIC_MISS_RATE_B,
        "stage B miss rate {rate_b:e}"
    );
}

/// The same on a large corpus: `MORPHIQ_EXP_SAMPLES` arguments (default
/// 2^28). Ignored by default; run with
/// `cargo test --release -p morphiq-numerics --lib stages_agree_on_a_large_corpus -- --ignored`.
#[test]
#[ignore = "a long check, run on demand"]
fn stages_agree_on_a_large_corpus() {
    let samples = std::env::var("MORPHIQ_EXP_SAMPLES").map_or(1 << 28, |s| s.parse().unwrap());
    let threads = 8;
    let undecided = std::thread::scope(|scope| {
        let handles: std::vec::Vec<_> = (0..threads)
            .map(|t| {
                scope.spawn(move || {
                    stages_agree_with_the_fallback(0x6578_705f_6c61_7267 + t, samples / threads)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .fold((0, 0), |(a, b), (c, d)| (a + c, b + d))
    });
    std::eprintln!(
        "exp stages on {} arguments: A undecided {}, B undecided {}",
        samples / threads * threads,
        undecided.0,
        undecided.1
    );
}

/// The stages' test constants are their definitions (§5, §6). As with `EPS`,
/// results can't check them: a smaller bound would rarely change a result,
/// but it would void the proof.
#[test]
fn stage_bounds_are_their_definitions() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(E_A.to_bits(), (1.5 * two(-61)).to_bits());
    assert_eq!(E_B.to_bits(), two(-70).to_bits());
}

#[test]
fn fast_path_agrees_with_the_accurate_path_and_mostly_decides() {
    let mut rng = SplitMix64::new(0x6578_705f_7061_7373);
    let samples = 1u32 << 20;
    let (mut tried, mut missed) = (0u32, 0u32);
    for _ in 0..samples {
        // Uniform over the arguments with a finite, nonzero result.
        #[allow(clippy::cast_precision_loss)] // 53-bit integer
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = X_ZERO + u * (X_OVERFLOW - X_ZERO);
        let reduced = Reduced::of(x);
        if reduced.k < -1021 {
            continue;
        }
        tried += 1;
        match reduced.fast() {
            Some(y) => assert_eq!(y.to_bits(), reduced.accurate().to_bits(), "exp({x:e})"),
            None => missed += 1,
        }
    }
    let rate = f64::from(missed) / f64::from(tried);
    std::eprintln!("exp fast path: {missed} of {tried} sent to the accurate path ({rate:.3e})");
    assert!(rate <= 4.0 * ANALYTIC_MISS_RATE, "miss rate {rate:e}");
}

#[test]
fn small_arguments_agree_with_the_general_accurate_path() {
    let mut rng = SplitMix64::new(0x6578_705f_736d_616c);
    for _ in 0..20_000 {
        // 2^-54 <= |x| < 2^-30, every binade.
        let e = 969 + rng.next_u64() % 24;
        let x = f64::from_bits((e << 52) | (rng.next_u64() >> 12) | (rng.next_u64() & 1) << 63);
        if (-f64::from_bits(0x3c90_0000_0000_0000)..f64::from_bits(0x3ca0_0000_0000_0000))
            .contains(&x)
        {
            continue;
        }
        assert_eq!(
            small(x).to_bits(),
            Reduced::of(x).accurate().to_bits(),
            "exp({x:e})"
        );
    }
}

/// The fixture's 192-bit references: `(x, e^x)`.
fn precise() -> std::vec::Vec<(f64, Exact)> {
    let fixture = include_str!("../../../reference/fixtures/exp.json");
    entries(fixture, &["precise"])
        .into_iter()
        .map(|c| {
            let e = field(c, "e").parse().unwrap();
            (word(c, "x"), Exact::of_hex(field(c, "m"), e))
        })
        .collect()
}

#[test]
fn every_unrounded_result_is_within_its_certified_bound() {
    let small_arguments = f64::from_bits(0x3e10_0000_0000_0000);
    let cases = precise();
    assert_eq!(cases.len(), 1200);
    for (x, reference) in cases {
        let reduced = Reduced::of(x);
        // §8.4, general case: below 2^-123.9 (1097/1024 * 2^-124 < 2^-123.9).
        let y = Exact::of(reduced.accurate_value());
        assert!(y.within(&reference, 1097, 134), "accurate path, exp({x:e})");
        if reduced.k >= -1021 {
            // §8.2: eps_1 = 2^-69, relative to 2^(j/128) e^r = e^x / 2^k.
            let y = reduced.fast_value();
            let y = Exact::of(Q128::from_f64(y.hi()))
                .add(&Exact::of(Q128::from_f64(y.lo())))
                .mul(&Exact::pow2(i64::from(reduced.k)));
            assert!(y.within(&reference, 1, 69), "fast path, exp({x:e})");
        }
        if x.abs() < 704.0 {
            // §5 and §6: y + l within the certified bound of 2^(j/512) e^r =
            // e^x / 2^k, absolutely: 0x1.2ep-61 < 5/4 2^-61 for stage A,
            // 0x1.a2p-71 < 7/4 2^-71 for stage B.
            let stages = Stages::of(x);
            let k = stages.jk().1;
            for ((y, l), numerator, shift) in [(stages.a_value(), 5, 63), (stages.b_value(), 7, 73)]
            {
                let error = Exact::of_f64(y)
                    .add(&Exact::of_f64(l))
                    .mul(&Exact::pow2(k))
                    .sub(&reference)
                    .abs();
                let bound = Exact::of_f64(f64::from(numerator)).mul(&Exact::pow2(k - shift));
                assert!(
                    error.cmp(&bound) != core::cmp::Ordering::Greater,
                    "stage bound 2^-{shift}·{numerator}, exp({x:e})"
                );
            }
        }
        if x.abs() < small_arguments {
            // §8.4, small arguments: within 2^-178, absolutely; e^x < 2 here.
            let (h, w) = small_parts(x);
            let error = Exact::of(Q128::from_f64(h))
                .add(&Exact::of(w))
                .sub(&reference)
                .abs();
            assert!(
                error.cmp(&Exact::pow2(-178)) != core::cmp::Ordering::Greater,
                "small path, exp({x:e})"
            );
        }
    }
}

/// The rounding test's constant is `ε₁·(1 + 2^−50)` with `ε₁ = 2^−69` (§8.3).
/// Results can't check it: the fast path's actual error is far below `ε₁`, so
/// a smaller constant would rarely change a result, but it would void §8.3's
/// proof.
#[test]
fn rounding_test_constant_is_its_definition() {
    let two = |k: i32| f64::from_bits(u64::try_from(1023 + k).unwrap() << 52);
    assert_eq!(EPS.to_bits(), (two(-69) * (1.0 + two(-50))).to_bits());
}

/// Time per call of `exp` and of `fallback` (the algorithm before the
/// stages) on shuffled grids of 4,096 arguments: throughput (independent
/// calls) and latency (each argument depends on the previous result), the
/// median of 7 rounds. A local measurement (docs/exp.md §11), not a check:
/// `cargo test --release -p morphiq-numerics --lib exp::tests::measure_cost
/// -- --ignored --nocapture`.
#[test]
#[ignore = "a local measurement, not a check"]
fn measure_cost() {
    use core::hint::black_box;
    use std::time::Instant;
    let grid = |lo: f64, hi: f64| {
        let mut rng = SplitMix64::new(0x6578_705f_636f_7374);
        let mut v: std::vec::Vec<f64> = (0..4096)
            .map(|i| lo + (hi - lo) * (f64::from(i) + 0.5) / 4096.0)
            .collect();
        for i in (1..v.len()).rev() {
            let j = usize::try_from(rng.next_u64() % (i as u64 + 1)).unwrap();
            v.swap(i, j);
        }
        v
    };
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let per_call = |start: Instant, calls: usize| start.elapsed().as_nanos() as f64 / calls as f64;
    let throughput = |f: fn(f64) -> f64, xs: &[f64]| {
        let mut out = std::vec![0.0; xs.len()];
        let start = Instant::now();
        for _ in 0..2000 {
            for (x, y) in xs.iter().zip(out.iter_mut()) {
                *y = f(black_box(*x));
            }
            black_box(&out);
        }
        per_call(start, 2000 * xs.len())
    };
    let latency = |f: fn(f64) -> f64, xs: &[f64]| {
        let zero = black_box(0.0);
        let mut y = 0.0;
        let start = Instant::now();
        for _ in 0..2000 {
            for &x in xs {
                y = f(x + y * zero);
            }
        }
        black_box(y);
        per_call(start, 2000 * xs.len())
    };
    let median = |mut v: std::vec::Vec<f64>| {
        v.sort_by(f64::total_cmp);
        v[v.len() / 2]
    };
    for (name, lo, hi) in [
        ("[-30, 0]", -30.0, 0.0),
        ("[-1, 1]", -1.0, 1.0),
        ("[-700, 700]", -700.0, 700.0),
    ] {
        let xs = grid(lo, hi);
        for (label, f) in [("exp", exp as fn(f64) -> f64), ("fallback", fallback)] {
            let t = median((0..7).map(|_| throughput(f, &xs)).collect());
            let l = median((0..7).map(|_| latency(f, &xs)).collect());
            std::eprintln!("{label:8} {name:12} throughput {t:6.2} ns, latency {l:6.2} ns");
        }
    }
}

/// Which part of `exp` decides `x`, and its value: `exp`'s branches, for the
/// native measurements' path counts.
#[cfg(feature = "simd")]
fn decided_by(x: f64) -> (&'static str, f64) {
    use super::{MAGNITUDE, ONE_HIGH, ONE_LOW, STAGES, Stages, X_OVERFLOW, X_ZERO, fallback};
    if x.to_bits() & MAGNITUDE < STAGES {
        let stages = Stages::of(x);
        if let Some(y) = stages.a() {
            return ("stage_a", y);
        }
        if let Some(y) = stages.b() {
            return ("stage_b", y);
        }
    }
    if x.is_nan() || x >= X_OVERFLOW || x <= X_ZERO || (ONE_LOW..ONE_HIGH).contains(&x) {
        return ("screen", fallback(x));
    }
    let reduced = Reduced::of(x);
    if reduced.k >= -1021
        && let Some(y) = reduced.fast()
    {
        return ("fast", y);
    }
    ("accurate", fallback(x))
}

/// Same-host timing of `exp`, scalar and per lane backend
/// (`lanes::tests::bench`); no timing assertion.
#[cfg(feature = "simd")]
#[test]
#[ignore = "same-host release-mode measurement; no timing assertions"]
fn native_performance() {
    use crate::lanes::tests::bench::{Draw, function, tables};
    use core::mem::size_of_val;
    tables(&[
        ("exp::POLY", size_of_val(&super::tables::POLY)),
        ("exp::T_BITS", size_of_val(&super::tables::T_BITS)),
        ("exp::T_Q128", size_of_val(&super::tables::T_Q128)),
        ("exp::RECIPROCALS", size_of_val(&super::tables::RECIPROCALS)),
        ("exp::POLY_S", size_of_val(&super::tables::POLY_S)),
        ("exp::S_T", size_of_val(&super::tables::S_T)),
    ]);
    static EXP_SCREENED: [f64; 8] = [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        709.79,
        710.0,
        1000.0,
        -746.0,
        -1000.0,
    ];
    static EXP_DOMAIN: Draw = Draw::Uniform(-745.0, 1454.0);
    static EXP_MIXED: [Draw; 4] = [
        Draw::Uniform(-30.0, 30.0),
        Draw::Uniform(-745.0, 1454.0),
        Draw::Values(&EXP_SCREENED),
        Draw::Uniform(-745.0, 36.6),
    ];
    function::<crate::exp::lanes::Exp>(
        "exp",
        decided_by,
        &[
            ("common", Draw::Uniform(-30.0, 30.0)),
            ("unit", Draw::Uniform(-1.0, 2.0)),
            ("domain", EXP_DOMAIN),
            ("subnormal", Draw::Uniform(-745.0, 36.6)),
            ("screened", Draw::Values(&EXP_SCREENED)),
            ("mixed", Draw::Mixed(&EXP_MIXED)),
            ("fallback", Draw::Fallback(&EXP_DOMAIN)),
        ],
    );
}
