//! `log_sum_exp` and `log_diff_exp` against the reference fixture
//! (`generators/log_space_reference.py`; docs/log_space.md §9).
//!
//! Exact cases must match bit for bit (any NaN where the fixture says `nan`).
//! A bounded case passes when `lo ≤ ŷ ≤ hi`: the documented bound around the
//! exact result, rounded inward, so the comparison is exact.

use super::{
    log_diff_exp, log_sum_exp, log_sum_exp_and_normalize, log_sum_exp_pairs, scalar_terms, shift,
};
use crate::test_exact::{entries, field, word};
use std::vec::Vec;

const FIXTURE: &str = include_str!("../../../reference/fixtures/log_space.json");

/// A `log_sum_exp` input: its elements' encodings, space-separated.
fn xs(case: &str) -> Vec<f64> {
    field(case, "x")
        .split_whitespace()
        .map(|bits| f64::from_bits(u64::from_str_radix(bits, 16).unwrap()))
        .collect()
}

fn same(got: f64, case: &str) -> bool {
    match field(case, "y") {
        "nan" => got.is_nan(),
        _ => got.to_bits() == word(case, "y").to_bits(),
    }
}

/// Checks every bounded case, and reports how far the results that are not
/// correctly rounded are from RN(y), in ulps of RN(y): `[1, 2, 3, 4–15, ≥ 16]`.
///
/// Distances above one ulp come from cancellation between `m` and `L`: the
/// bound's `β·u·|L|` term is absolute, and can be many ulps of a small `y`.
/// A result on the other side of zero from `RN(y)` counts as `≥ 16`.
fn check_bounded(name: &str, cases: &[&str], f: impl Fn(&str) -> f64) {
    let mut correctly_rounded = 0;
    let mut by_distance = [0usize; 5];
    for case in cases {
        let got = f(case);
        let (lo, hi, rn) = (word(case, "lo"), word(case, "hi"), word(case, "rn"));
        assert!(
            lo <= got && got <= hi,
            "{name} {case}: {got:e} outside [{lo:e}, {hi:e}]"
        );
        if got.to_bits() == rn.to_bits() || (got == 0.0 && rn == 0.0) {
            correctly_rounded += 1;
            continue;
        }
        let same_side = got.is_sign_negative() == rn.is_sign_negative() && got != 0.0 && rn != 0.0;
        let ulps = if same_side {
            got.to_bits().abs_diff(rn.to_bits())
        } else {
            u64::MAX
        };
        by_distance[match ulps {
            1 => 0,
            2 => 1,
            3 => 2,
            4..=15 => 3,
            _ => 4,
        }] += 1;
    }
    std::eprintln!(
        "{name}: {} bounded cases within the bound; {correctly_rounded} correctly rounded; \
         the rest by ulps from RN(y) [1, 2, 3, 4-15, >=16]: {by_distance:?}",
        cases.len()
    );
}

#[test]
fn log_sum_exp_special_values_are_exact() {
    let cases = entries(FIXTURE, &["log_sum_exp", "exact"]);
    assert_eq!(cases.len(), 29);
    for case in cases {
        let got = log_sum_exp(&xs(case));
        assert!(
            same(got, case),
            "{case}: got {got:e} ({:016x})",
            got.to_bits()
        );
    }
}

#[test]
fn log_diff_exp_special_values_are_exact() {
    let cases = entries(FIXTURE, &["log_diff_exp", "exact"]);
    assert_eq!(cases.len(), 21);
    for case in cases {
        let got = log_diff_exp(word(case, "a"), word(case, "b"));
        assert!(
            same(got, case),
            "{case}: got {got:e} ({:016x})",
            got.to_bits()
        );
    }
}

#[test]
fn log_sum_exp_is_within_its_bound() {
    let cases = entries(FIXTURE, &["log_sum_exp", "bounded"]);
    assert_eq!(cases.len(), 651);
    check_bounded("log_sum_exp", &cases, |c| log_sum_exp(&xs(c)));
}

#[test]
fn log_diff_exp_is_within_its_bound() {
    let cases = entries(FIXTURE, &["log_diff_exp", "bounded"]);
    assert_eq!(cases.len(), 451);
    check_bounded("log_diff_exp", &cases, |c| {
        log_diff_exp(word(c, "a"), word(c, "b"))
    });
}

#[test]
fn labelled_cases_are_present() {
    // The hand-picked edge cases carry labels; a regenerated fixture that lost
    // them would silently weaken the tests above.
    for (name, expected) in [("log_sum_exp", 51), ("log_diff_exp", 51)] {
        let labelled = entries(FIXTURE, &[name, "bounded"])
            .into_iter()
            .filter(|c| c.contains("\"label\":"))
            .count();
        assert_eq!(labelled, expected, "{name}");
    }
}

#[test]
fn log_sum_exp_does_not_depend_on_where_zero_mass_sits() {
    let a = log_sum_exp(&[-1.5, 0.25, -3.0]);
    let b = log_sum_exp(&[f64::NEG_INFINITY, -1.5, f64::NEG_INFINITY, 0.25, -3.0]);
    assert_eq!(a.to_bits(), b.to_bits());
}

/// `log_sum_exp` by §3's steps with every exponential a scalar `exp`
/// (`scalar_terms`): the operations the `simd` feature must reproduce bit
/// for bit (decision 7).
fn scalar_log_sum_exp(x: &[f64]) -> f64 {
    match shift(x) {
        Err(y) => y,
        Ok((m, j)) => {
            let t = scalar_terms(x, m, j);
            if t == 0.0 {
                m
            } else {
                m + crate::elementary::ln_1p(t)
            }
        }
    }
}

/// Slices of every length from 0 to 100 at several gap scales, so the
/// terms fill, cross and leave partial chunks, with zero mass, underflowing
/// terms, ties, NaN and `+∞` among them; then a long slice.
fn lane_corpus() -> Vec<Vec<f64>> {
    let mut stream = crate::random::SplitMix64::new(0x1095_1A5E);
    let mut unit = || crate::random::unit_closed_open(stream.next_u64());
    let mut corpus = Vec::new();
    for len in 0..=100 {
        for scale in [1e-12, 1.0, 30.0, 800.0] {
            let top = 40.0 * unit() - 20.0;
            let x: Vec<f64> = (0..len)
                .map(|_| match (16.0 * unit()) as u32 {
                    0 => f64::NEG_INFINITY,
                    1 => top,
                    _ => top - scale * unit(),
                })
                .collect();
            corpus.push(x);
        }
    }
    for special in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, -0.0, f64::MAX] {
        for at in [0, 31, 32, 33, 64, 99] {
            let mut x: Vec<f64> = (0..100).map(|i| -f64::from(i) / 7.0).collect();
            x[at] = special;
            corpus.push(x);
        }
    }
    corpus.push((0..10_000).map(|i| f64::from(i % 997) * -0.75).collect());
    corpus
}

#[test]
fn log_sum_exp_lanes_return_the_scalar_terms_bits() {
    let fixture = entries(FIXTURE, &["log_sum_exp", "exact"])
        .into_iter()
        .chain(entries(FIXTURE, &["log_sum_exp", "bounded"]))
        .map(xs);
    for x in fixture.chain(lane_corpus()) {
        let (got, expected) = (log_sum_exp(&x), scalar_log_sum_exp(&x));
        assert_eq!(got.to_bits(), expected.to_bits(), "{} elements", x.len());
    }
}

/// `log_sum_exp_pairs::<N>` against `log_sum_exp` on each pair, bit for
/// bit, the last batch padded with the first pairs.
fn check_pairs<const N: usize>(pairs: &[[f64; 2]]) {
    for start in (0..pairs.len()).step_by(N) {
        let batch: [[f64; 2]; N] = core::array::from_fn(|i| pairs[(start + i) % pairs.len()]);
        let got = log_sum_exp_pairs(&batch);
        for (y, pair) in got.iter().zip(&batch) {
            let expected = scalar_log_sum_exp(pair);
            assert_eq!(
                y.to_bits(),
                expected.to_bits(),
                "{pair:?} in a batch of {N}"
            );
            assert_eq!(y.to_bits(), log_sum_exp(pair).to_bits(), "{pair:?}");
        }
    }
}

/// §1's normalized pair by its stated operations, one scalar `exp` and
/// `ln_1p` each: `hi` the index of the larger entry, `d = x[lo] − x[hi]`,
/// `p[hi] = −ln_1p(exp(d))`, `p[lo] = d + p[hi]`; `None` when `x[hi] = −∞`.
fn normalized_reference(x: [f64; 2]) -> Option<[f64; 2]> {
    let hi = usize::from(x[1] > x[0]);
    if x[hi] == f64::NEG_INFINITY {
        return None;
    }
    let d = x[1 - hi] - x[hi];
    let top = -crate::elementary::ln_1p(crate::elementary::exp(d));
    let mut p = [0.0; 2];
    p[hi] = top;
    p[1 - hi] = d + top;
    Some(p)
}

/// `log_sum_exp_and_normalize::<N>` against `log_sum_exp` and
/// `normalized_reference` on each pair, bit for bit.
fn check_normalize<const N: usize>(pairs: &[[f64; 2]]) {
    for start in (0..pairs.len()).step_by(N) {
        let batch: [[f64; 2]; N] = core::array::from_fn(|i| pairs[(start + i) % pairs.len()]);
        for ((y, p), pair) in log_sum_exp_and_normalize(&batch).iter().zip(&batch) {
            assert_eq!(y.to_bits(), log_sum_exp(pair).to_bits(), "{pair:?}");
            // A NaN entry is NaN either way; its payload is not specified.
            let bits = |p: &Option<[f64; 2]>| {
                p.map(|p| p.map(|v| if v.is_nan() { u64::MAX } else { v.to_bits() }))
            };
            assert_eq!(
                bits(p),
                bits(&normalized_reference(*pair)),
                "{pair:?} in a batch of {N}"
            );
        }
    }
}

/// The pairs both batched tests run on: every pairing of twelve special
/// values, the fixture's pairs, and 40,000 random pairs.
fn pair_corpus() -> Vec<[f64; 2]> {
    let specials = [
        f64::NAN,
        -f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        0.0,
        -0.0,
        1.0,
        -800.0,
        -745.1,
        f64::MAX,
        -f64::MAX,
        f64::MIN_POSITIVE,
    ];
    let mut pairs: Vec<[f64; 2]> = specials
        .iter()
        .flat_map(|&a| specials.map(|b| [a, b]))
        .collect();
    pairs.extend(
        entries(FIXTURE, &["log_sum_exp", "bounded"])
            .into_iter()
            .map(xs)
            .filter(|x| x.len() == 2)
            .map(|x| [x[0], x[1]]),
    );
    let mut stream = crate::random::SplitMix64::new(0x1095_0A12);
    for _ in 0..20_000 {
        let a = f64::from_bits(stream.next_u64());
        let gap = 1000.0 * crate::random::unit_closed_open(stream.next_u64());
        pairs.push([a, a - gap]);
        pairs.push([-gap, f64::from_bits(stream.next_u64())]);
    }
    pairs
}

#[test]
fn log_sum_exp_and_normalize_lanes_return_the_scalar_bits() {
    let pairs = pair_corpus();
    check_normalize::<1>(&pairs);
    check_normalize::<2>(&pairs);
    check_normalize::<3>(&pairs);
    check_normalize::<8>(&pairs);
    check_normalize::<17>(&pairs);
}

#[test]
fn log_sum_exp_pairs_lanes_return_log_sum_exps_bits() {
    let pairs = pair_corpus();
    check_pairs::<1>(&pairs);
    check_pairs::<2>(&pairs);
    check_pairs::<3>(&pairs);
    check_pairs::<8>(&pairs);
    check_pairs::<17>(&pairs);
}

/// Local cost, for docs/log_space.md §8: `cargo test --release -p
/// morphiq-numerics measure_cost -- --ignored --nocapture`. Not a gate.
#[test]
#[ignore = "a local measurement, not a check"]
fn measure_cost() {
    use std::time::Instant;
    let mut stream = crate::random::SplitMix64::new(0x1095_C057);
    let mut unit = || crate::random::unit_closed_open(stream.next_u64());
    let pairs: Vec<(f64, f64)> = (0..1 << 16)
        .map(|_| {
            let a = 40.0 * unit() - 20.0;
            (a, a - 30.0 * unit() - 1e-9)
        })
        .collect();
    type Binary = fn(f64, f64) -> f64;
    let functions: [(&str, Binary); 2] = [
        ("log_sum_exp, n = 2", |a, b| log_sum_exp(&[a, b])),
        ("log_diff_exp", log_diff_exp),
    ];
    for (name, f) in functions {
        let mut sink = 0.0;
        let start = Instant::now();
        for _ in 0..16 {
            for &(a, b) in &pairs {
                sink += f(core::hint::black_box(a), core::hint::black_box(b));
            }
        }
        #[allow(clippy::cast_precision_loss)] // timing arithmetic
        let ns = start.elapsed().as_nanos() as f64 / (16.0 * pairs.len() as f64);
        std::eprintln!("{name}: {ns:.1} ns per call ({sink:e})");
    }
    // Two pairs per call, as a two-state recursion's step forms them.
    let mut sink = 0.0;
    let start = Instant::now();
    for _ in 0..16 {
        for two in pairs.chunks_exact(2) {
            let batch = [[two[0].0, two[0].1], [two[1].0, two[1].1]];
            let y = log_sum_exp_pairs(core::hint::black_box(&batch));
            sink += y[0] + y[1];
        }
    }
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let ns = start.elapsed().as_nanos() as f64 / (16.0 * pairs.len() as f64);
    std::eprintln!("log_sum_exp_pairs, N = 2: {ns:.1} ns per pair ({sink:e})");
    // A log-sum and its normalized pair, one pair per call as a filter step
    // forms it, against log_sum_exp and the normalization done separately.
    let mut sink = 0.0;
    let start = Instant::now();
    for _ in 0..16 {
        for &(a, b) in &pairs {
            let [(y, p)] = log_sum_exp_and_normalize(core::hint::black_box(&[[a, b]]));
            sink += y + p.map_or(0.0, |p| p[0]);
        }
    }
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let ns = start.elapsed().as_nanos() as f64 / (16.0 * pairs.len() as f64);
    std::eprintln!("log_sum_exp_and_normalize, N = 1: {ns:.1} ns per pair ({sink:e})");
    let mut sink = 0.0;
    let start = Instant::now();
    for _ in 0..16 {
        for &(a, b) in &pairs {
            let x = core::hint::black_box([a, b]);
            sink += log_sum_exp(&x) + normalized_reference(x).map_or(0.0, |p| p[0]);
        }
    }
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let ns = start.elapsed().as_nanos() as f64 / (16.0 * pairs.len() as f64);
    std::eprintln!("log_sum_exp + separate normalization: {ns:.1} ns per pair ({sink:e})");
    // One long slice, as a sum over a series.
    let long: Vec<f64> = pairs.iter().take(1_000).map(|&(_, b)| b).collect();
    let mut sink = 0.0;
    let start = Instant::now();
    for _ in 0..1_000 {
        sink += log_sum_exp(core::hint::black_box(&long));
    }
    #[allow(clippy::cast_precision_loss)] // timing arithmetic
    let ns = start.elapsed().as_nanos() as f64 / (1_000.0 * long.len() as f64);
    std::eprintln!("log_sum_exp, n = 1000: {ns:.1} ns per element ({sink:e})");
}
