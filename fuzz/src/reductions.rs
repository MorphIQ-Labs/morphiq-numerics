//! Reductions, mergeable moments and log-space arithmetic against MPFR and the
//! contracts in docs/reduce.md, docs/moments.md, docs/log_space.md and
//! docs/log_normalize.md.
//!
//! [`WIDE`] bits hold the sums, products and squared sums of these short
//! slices exactly, so every algebraic bound is checked without division.
use morphiq_numerics::log_space::{self, NormalizeError};
use morphiq_numerics::reduce::{self, MomentEstimate, Moments2, MomentsError};
use morphiq_numerics::{eft, elementary};
use rug::{Float, float::Round};

/// Binary64 products span 2^-2148 to 2^2048; squared sums of 64 terms double
/// that span.
const WIDE: u32 = 8600;
/// The runner's 1041-byte packets hold at most 129 words.
const TERMS: usize = 129;

fn exact(x: f64) -> Float {
    Float::with_val(WIDE, x)
}

fn power(k: i32) -> Float {
    let one = Float::with_val(WIDE, 1);
    if k >= 0 {
        one << k as u32
    } else {
        one >> k.unsigned_abs()
    }
}

fn exactly<T>(value: T) -> Float
where
    Float: rug::ops::AssignRound<T, Round = Round, Ordering = std::cmp::Ordering>,
{
    let (result, order) = Float::with_val_round(WIDE, value, Round::Nearest);
    assert_eq!(order, std::cmp::Ordering::Equal, "inexact oracle step");
    result
}

fn add(a: &Float, b: &Float) -> Float {
    exactly(a + b)
}

fn sub(a: &Float, b: &Float) -> Float {
    exactly(a - b)
}

fn mul(a: &Float, b: &Float) -> Float {
    exactly(a * b)
}

fn magnitude(x: &Float) -> Float {
    x.clone().abs()
}

fn total(terms: impl Iterator<Item = Float>) -> Float {
    terms.fold(exact(0.0), |sum, t| add(&sum, &t))
}

/// `(|error| - u |target|?) (1 - ku)^power <= (ku)^power scale`, `u = 2^-53`.
fn gamma_bound(
    error: &Float,
    target: Option<&Float>,
    k: usize,
    squared: bool,
    scale: &Float,
) -> bool {
    let mut excess = magnitude(error);
    if let Some(target) = target {
        excess = sub(&excess, &mul(&magnitude(target), &power(-53)));
    }
    if excess <= 0 {
        return true;
    }
    let ku = mul(&exact(k as f64), &power(-53));
    let rest = sub(&exact(1.0), &ku);
    if squared {
        mul(&excess, &mul(&rest, &rest)) <= mul(&mul(&ku, &ku), scale)
    } else {
        mul(&excess, &rest) <= mul(&ku, scale)
    }
}

/// docs/reduce.md: a NaN result is the first input NaN in index order, `x`
/// before `y`, or the canonical quiet NaN when no input is NaN.
fn check_nan(name: &str, result: f64, x: &[f64], y: &[f64]) {
    let first = (0..x.len().max(y.len()))
        .flat_map(|i| [x.get(i), y.get(i)])
        .flatten()
        .find(|v| v.is_nan());
    match first {
        Some(nan) => assert_eq!(result.to_bits(), nan.to_bits(), "{name} NaN {x:?} {y:?}"),
        None => assert!(
            !result.is_nan() || result.to_bits() == 0x7ff8_0000_0000_0000,
            "{name} created NaN {:016x}",
            result.to_bits()
        ),
    }
}

fn check_max_abs(xs: &[f64]) {
    let actual = reduce::max_abs(xs);
    let expected = match xs.iter().find(|x| x.is_nan()) {
        Some(&nan) => nan,
        None => xs
            .iter()
            .fold(0.0, |m, x| if x.abs() > m { x.abs() } else { m }),
    };
    assert_eq!(actual.to_bits(), expected.to_bits(), "max_abs {xs:?}");
}

fn check_sums(xs: &[f64]) {
    let (plain, compensated) = (reduce::sum(xs), reduce::sum2(xs));
    check_nan("sum", plain, xs, &[]);
    check_nan("sum2", compensated, xs, &[]);
    if xs.is_empty() {
        assert_eq!([plain.to_bits(), compensated.to_bits()], [0, 0]);
        return;
    }
    if !xs.iter().all(|x| x.is_finite()) {
        return;
    }
    let target = total(xs.iter().map(|&x| exact(x)));
    let scale = total(xs.iter().map(|&x| exact(x.abs())));
    let k = xs.len() - 1;
    // An overflowing operation leaves an infinity or NaN that every later step
    // keeps, so a finite result establishes the bound's no-overflow condition.
    if plain.is_finite() {
        assert!(
            gamma_bound(&sub(&exact(plain), &target), None, k, false, &scale),
            "sum bound {xs:?}"
        );
    }
    if compensated.is_finite() {
        assert!(
            gamma_bound(
                &sub(&exact(compensated), &target),
                Some(&target),
                k,
                true,
                &scale
            ),
            "sum2 bound {xs:?}"
        );
    }
}

/// The least `e` with `|x| <= 2^e`; any exponent bounds zero.
fn bounding_exponent(x: f64) -> i32 {
    match exact(x).get_exp() {
        None => -1074,
        // MPFR's exponent satisfies 2^(e-1) <= |x| < 2^e.
        Some(e) if exact(x.abs()) == power(e - 1) => e - 1,
        Some(e) => e,
    }
}

/// `two_prod`'s magnitude limits (docs/double-word.md).
fn product_fits(a: f64, b: f64) -> bool {
    let (ea, eb) = (bounding_exponent(a), bounding_exponent(b));
    ea <= 994 && eb <= 994 && ea + eb <= 1020
}

fn check_dots(xs: &[f64], ys: &[f64]) {
    let (plain, compensated) = (reduce::dot(xs, ys), reduce::dot2(xs, ys));
    check_nan("dot", plain, xs, ys);
    check_nan("dot2", compensated, xs, ys);
    check_nan("sum_squares", reduce::sum_squares(xs), xs, &[]);
    check_nan("sum_squares2", reduce::sum_squares2(xs), xs, &[]);
    if xs.is_empty() {
        assert_eq!([plain.to_bits(), compensated.to_bits()], [0, 0]);
    }
    assert_eq!(
        reduce::sum_squares(xs).to_bits(),
        reduce::dot(xs, xs).to_bits()
    );
    assert_eq!(
        reduce::sum_squares2(xs).to_bits(),
        reduce::dot2(xs, xs).to_bits()
    );
    if xs.is_empty() || !xs.iter().chain(ys).all(|x| x.is_finite()) {
        return;
    }
    for (a, b) in [(xs, ys), (xs, xs)] {
        let products: Vec<Float> = a
            .iter()
            .zip(b)
            .map(|(&x, &y)| mul(&exact(x), &exact(y)))
            .collect();
        let target = total(products.iter().cloned());
        let scale = total(products.iter().map(magnitude));
        let above = |k| {
            products
                .iter()
                .all(|p| p.is_zero() || magnitude(p) >= power(k))
        };
        let n = a.len();
        let plain = reduce::dot(a, b);
        if above(-1022) && plain.is_finite() {
            let error = sub(&exact(plain), &target);
            assert!(
                gamma_bound(&error, None, n, false, &scale),
                "dot bound {a:?} {b:?}"
            );
        }
        // Dot2 also needs every product inside two_prod's domain.
        let compensated = reduce::dot2(a, b);
        let fits = a.iter().zip(b).all(|(&x, &y)| product_fits(x, y));
        if above(-969) && fits && compensated.is_finite() {
            let error = sub(&exact(compensated), &target);
            assert!(
                gamma_bound(&error, Some(&target), n, true, &scale),
                "dot2 bound {a:?} {b:?}"
            );
        }
    }
}

type Readouts = [Result<(u64, u64), MomentsError>; 3];

fn readouts(m: &Moments2) -> Readouts {
    [m.mean(), m.variance(), m.standard_error()]
        .map(|r| r.map(|e: MomentEstimate| (e.value().to_bits(), e.absolute_error().to_bits())))
}

fn check_readouts(m: &Moments2, samples: &[f64]) {
    assert_eq!(m.count(), samples.len() as u64);
    let n = samples.len();
    let count = exact(n as f64);
    let sum = total(samples.iter().map(|&x| exact(x)));
    let squares = total(samples.iter().map(|&x| mul(&exact(x), &exact(x))));
    // n Q - S^2 is the variance numerator over n (n - 1).
    let numerator = sub(&mul(&count, &squares), &mul(&sum, &sum));
    let pairs = mul(&count, &exact(n.saturating_sub(1) as f64));
    let ends = |e: MomentEstimate| {
        assert!(e.value().is_finite() && e.absolute_error().is_finite());
        assert!(e.absolute_error() >= 0.0 && !e.absolute_error().is_sign_negative());
        assert!(
            e.value() != 0.0 || !e.value().is_sign_negative(),
            "negative zero readout"
        );
        (
            sub(&exact(e.value()), &exact(e.absolute_error())),
            add(&exact(e.value()), &exact(e.absolute_error())),
        )
    };
    match m.mean() {
        Ok(e) => {
            let (lo, hi) = ends(e);
            assert!(
                mul(&lo, &count) <= sum && sum <= mul(&hi, &count),
                "mean {samples:?}"
            );
        }
        Err(MomentsError::Empty) => assert_eq!(n, 0),
        Err(_) => assert!(n > 0),
    }
    match m.variance() {
        Ok(e) => {
            let (lo, hi) = ends(e);
            assert!(
                mul(&lo, &pairs) <= numerator && numerator <= mul(&hi, &pairs),
                "variance {samples:?}"
            );
        }
        Err(MomentsError::InsufficientSamples) => assert!(n < 2),
        Err(_) => assert!(n >= 2),
    }
    match m.standard_error() {
        Ok(e) => {
            let (lo, hi) = ends(e);
            // se^2 = numerator / (n^2 (n - 1)).
            let scale = mul(&pairs, &count);
            let square_at_most = lo <= 0 || mul(&mul(&lo, &lo), &scale) <= numerator;
            let square_at_least = hi >= 0 && mul(&mul(&hi, &hi), &scale) >= numerator;
            assert!(
                square_at_most && square_at_least,
                "standard error {samples:?}"
            );
        }
        Err(MomentsError::InsufficientSamples) => assert!(n < 2),
        Err(_) => assert!(n >= 2),
    }
}

fn check_moments(xs: &[f64], split: usize) {
    let split = split % (xs.len() + 1);
    let mut parts = [Moments2::new(), Moments2::new()];
    let mut kept = [Vec::new(), Vec::new()];
    for (i, &x) in xs.iter().enumerate() {
        let part = usize::from(i >= split);
        let before = readouts(&parts[part]);
        match parts[part].push(x) {
            Ok(()) => {
                assert!(x.is_finite());
                kept[part].push(x);
            }
            Err(error) => {
                assert_eq!(error == MomentsError::NonFiniteSample, !x.is_finite());
                assert_eq!(readouts(&parts[part]), before, "failed push changed state");
                assert_eq!(parts[part].count(), kept[part].len() as u64);
            }
        }
    }
    for (part, samples) in parts.iter().zip(&kept) {
        check_readouts(part, samples);
    }
    let [mut left, right] = parts;
    let (before, right_before) = (readouts(&left), readouts(&right));
    match left.merge(&right) {
        Ok(()) => {
            let all: Vec<f64> = kept.concat();
            check_readouts(&left, &all);
        }
        Err(_) => {
            assert_eq!(readouts(&left), before, "failed merge changed the receiver");
            assert_eq!(left.count(), kept[0].len() as u64);
        }
    }
    assert_eq!(readouts(&right), right_before, "merge changed its operand");
}

/// Enclose `x - m` as `ln(1 + sum_{i != j} exp(x_i - m))` for the finite
/// entries, where `j` is the first maximum.
fn log_correction(xs: &[f64], j: usize, p: u32) -> (Float, Float) {
    let (mut lo, mut hi) = (Float::with_val(p, 0), Float::with_val(p, 0));
    for (i, &x) in xs.iter().enumerate() {
        if i == j || x == f64::NEG_INFINITY {
            continue;
        }
        let d = sub(&exact(x), &exact(xs[j]));
        let mut below = Float::with_val_round(p, &d, Round::Down).0;
        let mut above = Float::with_val_round(p, &d, Round::Up).0;
        below.exp_round(Round::Down);
        above.exp_round(Round::Up);
        lo = Float::with_val_round(p, &lo + &below, Round::Down).0;
        hi = Float::with_val_round(p, &hi + &above, Round::Up).0;
    }
    lo.ln_1p_round(Round::Down);
    hi.ln_1p_round(Round::Up);
    (lo, hi)
}

/// `|actual - (m + L)| <= u |m + L| + beta u |L| + eta 2^-1074` for every `L`
/// in the enclosure; `None` when the enclosure is too wide to decide.
fn log_bound(actual: f64, m: f64, l: &(Float, Float), beta: f64, eta: u32) -> Option<bool> {
    let (lo, hi) = (exactly(&l.0 + exact(0.0)), exactly(&l.1 + exact(0.0)));
    // MPFR can enclose a vanishing L with exponents far below binary64's; the
    // eta allowance exceeds any such term, so replace them by their bounds.
    let floor = power(-4000);
    let clamp = |v: Float, up: bool| {
        if v.is_zero() || magnitude(&v) >= floor {
            v
        } else if up == (v > 0) {
            if up { floor.clone() } else { -floor.clone() }
        } else {
            exact(0.0)
        }
    };
    let (lo, hi) = (clamp(lo, false), clamp(hi, true));
    let base = sub(&exact(actual), &exact(m));
    let errors = [sub(&base, &lo), sub(&base, &hi)];
    let widest = errors
        .iter()
        .map(magnitude)
        .fold(exact(0.0), |a, b| a.max(&b));
    let narrowest = if errors[0] >= 0 && errors[1] <= 0 || errors[0] <= 0 && errors[1] >= 0 {
        exact(0.0)
    } else {
        magnitude(&errors[0]).min(&magnitude(&errors[1]))
    };
    let ys = [add(&exact(m), &lo), add(&exact(m), &hi)];
    let ls = [magnitude(&lo), magnitude(&hi)];
    let allowance = |y: Float, l: Float| {
        let relative = add(&y, &mul(&exact(beta), &l));
        add(
            &mul(&relative, &power(-53)),
            &mul(&exact(f64::from(eta)), &power(-1074)),
        )
    };
    let y_small = if (ys[0] <= 0) != (ys[1] <= 0) {
        exact(0.0)
    } else {
        magnitude(&ys[0]).min(&magnitude(&ys[1]))
    };
    let y_large = magnitude(&ys[0]).max(&magnitude(&ys[1]));
    let l_small = ls[0].clone().min(&ls[1]);
    let l_large = ls[0].clone().max(&ls[1]);
    if widest <= allowance(y_small, l_small) {
        Some(true)
    } else if narrowest > allowance(y_large, l_large) {
        Some(false)
    } else {
        None
    }
}

/// `beta = 3 + 2^-8` and `eta = 2k + 1` (docs/log_space.md section 4).
const SUM_BETA: f64 = 3.003_906_25;

fn first_maximum(xs: &[f64]) -> usize {
    (1..xs.len()).fold(0, |j, i| if xs[i] > xs[j] { i } else { j })
}

fn check_log_sum(xs: &[f64]) -> f64 {
    let y = log_space::log_sum_exp(xs);
    if let Some(&nan) = xs.iter().find(|x| x.is_nan()) {
        assert_eq!(y.to_bits(), nan.to_bits(), "log_sum_exp NaN");
        return y;
    }
    if xs.contains(&f64::INFINITY) {
        assert_eq!(y, f64::INFINITY);
        return y;
    }
    let finite: Vec<f64> = xs.iter().copied().filter(|x| x.is_finite()).collect();
    match finite.len() {
        0 => assert_eq!(y, f64::NEG_INFINITY),
        1 => assert_eq!(y.to_bits(), finite[0].to_bits()),
        count => {
            assert!(y.is_finite(), "log_sum_exp overflow {xs:?}");
            let j = first_maximum(&finite);
            let eta = 2 * (count as u32 - 1) + 1;
            let decided = [256, 1024, 4096].iter().find_map(|&p| {
                log_bound(y, finite[j], &log_correction(&finite, j, p), SUM_BETA, eta)
            });
            assert_eq!(decided, Some(true), "log_sum_exp bound {xs:?}");
        }
    }
    y
}

fn check_log_difference(a: f64, b: f64) {
    let y = log_space::log_diff_exp(a, b);
    if a.is_nan() || b.is_nan() {
        let expected = if a.is_nan() { a } else { b };
        assert_eq!(y.to_bits(), expected.to_bits(), "log_diff_exp NaN");
    } else if b > a || a == f64::INFINITY && b == f64::INFINITY {
        assert!(y.is_nan(), "log_diff_exp outside domain {a:e} {b:e}");
    } else if a == b {
        assert_eq!(y, f64::NEG_INFINITY);
    } else if b == f64::NEG_INFINITY || a == f64::INFINITY {
        assert_eq!(y.to_bits(), a.to_bits());
    } else {
        let d = sub(&exact(b), &exact(a));
        let decided = [256, 1024, 4096].iter().find_map(|&p| {
            // -expm1(d) decreases with d.
            let mut lo = Float::with_val_round(p, &d, Round::Up).0;
            let mut hi = Float::with_val_round(p, &d, Round::Down).0;
            lo.exp_m1_round(Round::Up);
            hi.exp_m1_round(Round::Down);
            let (mut lo, mut hi) = (-lo, -hi);
            lo.ln_round(Round::Down);
            hi.ln_round(Round::Up);
            if lo.is_finite() && hi.is_finite() {
                log_bound(y, a, &(lo, hi), 3.89, 5)
            } else {
                None
            }
        });
        // A result below -MAX rounds to -infinity: both terms are then huge.
        if y.is_finite() {
            assert_eq!(decided, Some(true), "log_diff_exp bound {a:e} {b:e}");
        } else {
            assert!(a < -f64::MAX / 2.0 && y == f64::NEG_INFINITY);
        }
    }
}

/// docs/log_space.md fixes the pair record's operations and refusals.
fn check_pairs(xs: &[f64]) {
    let mut pairs = [[f64::NEG_INFINITY; 2]; 4];
    for (pair, values) in pairs.iter_mut().zip(xs.as_chunks::<2>().0.iter()) {
        *pair = [values[0], values[1]];
    }
    let sums = log_space::log_sum_exp_pairs(&pairs);
    let both = log_space::log_sum_exp_and_normalize(&pairs);
    for (i, pair) in pairs.iter().enumerate() {
        let scalar = log_space::log_sum_exp(pair);
        assert_eq!(sums[i].to_bits(), scalar.to_bits(), "pair sum {pair:?}");
        assert_eq!(both[i].0.to_bits(), scalar.to_bits(), "fused sum {pair:?}");
        let hi = usize::from(pair[1] > pair[0]);
        let d = pair[1 - hi] - pair[hi];
        match both[i].1 {
            Ok(p) => {
                assert!(pair.iter().all(|x| !x.is_nan() && *x != f64::INFINITY));
                assert!(pair[hi].is_finite());
                let top = -elementary::ln_1p(elementary::exp(d));
                assert_eq!(p[hi].to_bits(), top.to_bits(), "pair top {pair:?}");
                assert_eq!(
                    p[1 - hi].to_bits(),
                    (d + top).to_bits(),
                    "pair other {pair:?}"
                );
            }
            Err(NormalizeError::InvalidWeight(k)) => {
                let first = pair.iter().position(|x| x.is_nan() || *x == f64::INFINITY);
                assert_eq!(first, Some(k));
            }
            Err(NormalizeError::ZeroMass) => assert_eq!(pair[hi], f64::NEG_INFINITY),
            Err(NormalizeError::Unrepresentable(k)) => {
                assert_eq!(k, 1 - hi);
                assert!(pair[k].is_finite() && d == f64::NEG_INFINITY);
            }
            Err(error) => panic!("unexpected pair refusal {error:?}"),
        }
    }
}

fn check_normalization(xs: &[f64]) {
    const SENTINEL: f64 = 0.125;
    let mut short = vec![SENTINEL; xs.len() + 1];
    assert!(matches!(
        log_space::normalize_log_weights(xs, &mut short),
        Err(NormalizeError::LengthMismatch)
    ));
    assert!(short.iter().all(|&p| p == SENTINEL));
    let mut out = vec![SENTINEL; xs.len()];
    let result = log_space::normalize_log_weights(xs, &mut out);
    let invalid = xs.iter().position(|x| x.is_nan() || *x == f64::INFINITY);
    let finite = xs.iter().filter(|x| x.is_finite()).count();
    let untouched = || {
        assert!(
            out.iter().all(|&p| p == SENTINEL),
            "output written on error"
        )
    };
    match result {
        Err(NormalizeError::InvalidWeight(k)) => {
            untouched();
            assert_eq!(invalid, Some(k));
        }
        Err(NormalizeError::ZeroMass) => {
            untouched();
            assert!(invalid.is_none() && finite == 0);
        }
        Err(NormalizeError::Unrepresentable(k)) => {
            untouched();
            let m = xs[first_maximum(xs)];
            // Only a component near the overflow threshold may be refused.
            assert!(
                sub(&exact(xs[k]), &exact(m))
                    < -mul(&exact(f64::MAX), &sub(&exact(1.0), &power(-40)))
            );
        }
        Err(error) => panic!("unexpected refusal {error:?} for {xs:?}"),
        Ok(record) => {
            assert!(invalid.is_none() && finite > 0);
            let sum = log_space::log_sum_exp(xs);
            assert_eq!(record.log_sum().to_bits(), sum.to_bits());
            let radius = record.max_absolute_error();
            assert!(radius.is_finite() && radius >= 0.0);
            let j = first_maximum(xs);
            for (i, (&x, &p)) in xs.iter().zip(&out).enumerate() {
                if x == f64::NEG_INFINITY {
                    assert_eq!(p, f64::NEG_INFINITY);
                    continue;
                }
                assert!(p.is_finite() && p <= 0.0, "normalized component {i}");
                if finite == 1 {
                    assert_eq!([p.to_bits(), radius.to_bits()], [0, 0]);
                    continue;
                }
                let d = sub(&exact(x), &exact(xs[j]));
                let contained = [256, 1024, 4096].iter().find_map(|&q| {
                    let (lo, hi) = log_correction(xs, j, q);
                    // p_i = d_i - L, and |p - p_i| <= radius at both ends.
                    let residual = sub(&exact(p), &d);
                    let ends = [lo, hi].map(|l| {
                        let l = exactly(&l + exact(0.0));
                        let l = if magnitude(&l) < power(-4000) {
                            exact(0.0)
                        } else {
                            l
                        };
                        magnitude(&add(&residual, &l))
                    });
                    let widest = ends[0].clone().max(&ends[1]);
                    let narrowest = ends[0].clone().min(&ends[1]);
                    if widest <= exact(radius) {
                        Some(true)
                    } else if narrowest > exact(radius) {
                        Some(false)
                    } else {
                        None
                    }
                });
                assert_eq!(contained, Some(true), "normalization radius {i} {xs:?}");
            }
        }
    }
}

/// Byte 0 selects reductions, moments or log space; byte 1 selects how the
/// little-endian words become a slice, so that clustered and cancelling inputs
/// are reachable; byte 2 places the moment split. At most 64 words are used.
fn decode(mode: u8, words: &[f64]) -> Vec<f64> {
    let Some(&base) = words.first() else {
        return Vec::new();
    };
    words
        .iter()
        .enumerate()
        .map(|(i, &w)| match mode % 3 {
            0 => w,
            // A cluster around the first word, in steps of 2^-8.
            1 if i > 0 => base + f64::from(w.to_bits() as i16) / 256.0,
            // Cancelling neighbours: each odd term nearly negates the last.
            2 if i % 2 == 1 => {
                let previous = words[i - 1];
                let (negated, _) = eft::two_sum(-previous, 0.0);
                f64::from_bits(negated.to_bits().wrapping_add(w.to_bits() % 5))
            }
            _ => w,
        })
        .collect()
}

pub fn check_input(data: &[u8]) {
    let [selector, mode, split, data @ ..] = data else {
        return;
    };
    let words: Vec<f64> = data
        .as_chunks::<8>()
        .0
        .iter()
        .take(TERMS)
        .map(|w| f64::from_bits(u64::from_le_bytes(*w)))
        .collect();
    let xs = decode(*mode, &words);
    match selector % 3 {
        0 => {
            check_max_abs(&xs);
            check_sums(&xs);
            let half = xs.len() / 2;
            check_dots(&xs[..half], &xs[half..2 * half]);
        }
        1 => check_moments(&xs, usize::from(*split)),
        _ => {
            check_log_sum(&xs);
            check_normalization(&xs);
            check_pairs(&xs[..xs.len().min(8)]);
            for pair in xs.as_chunks::<2>().0.iter().take(8) {
                check_log_difference(pair[0], pair[1]);
                check_log_difference(pair[1], pair[0]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet(selector: u8, mode: u8, split: u8, xs: &[f64]) -> Vec<u8> {
        let mut data = vec![selector, mode, split];
        data.extend(xs.iter().flat_map(|x| x.to_bits().to_le_bytes()));
        data
    }

    #[test]
    fn boundary_and_cancelling_slices_satisfy_their_contracts() {
        let tiny = f64::from_bits(1);
        let slices: [&[f64]; 14] = [
            &[],
            &[-0.0],
            &[0.0, -0.0, 0.0],
            &[1.0, f64::EPSILON, -1.0, -1.0],
            &[1e16, 1e16 + 2.0, 1e16 + 4.0],
            &[1e300, -1e300, 1e-300, 3.0],
            &[tiny, tiny, -tiny, 0.5],
            &[-800.0, -800.0, -801.5],
            &[0.0, -std::f64::consts::LN_2, -745.0, -746.0, -1000.0],
            &[f64::MAX, -f64::MAX, f64::MAX],
            &[-f64::MAX, -f64::MAX],
            &[f64::NEG_INFINITY, f64::NEG_INFINITY],
            &[f64::INFINITY, f64::NAN, 1.0],
            &[1.0e-12, 0.0, -1.0e-12, 700.0, 709.0, 1.0e305],
        ];
        for xs in slices {
            for selector in 0..3 {
                for mode in 0..3 {
                    for split in [0, 1, 3] {
                        check_input(&packet(selector, mode, split, xs));
                    }
                }
            }
        }
    }

    #[test]
    fn nan_results_follow_the_rule() {
        check_input(include_bytes!(
            "../regressions/reductions/nan-payload-order"
        ));
        let a = f64::from_bits(0xffff_0101_0292_4925);
        let b = f64::from_bits(0xffff_7fef_ffff_ffff);
        check_nan("planted", a, &[a, b], &[]);
        for (wrong, x) in [
            (b, vec![a, b]),
            (f64::from_bits(0xfff8_0000_0000_0000), vec![f64::INFINITY]),
        ] {
            assert!(std::panic::catch_unwind(|| check_nan("planted", wrong, &x, &[])).is_err());
        }
    }

    #[test]
    fn slices_near_the_overflow_threshold_satisfy_their_bounds() {
        let big = f64::from_bits(0x7fe0_0000_0000_0000); // 2^1023
        let limit = f64::from_bits(0x7e10_0000_0000_0000); // 2^994
        let slices: [&[f64]; 6] = [
            &[big, -big, big, -1.0],
            &[f64::MAX, -f64::MAX, 3.0],
            &[big, big.next_down(), -big, -big.next_down(), 1.0e290],
            &[limit, 2.0_f64, -limit, 2.0, 1.5, limit.next_down()],
            &[1.0e154, -1.0e154, 1.0e153, 7.0],
            &[f64::MAX, f64::MAX],
        ];
        for xs in slices {
            for mode in 0..3 {
                check_input(&packet(0, mode, 0, xs));
            }
        }
        assert!(product_fits(limit, 2.0) && !product_fits(limit.next_up(), 2.0));
    }

    #[test]
    fn long_clustered_slices_reach_lane_remainders() {
        for count in [1_usize, 7, 31, 32, 33, 63, 64, 128, 129] {
            let xs: Vec<f64> = (0..count)
                .map(|i| f64::from_bits(0xc059_0000_0000_0000 + i as u64 * 977))
                .collect();
            for selector in 0..3 {
                for mode in 0..3 {
                    check_input(&packet(selector, mode, count as u8 / 2, &xs));
                }
            }
        }
    }

    #[test]
    fn the_bound_comparisons_reject_planted_errors() {
        let one = exact(1.0);
        assert!(gamma_bound(&exact(0.0), None, 3, false, &one));
        assert!(!gamma_bound(&power(-50), None, 3, false, &one));
        assert!(!gamma_bound(&power(-52), Some(&one), 3, true, &one));
        let xs = [-1.0, -2.0, -3.0];
        let l = log_correction(&xs, 0, 256);
        let y = log_space::log_sum_exp(&xs);
        assert_eq!(log_bound(y, -1.0, &l, SUM_BETA, 5), Some(true));
        let off = f64::from_bits(y.to_bits() + 16);
        assert_eq!(log_bound(off, -1.0, &l, SUM_BETA, 5), Some(false));
    }
}
