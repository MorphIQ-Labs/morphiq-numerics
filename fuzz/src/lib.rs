//! Unpublished MPFR oracle for the strong and fast elementary APIs.
//!
//! MPFR is used only through its public API; no oracle implementation is copied.
use morphiq_numerics::{elementary as e, fast::elementary as fast};
use rug::{Float, float::Round};

/// Stable operation IDs in the corpus format (see README.md).
#[derive(Clone, Copy, Debug)]
pub enum Operation {
    Exp,
    Exp2,
    Expm1,
    Ln,
    Ln1p,
    Log2,
    Log10,
    Sin,
    Cos,
    Tan,
    Sqrt,
    Asin,
    Asinh,
    Atan2,
    FastExp,
    FastExpCoarse,
    FastLn,
}

#[derive(Clone, Copy, Debug)]
enum Bound {
    Ulps(u32),
    Relative(u32),
    LogAbsolute,
}

impl Operation {
    const FAST: [Self; 3] = [Self::FastExp, Self::FastExpCoarse, Self::FastLn];
    pub const ALL: [Self; 14] = [
        Self::Exp,
        Self::Exp2,
        Self::Expm1,
        Self::Ln,
        Self::Ln1p,
        Self::Log2,
        Self::Log10,
        Self::Sin,
        Self::Cos,
        Self::Tan,
        Self::Sqrt,
        Self::Asin,
        Self::Asinh,
        Self::Atan2,
    ];

    fn evaluate(self, x: f64, y: f64) -> f64 {
        match self {
            Self::Exp => e::exp(x),
            Self::Exp2 => e::exp2(x),
            Self::Expm1 => e::expm1(x),
            Self::Ln => e::ln(x),
            Self::Ln1p => e::ln_1p(x),
            Self::Log2 => e::log2(x),
            Self::Log10 => e::log10(x),
            Self::Sin => e::sin(x),
            Self::Cos => e::cos(x),
            Self::Tan => e::tan(x),
            Self::Sqrt => e::sqrt(x),
            Self::Asin => e::asin(x),
            Self::Asinh => e::asinh(x),
            Self::Atan2 => e::atan2(x, y),
            Self::FastExp => fast::exp(x),
            Self::FastExpCoarse => fast::exp_coarse(x),
            Self::FastLn => fast::ln(x),
        }
    }

    fn reference(self, x: f64, y: f64, precision: u32, round: Round) -> Float {
        // Every binary64 input is represented exactly, including subnormals.
        let mut value = Float::with_val(precision, x);
        match self {
            Self::Exp | Self::FastExp | Self::FastExpCoarse => value.exp_round(round),
            Self::Exp2 => value.exp2_round(round),
            Self::Expm1 => value.exp_m1_round(round),
            Self::Ln | Self::FastLn => value.ln_round(round),
            Self::Ln1p => value.ln_1p_round(round),
            Self::Log2 => value.log2_round(round),
            Self::Log10 => value.log10_round(round),
            Self::Sin => value.sin_round(round),
            Self::Cos => value.cos_round(round),
            Self::Tan => value.tan_round(round),
            Self::Sqrt => value.sqrt_round(round),
            Self::Asin => value.asin_round(round),
            Self::Asinh => value.asinh_round(round),
            Self::Atan2 => value.atan2_round(&Float::with_val(precision, y), round),
        };
        value
    }

    /// None means exact rounding; the other cases specify the public error metric.
    /// Domain constants here describe the published mathematics, independently
    /// of the implementation's branch decisions. See the contract table.
    fn bound(self, x: f64, y: f64) -> Option<Bound> {
        let a = x.abs();
        match self {
            Self::FastExp if a < 704.0 => Some(Bound::Relative(51)),
            Self::FastExpCoarse if a < 704.0 => Some(Bound::Relative(38)),
            Self::FastLn if x.is_finite() && x > 0.0 && x != 1.0 => Some(Bound::LogAbsolute),
            Self::Expm1 if a >= f64::from_bits(0x3c90_0000_0000_0000) => Some(Bound::Ulps(65)),
            Self::Ln1p if a >= f64::from_bits(0x3c90_0000_0000_0000) => Some(Bound::Ulps(70)),
            Self::Log10 => Some(Bound::Ulps(69)),
            Self::Sin
                if !(a <= f64::from_bits(0x3e57_1374_4912_3ef6)
                    || (f64::from_bits(0x3e70_0000_0000_0000)..=2.0 + 4675.0 / 8192.0)
                        .contains(&a)) =>
            {
                Some(Bound::Ulps(144))
            }
            Self::Cos if a > 12867.0 / 8192.0 => Some(Bound::Ulps(144)),
            Self::Tan => {
                // atan(2) rounded DOWN to binary64, derived by MPFR in tests.
                let end = f64::from_bits(0x3ff1_b6e1_92eb_be44);
                if a <= f64::from_bits(0x3e4d_12ed_0af1_a27e)
                    || (f64::from_bits(0x3e60_0000_0000_0000)..=end).contains(&a)
                {
                    None
                } else {
                    Some(Bound::Ulps(142))
                }
            }
            Self::Atan2 if x.is_finite() && y.is_finite() && x != 0.0 && y != 0.0 => {
                // Tiny ratios are correctly rounded in every quadrant. Compare
                // exact dyadics rather than underflowing a binary64 quotient.
                let small = Float::with_val(128, a.min(y.abs())) << 900;
                if small < Float::with_val(128, a.max(y.abs())) {
                    None
                } else {
                    Some(Bound::Ulps(137))
                }
            }
            _ => None,
        }
    }
}

fn same_bits(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits()
}

/// Enclose the allowed absolute error as a function of the exact result.
/// Both magnitude and addition round outwards; the ln floor is never computed
/// in binary64 or replaced with a relative/ULP approximation.
fn limits(lo: &Float, hi: &Float, bound: Bound) -> Option<(Float, Float)> {
    let precision = lo.prec();
    match bound {
        Bound::Ulps(k) => {
            let lo_exp = lo.get_exp()?;
            if lo_exp != hi.get_exp()? {
                return None;
            }
            let mut limit = Float::with_val(precision, 1) >> k;
            limit += 0.5;
            limit <<= (lo_exp - 53).max(-1074);
            Some((limit.clone(), limit))
        }
        Bound::Relative(_) | Bound::LogAbsolute => {
            let a = lo.clone().abs();
            let b = hi.clone().abs();
            let (mut small, mut large) = if a <= b { (a, b) } else { (b, a) };
            if lo <= &0 && hi >= &0 {
                small = Float::with_val(precision, 0);
            }
            let shift = match bound {
                Bound::Relative(k) => k,
                _ => 53,
            };
            small >>= shift;
            large >>= shift;
            if matches!(bound, Bound::LogAbsolute) {
                let floor = Float::with_val(precision, 1) >> 65;
                small = Float::with_val_round(precision, &small + &floor, Round::Down).0;
                large = Float::with_val_round(precision, &large + &floor, Round::Up).0;
            }
            Some((small, large))
        }
    }
}

/// Indeterminate means refine the oracle, never accept an unestablished result.
fn within_bound(value: f64, lo: &Float, hi: &Float, bound: Bound) -> Option<bool> {
    let precision = lo.prec();
    let (limit_lo, limit_hi) = limits(lo, hi, bound)?;
    let actual = Float::with_val(precision, value);
    let (left, _) = Float::with_val_round(precision, &actual - lo, Round::Up);
    let (right, _) = Float::with_val_round(precision, hi - &actual, Round::Up);
    if left <= limit_lo && right <= limit_lo {
        return Some(true);
    }
    let (left, _) = Float::with_val_round(precision, &actual - hi, Round::Down);
    let (right, _) = Float::with_val_round(precision, lo - &actual, Round::Down);
    if left > limit_hi || right > limit_hi {
        Some(false)
    } else {
        None
    }
}

/// Verify one result against an independently rounded MPFR enclosure.
pub fn check_result(op: Operation, x: f64, y: f64, actual: f64) {
    // These API relationships include NaN payloads and exact identities. The
    // independent MPFR check below additionally validates the numerical result.
    let owner = match op {
        Operation::FastExp | Operation::FastExpCoarse if x.abs() >= 704.0 || x.is_nan() => {
            Some(e::exp(x))
        }
        Operation::FastExp | Operation::FastExpCoarse if x == 0.0 => Some(1.0),
        Operation::FastLn if !(x.is_finite() && x > 0.0) => Some(e::ln(x)),
        Operation::FastLn if x == 1.0 => Some(0.0),
        _ => None,
    };
    if let Some(expected) = owner {
        assert_eq!(
            actual.to_bits(),
            expected.to_bits(),
            "{op:?} fallback/identity for {:016x}",
            x.to_bits()
        );
    }
    let bound = op.bound(x, y);
    for precision in [256, 512, 1024, 2048, 4096, 8192] {
        let lo = op.reference(x, y, precision, Round::Down);
        let hi = op.reference(x, y, precision, Round::Up);
        if lo.is_nan() && hi.is_nan() {
            // The numerical contract says NaN, not an MPFR-specific payload.
            // Slice equivalence below still compares the library's exact bits.
            assert!(actual.is_nan(), "{op:?}: expected NaN");
            return;
        }
        let lower = lo.to_f64_round(Round::Nearest);
        let upper = hi.to_f64_round(Round::Nearest);
        if !same_bits(lower, upper) {
            continue;
        }
        if same_bits(actual, lower)
            && !matches!(bound, Some(Bound::Relative(_) | Bound::LogAbsolute))
        {
            return;
        }
        if let Some(bound) = bound
            && actual.is_finite()
            && lower.is_finite()
            && actual != 0.0
            && lower != 0.0
        {
            match within_bound(actual, &lo, &hi, bound) {
                Some(true) => return,
                None => continue,
                Some(false) => (),
            }
        }
        panic!(
            "{op:?} contract violation: x={:016x}, y={:016x}, got={:016x}, RN={:016x}, bound={bound:?}, precision={precision}",
            x.to_bits(),
            y.to_bits(),
            actual.to_bits(),
            lower.to_bits()
        );
    }
    panic!(
        "MPFR oracle unresolved at 8192 bits: {op:?}, x={:016x}, y={:016x}",
        x.to_bits(),
        y.to_bits()
    );
}

/// A selector byte followed by up to sixteen little-endian (x, y) bit pairs.
/// Unary functions ignore y; Atan2 interprets each pair as atan2(x, y).
/// Partial trailing pairs are ignored. Even empty slices exercise the wrapper.
pub fn check_input(data: &[u8]) {
    let Some((&selector, data)) = data.split_first() else {
        return;
    };
    let op = Operation::ALL[usize::from(selector) % Operation::ALL.len()];
    check_cases::<16>(op, data);
}

/// Fast-target selectors have their own namespace, preserving every existing
/// strong corpus byte (including mutated selector bytes above 13).
pub fn check_fast_input(data: &[u8]) {
    let Some((&selector, data)) = data.split_first() else {
        return;
    };
    let op = Operation::FAST[usize::from(selector) % Operation::FAST.len()];
    check_cases::<65>(op, data);
}

fn check_cases<const N: usize>(op: Operation, data: &[u8]) {
    let mut xs = [0.0; N];
    let mut ys = [0.0; N];
    let mut expected = [0.0; N];
    let count = data.len().min(16 * N) / 16;
    for (i, pair) in data.chunks_exact(16).take(N).enumerate() {
        xs[i] = f64::from_bits(u64::from_le_bytes(pair[..8].try_into().unwrap()));
        ys[i] = f64::from_bits(u64::from_le_bytes(pair[8..].try_into().unwrap()));
        expected[i] = op.evaluate(xs[i], ys[i]);
        check_result(op, xs[i], ys[i], expected[i]);
        if matches!(op, Operation::Sin | Operation::Cos) {
            let (s, c) = e::sincos(xs[i]);
            assert_eq!(s.to_bits(), e::sin(xs[i]).to_bits(), "sincos/sin");
            assert_eq!(c.to_bits(), e::cos(xs[i]).to_bits(), "sincos/cos");
        }
    }
    let xs = &xs[..count];
    let ys = &ys[..count];
    let mut out = [0.0; N];
    let out = &mut out[..count];
    match op {
        Operation::FastExp => fast::exp_slice(xs, out),
        Operation::FastExpCoarse => fast::exp_coarse_slice(xs, out),
        Operation::FastLn => fast::ln_slice(xs, out),
        Operation::Exp => e::exp_slice(xs, out),
        Operation::Exp2 => e::exp2_slice(xs, out),
        Operation::Expm1 => e::expm1_slice(xs, out),
        Operation::Ln => e::ln_slice(xs, out),
        Operation::Ln1p => e::ln_1p_slice(xs, out),
        Operation::Asin => e::asin_slice(xs, out),
        Operation::Asinh => e::asinh_slice(xs, out),
        Operation::Atan2 => e::atan2_slice(xs, ys, out),
        _ => return,
    }
    for (i, (&a, &b)) in out.iter().zip(expected.iter()).enumerate() {
        assert_eq!(a.to_bits(), b.to_bits(), "{op:?} slice lane {i}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tan_cr_endpoint_is_the_downward_rounding_of_atan_two() {
        for round in [Round::Down, Round::Up] {
            let mut end = Float::with_val(256, 2);
            end.atan_round(round);
            assert_eq!(
                end.to_f64_round(Round::Down).to_bits(),
                0x3ff1_b6e1_92eb_be44
            );
        }
    }

    #[test]
    fn exact_results_signed_zeros_and_subnormal_ties() {
        for (op, x, y, expected) in [
            (Operation::Exp2, -1075.0, 0.0, 0.0),
            (Operation::Exp2, -1074.0, 0.0, f64::from_bits(1)),
            (Operation::Sqrt, -0.0, 0.0, -0.0),
            (Operation::Ln, 1.0, 0.0, 0.0),
            (Operation::Atan2, f64::from_bits(3), 2.0, f64::from_bits(1)),
            (Operation::Atan2, -0.0, 1.0, -0.0),
        ] {
            check_result(op, x, y, expected);
        }
    }

    #[test]
    fn nan_payloads_are_not_part_of_the_mpfr_numeric_contract() {
        for bits in [
            0x7ff8_0000_0000_0000,
            0xfff8_0000_0000_1234,
            0x7ff0_0000_0000_0001,
        ] {
            check_result(Operation::Ln, -1.0, 0.0, f64::from_bits(bits));
        }
    }

    #[test]
    fn oracle_rejects_wrong_rounding_sign_nan_and_bound() {
        for (op, x, y, bad) in [
            (Operation::Sqrt, 4.0, 0.0, 2.0_f64.next_up()),
            (Operation::Sin, -0.0, 0.0, 0.0),
            (Operation::Ln, -1.0, 0.0, 0.0),
            (Operation::Log10, 10.0, 0.0, 1.0_f64.next_up()),
            (Operation::Expm1, 1.0, 0.0, 2.0),
        ] {
            assert!(std::panic::catch_unwind(|| check_result(op, x, y, bad)).is_err());
        }
    }

    #[test]
    fn fast_bounds_accept_their_allowance_and_reject_excess_error() {
        let exact = Float::with_val(256, 1);
        for k in [51, 38] {
            let allowance = f64::from_bits(u64::from(1023 - k) << 52);
            let edge = 1.0 + allowance;
            assert_eq!(
                within_bound(edge, &exact, &exact, Bound::Relative(k)),
                Some(true)
            );
            assert_eq!(
                within_bound(edge.next_up(), &exact, &exact, Bound::Relative(k)),
                Some(false)
            );
            let neg = -exact.clone();
            assert_eq!(
                within_bound(-edge, &neg, &neg, Bound::Relative(k)),
                Some(true)
            );
        }
        let floor = f64::from_bits((1023 - 65) << 52);
        let zero = Float::with_val(256, 0);
        assert_eq!(
            within_bound(floor, &zero, &zero, Bound::LogAbsolute),
            Some(true)
        );
        assert_eq!(
            within_bound(floor.next_up(), &zero, &zero, Bound::LogAbsolute),
            Some(false)
        );
        // At a large magnitude both terms remain present, with the exact sign
        // removed before computing the relative part of the absolute budget.
        let magnitude: Float = Float::with_val(256, 1) << 100;
        let expected = (Float::with_val(256, 1) << 47) + Float::with_val(256, floor);
        for value in [magnitude.clone(), -magnitude] {
            let (lo, hi) = limits(&value, &value, Bound::LogAbsolute).unwrap();
            assert_eq!(lo, expected);
            assert_eq!(hi, expected);
        }
    }

    #[test]
    fn uncertain_relative_bound_requires_refinement() {
        let lo = Float::with_val(256, 1);
        let hi = Float::with_val(256, 1.0_f64.next_up());
        let candidate = f64::from_bits(1.0_f64.to_bits() + 3);
        assert_eq!(within_bound(candidate, &lo, &hi, Bound::Relative(51)), None);
    }

    #[test]
    fn fast_exp_accepts_non_cr_results_only_under_its_selected_budget() {
        for op in [Operation::FastExp, Operation::FastExpCoarse] {
            for x in [1.0, 704.0_f64.next_down(), (-704.0_f64).next_up()] {
                check_result(op, x, 0.0, e::exp(x).next_up());
            }
        }
        let coarse_only = f64::from_bits(e::exp(1.0).to_bits() + 8);
        check_result(Operation::FastExpCoarse, 1.0, 0.0, coarse_only);
        assert!(
            std::panic::catch_unwind(|| check_result(Operation::FastExp, 1.0, 0.0, coarse_only))
                .is_err()
        );
        let excessive = e::exp(1.0) + 1e-10;
        assert!(
            std::panic::catch_unwind(|| check_result(
                Operation::FastExpCoarse,
                1.0,
                0.0,
                excessive
            ))
            .is_err()
        );
    }

    #[test]
    fn fast_log_absolute_floor_is_valid_near_one_but_one_is_exact() {
        let x = 1.0_f64.next_up();
        let rounded = Operation::Ln
            .reference(x, 0.0, 256, Round::Nearest)
            .to_f64();
        let within_floor = rounded + f64::from_bits((1023 - 66) << 52);
        check_result(Operation::FastLn, x, 0.0, within_floor);
        let outside_floor = rounded + f64::from_bits((1023 - 64) << 52);
        assert!(
            std::panic::catch_unwind(|| check_result(Operation::FastLn, x, 0.0, outside_floor))
                .is_err()
        );
        for bad in [-0.0, f64::from_bits(1)] {
            assert!(
                std::panic::catch_unwind(|| check_result(Operation::FastLn, 1.0, 0.0, bad))
                    .is_err()
            );
        }
    }

    #[test]
    fn fast_fallbacks_require_owner_bits_including_nan_payloads() {
        for op in [Operation::FastExp, Operation::FastExpCoarse] {
            for x in [704.0, -704.0, 704.0_f64.next_up(), (-704.0_f64).next_down()] {
                let expected = e::exp(x);
                check_result(op, x, 0.0, expected);
                assert!(
                    std::panic::catch_unwind(|| check_result(op, x, 0.0, expected.next_up()))
                        .is_err()
                );
            }
        }
        for op in Operation::FAST {
            let x = f64::from_bits(0xfff8_0000_0000_1234);
            check_result(op, x, 0.0, op.evaluate(x, 0.0));
            assert!(std::panic::catch_unwind(|| check_result(op, x, 0.0, f64::NAN)).is_err());
        }
    }

    #[test]
    fn bound_keeps_the_term_beyond_half_an_ulp() {
        // A non-CR result can satisfy the stated bound; do not silently demand
        // CR or round (1/2 + 2^-k) to 1/2 in binary64 arithmetic.
        let mut exact = Float::with_val(256, 1);
        exact += Float::with_val(256, 1) >> 53;
        exact += Float::with_val(256, 1) >> 198;
        assert_eq!(
            within_bound(1.0, &exact, &exact, Bound::Ulps(144)),
            Some(true)
        );
        exact += Float::with_val(256, 1) >> 195;
        assert_eq!(
            within_bound(1.0, &exact, &exact, Bound::Ulps(144)),
            Some(false)
        );
    }
}
