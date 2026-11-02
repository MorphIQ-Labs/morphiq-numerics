//! Unpublished MPFR oracle for the strong elementary API.
//!
//! MPFR is used only through its public API; no oracle implementation is copied.
use morphiq_numerics::elementary as e;
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
}

impl Operation {
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
        }
    }

    fn reference(self, x: f64, y: f64, precision: u32, round: Round) -> Float {
        // Every binary64 input is represented exactly, including subnormals.
        let mut value = Float::with_val(precision, x);
        match self {
            Self::Exp => value.exp_round(round),
            Self::Exp2 => value.exp2_round(round),
            Self::Expm1 => value.exp_m1_round(round),
            Self::Ln => value.ln_round(round),
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

    /// None means exact rounding; Some(k) means (1/2 + 2^-k) ulp.
    /// Domain constants here describe the published mathematics, independently
    /// of the implementation's branch decisions. See the contract table.
    fn bound(self, x: f64, y: f64) -> Option<u32> {
        let a = x.abs();
        match self {
            Self::Expm1 if a >= f64::from_bits(0x3c90_0000_0000_0000) => Some(65),
            Self::Ln1p if a >= f64::from_bits(0x3c90_0000_0000_0000) => Some(70),
            Self::Log10 => Some(69),
            Self::Sin
                if !(a <= f64::from_bits(0x3e57_1374_4912_3ef6)
                    || (f64::from_bits(0x3e70_0000_0000_0000)..=2.0 + 4675.0 / 8192.0)
                        .contains(&a)) =>
            {
                Some(144)
            }
            Self::Cos if a > 12867.0 / 8192.0 => Some(144),
            Self::Tan => {
                // atan(2) rounded DOWN to binary64, derived by MPFR in tests.
                let end = f64::from_bits(0x3ff1_b6e1_92eb_be44);
                if a <= f64::from_bits(0x3e4d_12ed_0af1_a27e)
                    || (f64::from_bits(0x3e60_0000_0000_0000)..=end).contains(&a)
                {
                    None
                } else {
                    Some(142)
                }
            }
            Self::Atan2 if x.is_finite() && y.is_finite() && x != 0.0 && y != 0.0 => {
                // Tiny ratios are correctly rounded in every quadrant. Compare
                // exact dyadics rather than underflowing a binary64 quotient.
                let small = Float::with_val(128, a.min(y.abs())) << 900;
                if small < Float::with_val(128, a.max(y.abs())) {
                    None
                } else {
                    Some(137)
                }
            }
            _ => None,
        }
    }
}

fn same_bits(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits()
}

/// Classify an interval against a bound. Indeterminate means refine the oracle,
/// never accept an unestablished result. All error arithmetic rounds outwards.
fn within_bound(value: f64, lo: &Float, hi: &Float, k: u32) -> Option<bool> {
    let precision = lo.prec();
    let lo_exp = lo.get_exp()?;
    let hi_exp = hi.get_exp()?;
    if lo_exp != hi_exp {
        return None;
    }
    let ulp_exp = (lo_exp - 53).max(-1074);
    let mut limit = Float::with_val(precision, 1) >> k;
    limit += 0.5;
    limit <<= ulp_exp;
    let actual = Float::with_val(precision, value);
    let (left, _) = Float::with_val_round(precision, &actual - lo, Round::Up);
    let (right, _) = Float::with_val_round(precision, hi - &actual, Round::Up);
    if left <= limit && right <= limit {
        return Some(true);
    }
    let (left, _) = Float::with_val_round(precision, &actual - hi, Round::Down);
    let (right, _) = Float::with_val_round(precision, lo - &actual, Round::Down);
    if left > limit || right > limit {
        Some(false)
    } else {
        None
    }
}

/// Verify one result against an independently rounded MPFR enclosure.
pub fn check_result(op: Operation, x: f64, y: f64, actual: f64) {
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
        if same_bits(actual, lower) {
            return;
        }
        if let Some(k) = bound
            && actual.is_finite()
            && lower.is_finite()
            && actual != 0.0
            && lower != 0.0
        {
            match within_bound(actual, &lo, &hi, k) {
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
    let mut xs = [0.0; 16];
    let mut ys = [0.0; 16];
    let mut expected = [0.0; 16];
    let count = data.len().min(256) / 16;
    for (i, pair) in data.chunks_exact(16).take(16).enumerate() {
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
    let mut out = [0.0; 16];
    let out = &mut out[..count];
    match op {
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
    fn bound_keeps_the_term_beyond_half_an_ulp() {
        // A non-CR result can satisfy the stated bound; do not silently demand
        // CR or round (1/2 + 2^-k) to 1/2 in binary64 arithmetic.
        let mut exact = Float::with_val(256, 1);
        exact += Float::with_val(256, 1) >> 53;
        exact += Float::with_val(256, 1) >> 198;
        assert_eq!(within_bound(1.0, &exact, &exact, 144), Some(true));
        exact += Float::with_val(256, 1) >> 195;
        assert_eq!(within_bound(1.0, &exact, &exact, 144), Some(false));
    }
}
