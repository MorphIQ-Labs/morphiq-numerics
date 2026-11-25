//! Full-domain independent checks of the published strong normal contracts.
use super::{Bound, normal_reference, within_bound};
use morphiq_numerics::normal;
use rug::{Float, float::Round};

#[derive(Clone, Copy, Debug)]
enum Operation {
    Erfcx,
    Cdf,
    LogCdf,
}

impl Operation {
    const ALL: [Self; 3] = [Self::Erfcx, Self::Cdf, Self::LogCdf];

    fn evaluate(self, x: f64) -> f64 {
        match self {
            Self::Erfcx => normal::erfcx(x),
            Self::Cdf => normal::norm_cdf(x),
            Self::LogCdf => normal::log_norm_cdf(x),
        }
    }

    fn slice(self, xs: &[f64], out: &mut [f64]) {
        match self {
            Self::Erfcx => normal::erfcx_slice(xs, out),
            Self::Cdf => normal::norm_cdf_slice(xs, out),
            Self::LogCdf => normal::log_norm_cdf_slice(xs, out),
        }
    }

    fn bound(self, x: f64) -> Bound {
        let (relative_extra, absolute_extra) = match self {
            Self::Erfcx if x < -0.5 => (Some(122), None),
            Self::Erfcx if x < 16.0 => (None, Some(123)),
            Self::Erfcx => (Some(223), None),
            Self::Cdf if x.abs() <= 0.5 => (Some(245), None),
            Self::Cdf if x < 0.0 => (Some(114), None),
            Self::LogCdf if x.abs() <= 0.5 => (Some(228), None),
            Self::Cdf | Self::LogCdf => (Some(111), None),
        };
        Bound::Normal {
            relative_extra,
            absolute_extra,
        }
    }

    fn enclosure(self, x: f64, p: u32) -> (Float, Float) {
        assert!(p >= 256);
        match self {
            Self::Erfcx => normal_reference::erfcx(&Float::with_val(p, x)),
            Self::Cdf => normal_reference::cdf(x, p),
            Self::LogCdf => normal_reference::log_cdf(x, p),
        }
    }

    /// Exact special values and conservative far screens derived from the
    /// mathematics, not the implementation's threshold encodings.
    fn special(self, x: f64) -> Option<f64> {
        if x.is_nan() {
            return Some(x); // Public contract preserves the entire encoding.
        }
        match self {
            Self::Erfcx if x == f64::INFINITY => Some(0.0),
            // For a>=32, erfcx(-a) > exp(a²) >= exp(1024) > 2^1024.
            Self::Erfcx if x <= -32.0 => Some(f64::INFINITY),
            Self::Erfcx if x == 0.0 => Some(1.0),
            // Mills' bound q=Phi(-a) < exp(-a²/2)/(a sqrt(2pi))
            // gives q<2^-1100 at a>=40. Also -ln(1-q)<2q there.
            Self::Cdf if x <= -40.0 => Some(0.0),
            Self::Cdf if x >= 40.0 => Some(1.0),
            Self::Cdf if x == 0.0 => Some(0.5),
            Self::LogCdf if x >= 40.0 => Some(-0.0),
            Self::LogCdf if x == f64::NEG_INFINITY => Some(f64::NEG_INFINITY),
            _ => None,
        }
    }

    fn check(self, x: f64, actual: f64) {
        if let Some(expected) = self.special(x) {
            assert_eq!(
                actual.to_bits(),
                expected.to_bits(),
                "{self:?}: x={:016x}",
                x.to_bits()
            );
            return;
        }
        // Signs/ranges and erfcx's strictly positive finite-domain result are
        // separate commitments; the additive underflow allowance cannot waive them.
        assert!(!actual.is_nan(), "{self:?}: unexpected NaN");
        match self {
            Self::Erfcx => assert!(actual > 0.0 && !actual.is_sign_negative()),
            Self::Cdf => assert!((0.0..=1.0).contains(&actual) && !actual.is_sign_negative()),
            Self::LogCdf => assert!(actual <= 0.0 && actual.is_sign_negative()),
        }
        let bound = self.bound(x);
        for p in [256, 512, 1024, 2048, 4096, 8192] {
            let (lo, hi) = self.enclosure(x, p);
            assert!(
                lo.is_finite() && hi.is_finite() && lo <= hi,
                "invalid oracle enclosure"
            );
            let lower = lo.to_f64_round(Round::Nearest);
            let upper = hi.to_f64_round(Round::Nearest);
            if lower.to_bits() != upper.to_bits() {
                continue;
            }
            // Saturation/overflow and log-CDF at zero have separate rounding
            // contracts. Interior results use their actual published bounds.
            let exact_rounding = lower.is_infinite()
                || lower == 0.0
                || matches!(self, Self::Cdf) && lower == 1.0
                || matches!(self, Self::LogCdf) && x == 0.0;
            if exact_rounding {
                assert_eq!(
                    actual.to_bits(),
                    lower.to_bits(),
                    "{self:?}: x={:016x}",
                    x.to_bits()
                );
                return;
            }
            assert!(
                actual.is_finite(),
                "{self:?}: premature overflow at {:016x}",
                x.to_bits()
            );
            match within_bound(actual, &lo, &hi, bound) {
                Some(true) => return,
                None => (),
                Some(false) => panic!(
                    "{self:?} contract violation: x={:016x}, got={:016x}, bound={bound:?}, precision={p}",
                    x.to_bits(),
                    actual.to_bits()
                ),
            }
        }
        panic!(
            "normal oracle unresolved at 8192 bits: {self:?}, x={:016x}",
            x.to_bits()
        );
    }
}

/// Independent selector namespace, modulo three: erfcx, CDF and log-CDF.
/// Up to 65 little-endian (x, unused) pairs; incomplete pairs are ignored.
pub fn check_input(data: &[u8]) {
    let Some((&selector, data)) = data.split_first() else {
        return;
    };
    let op = Operation::ALL[usize::from(selector) % Operation::ALL.len()];
    let count = data.len().min(65 * 16) / 16;
    let (mut xs, mut expected, mut out) = ([0.0; 65], [0.0; 65], [0.0; 65]);
    for (i, pair) in data.as_chunks::<16>().0.iter().take(65).enumerate() {
        xs[i] = f64::from_bits(u64::from_le_bytes(pair[..8].try_into().unwrap()));
        expected[i] = op.evaluate(xs[i]);
        op.check(xs[i], expected[i]);
    }
    op.slice(&xs[..count], &mut out[..count]);
    for i in 0..count {
        assert_eq!(
            out[i].to_bits(),
            expected[i].to_bits(),
            "{op:?} slice lane {i}"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_domain_boundaries_and_tail_witnesses() {
        check_input(include_bytes!(
            "../regressions/strong_normal/tail-boundaries"
        ));
        // Documented screens plus oracle formula boundaries; no output values
        // are imported from fixtures or from the implementation under test.
        for op in Operation::ALL {
            for bits in [
                0,
                1,
                0x0010_0000_0000_0000,
                0x3fe0_0000_0000_0000,
                0x4020_95b0_59d6_7c4d,
                0x4030_0000_0000_0000,
                0x403a_a0f4_d2e0_63cf,
                0x4043_3e21_dc3f_3bd8,
                0x4044_0000_0000_0000,
                0x4050_0000_0000_0000,
                0x5ff6_a09e_667f_3bcd,
                0x7fc2_0dd7_5042_9b6e,
                0x7fef_ffff_ffff_ffff,
            ] {
                let center = f64::from_bits(bits);
                for x in [center.next_down(), center, center.next_up()] {
                    for x in [x, -x] {
                        op.check(x, op.evaluate(x));
                    }
                }
            }
        }
    }

    #[test]
    fn tail_integral_encloses_direct_mpfr_in_the_overlap() {
        for x in [64.0, 65.0, 90.0, 128.0, 256.0] {
            let input = Float::with_val(1024, x);
            let (lo, hi) = normal_reference::erfcx(&Float::with_val(256, x));
            let mut exponential = Float::with_val(1024, &input * &input);
            exponential.exp_mut();
            let mut complement = input;
            complement.erfc_mut();
            let direct = Float::with_val(1024, exponential * complement);
            assert!(lo < direct && direct < hi, "tail overlap at {x}");
        }
    }

    #[test]
    fn logarithmic_formulas_enclose_direct_mpfr_where_both_are_representable() {
        // Direct erfc at the signed argument is independent of the oracle's
        // erfcx/log1p transformations. 2048 bits retain the positive tail even
        // at x=40, well beyond binary64 probability underflow.
        for x in [
            -256.0,
            -100.0,
            -40.0,
            -8.0_f64.next_up(),
            -8.0,
            -1.0,
            1.0,
            8.0,
            38.5,
            40.0,
        ] {
            let mut sqrt_two = Float::with_val(2048, 2);
            sqrt_two.sqrt_mut();
            let input = Float::with_val(2048, -x);
            let mut direct = Float::with_val(2048, &input / &sqrt_two);
            direct.erfc_mut();
            direct >>= 1;
            direct.ln_mut();
            let (lo, hi) = normal_reference::log_cdf(x, 256);
            assert!(lo < direct && direct < hi, "log-CDF overlap at {x}");
        }
    }

    #[test]
    fn extreme_enclosures_refine_without_mpfr_underflow_or_overflow() {
        for (op, x) in [
            (Operation::Erfcx, f64::MAX),
            (Operation::Erfcx, 1e270),
            (Operation::LogCdf, -f64::MAX),
            (Operation::LogCdf, -1e100),
            (Operation::LogCdf, 38.5),
            (Operation::Cdf, -38.5),
        ] {
            let (lo, hi) = op.enclosure(x, 256);
            let (fine_lo, fine_hi) = op.enclosure(x, 1024);
            assert!(lo.is_finite() && hi.is_finite() && lo <= fine_lo && fine_hi <= hi);
            assert!(lo != 0 && hi != 0);
        }
    }

    #[test]
    fn special_values_preserve_payloads_and_signed_zeros() {
        for op in Operation::ALL {
            for x in [
                0.0,
                -0.0,
                f64::INFINITY,
                f64::NEG_INFINITY,
                f64::from_bits(0x7ff0_0000_0000_0042),
                f64::from_bits(0xfff8_0000_0000_1234),
            ] {
                let expected = op.evaluate(x);
                op.check(x, expected);
                let wrong = f64::from_bits(expected.to_bits() ^ 1);
                assert!(std::panic::catch_unwind(|| op.check(x, wrong)).is_err());
            }
        }
    }

    #[test]
    fn independent_oracle_rejects_wrong_tails_signs_and_saturations() {
        for (op, x, wrong) in [
            (Operation::Erfcx, f64::MAX, 0.0),
            (Operation::Erfcx, 64.0, 0.01),
            (Operation::Erfcx, -26.0, f64::INFINITY),
            (Operation::Cdf, -38.0, 0.0),
            (Operation::Cdf, -100.0, -0.0),
            (Operation::Cdf, 40.0, 1.0_f64.next_down()),
            (Operation::LogCdf, 40.0, 0.0),
            (Operation::LogCdf, 10.0, -0.0),
            (Operation::LogCdf, -1e100, f64::NEG_INFINITY),
            (Operation::LogCdf, -f64::MAX, -f64::MAX),
        ] {
            assert!(
                std::panic::catch_unwind(|| op.check(x, wrong)).is_err(),
                "{op:?}: {x}"
            );
        }
    }

    #[test]
    fn compound_allowances_keep_tiny_terms_and_underflow_floor() {
        let p = 2048;
        let exact = Float::with_val(p, 1);
        let bound = Bound::Normal {
            relative_extra: Some(223),
            absolute_extra: Some(123),
        };
        let (lo, hi) = super::super::limits(&exact, &exact, bound).unwrap();
        let expected = (Float::with_val(p, 1) >> 53)
            + (Float::with_val(p, 1) >> 223)
            + (Float::with_val(p, 1) >> 123)
            + (Float::with_val(p, 1) >> 1075);
        assert_eq!(lo, expected);
        assert_eq!(hi, expected);
        // A non-CR candidate can satisfy the published bound. The extra
        // relative term must survive even far below binary64 precision.
        let midpoint = Float::with_val(p, 1) + (Float::with_val(p, 1) >> 53);
        let beyond = midpoint + (Float::with_val(p, 1) >> 110);
        assert_eq!(
            within_bound(1.0, &beyond, &beyond, Operation::Cdf.bound(1.0)),
            Some(true)
        );
        let outside = Float::with_val(p, 1) + (Float::with_val(p, 1) >> 52);
        assert_eq!(within_bound(1.0, &outside, &outside, bound), Some(false));
        let half_min = Float::with_val(p, 1) >> 1075;
        let zero_bound = Bound::Normal {
            relative_extra: None,
            absolute_extra: None,
        };
        assert_eq!(
            within_bound(0.0, &half_min, &half_min, zero_bound),
            Some(true)
        );
        let over = half_min + (Float::with_val(p, 1) >> 1127);
        assert_eq!(within_bound(0.0, &over, &over, zero_bound), Some(false));
    }

    #[test]
    fn packets_include_empty_short_and_simd_remainders() {
        for selector in [0_u8, 1, 2, 255] {
            for count in 0..=65 {
                let mut data = vec![selector];
                for i in 0..count {
                    let x: f64 = [-0.0, 0.5, -8.0, 40.0, -40.0, 64.0][i % 6];
                    data.extend_from_slice(&x.to_bits().to_le_bytes());
                    data.extend_from_slice(&0_u64.to_le_bytes());
                }
                data.extend_from_slice(&[0; 7]);
                check_input(&data);
            }
        }
    }
}
