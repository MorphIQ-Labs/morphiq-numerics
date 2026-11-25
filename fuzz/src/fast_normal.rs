//! Independent directed MPFR enclosures for the accelerated normal contracts.
//! Outside those domains this target checks exact strong-owner delegation only.
use super::{Bound, within_bound};
use morphiq_numerics::{fast::normal as fast, normal};
use rug::{Float, float::Round};

#[derive(Clone, Copy, Debug)]
enum Operation {
    Erfcx,
    Cdf,
    LogCdf,
}

impl Operation {
    const ALL: [Self; 3] = [Self::Erfcx, Self::Cdf, Self::LogCdf];

    fn accelerated(self, x: f64) -> bool {
        // Public mathematical domains, independent of runtime dispatch bits.
        let minimum = f64::from_bits((1023 - 33) << 52);
        match self {
            Self::Erfcx => (-0.5..16.0).contains(&x) && x.abs() >= minimum,
            Self::Cdf | Self::LogCdf => {
                (-22.5..=-minimum).contains(&x) || (minimum..=8.0).contains(&x)
            }
        }
    }

    fn evaluate(self, x: f64) -> f64 {
        match self {
            Self::Erfcx => fast::erfcx(x),
            Self::Cdf => fast::norm_cdf(x),
            Self::LogCdf => fast::log_norm_cdf(x),
        }
    }

    fn owner(self, x: f64) -> f64 {
        match self {
            Self::Erfcx => normal::erfcx(x),
            Self::Cdf => normal::norm_cdf(x),
            Self::LogCdf => normal::log_norm_cdf(x),
        }
    }

    fn slice(self, xs: &[f64], out: &mut [f64]) {
        match self {
            Self::Erfcx => fast::erfcx_slice(xs, out),
            Self::Cdf => fast::norm_cdf_slice(xs, out),
            Self::LogCdf => fast::log_norm_cdf_slice(xs, out),
        }
    }

    fn enclosure(self, x: f64, precision: u32) -> (Float, Float) {
        assert!(self.accelerated(x));
        assert!(
            precision >= 256,
            "oracle must represent the input square exactly"
        );
        if matches!(self, Self::Erfcx) {
            let input = Float::with_val(precision, x);
            // The binary64 square has at most 106 significant bits, so this
            // multiplication is exact at every oracle precision (>= 256).
            let square = Float::with_val(precision, &input * &input);
            let mut lower_exp = square.clone();
            let mut upper_exp = square;
            lower_exp.exp_round(Round::Down);
            upper_exp.exp_round(Round::Up);
            let mut lower_erfc = input.clone();
            let mut upper_erfc = input;
            lower_erfc.erfc_round(Round::Down);
            upper_erfc.erfc_round(Round::Up);
            // Both factors are positive; monotone multiplication encloses
            // exp(x*x) * erfc(x), without using a library approximation.
            return (
                Float::with_val_round(precision, &lower_exp * &lower_erfc, Round::Down).0,
                Float::with_val_round(precision, &upper_exp * &upper_erfc, Round::Up).0,
            );
        }
        let mut sqrt_lo = Float::with_val(precision, 2);
        let mut sqrt_hi = sqrt_lo.clone();
        sqrt_lo.sqrt_round(Round::Down);
        sqrt_hi.sqrt_round(Round::Up);
        let magnitude = Float::with_val(precision, x.abs());
        let arg_lo = Float::with_val_round(precision, &magnitude / &sqrt_hi, Round::Down).0;
        let arg_hi = Float::with_val_round(precision, &magnitude / &sqrt_lo, Round::Up).0;
        // erfc is decreasing, so reverse the argument endpoints.
        let mut lo = arg_hi;
        let mut hi = arg_lo;
        lo.erfc_round(Round::Down);
        hi.erfc_round(Round::Up);
        lo >>= 1;
        hi >>= 1;
        if x > 0.0 {
            let one = Float::with_val(precision, 1);
            (lo, hi) = (
                Float::with_val_round(precision, &one - &hi, Round::Down).0,
                Float::with_val_round(precision, &one - &lo, Round::Up).0,
            );
        }
        if matches!(self, Self::LogCdf) {
            // ln is increasing; the CDF enclosure is strictly positive.
            lo.ln_round(Round::Down);
            hi.ln_round(Round::Up);
        }
        (lo, hi)
    }

    fn bounds(self, x: f64) -> &'static [Bound] {
        match self {
            Self::Erfcx => &[Bound::Relative(51)],
            Self::Cdf if x < 0.0 => &[Bound::Absolute(49), Bound::Relative(48)],
            Self::Cdf => &[Bound::Absolute(49)],
            Self::LogCdf => &[Bound::Mixed {
                relative: 51,
                absolute: 48,
            }],
        }
    }

    fn check(self, x: f64, actual: f64) {
        if !self.accelerated(x) {
            assert_eq!(
                actual.to_bits(),
                self.owner(x).to_bits(),
                "{self:?} fallback: x={:016x}",
                x.to_bits()
            );
            // This is delegation coverage, not an independent oracle for the
            // strong owner's full-domain numerical contract.
            return;
        }
        assert!(
            actual.is_normal(),
            "{self:?} accelerated result must be normal"
        );
        match self {
            Self::Erfcx => assert!(actual > 0.0),
            Self::Cdf => assert!(actual > 0.0 && actual <= 1.0),
            Self::LogCdf => assert!(actual < 0.0),
        }
        let bounds = self.bounds(x);
        for precision in [256, 512, 1024, 2048, 4096, 8192] {
            let (lo, hi) = self.enclosure(x, precision);
            let mut settled = true;
            for &bound in bounds {
                match within_bound(actual, &lo, &hi, bound) {
                    Some(true) => (),
                    None => settled = false,
                    Some(false) => panic!(
                        "{self:?} contract violation: x={:016x}, got={:016x}, bound={bound:?}, precision={precision}",
                        x.to_bits(),
                        actual.to_bits()
                    ),
                }
            }
            if settled {
                return;
            }
        }
        panic!(
            "MPFR oracle unresolved at 8192 bits: {self:?}, x={:016x}",
            x.to_bits()
        );
    }
}

/// Separate selector namespace: erfcx, CDF, log-CDF modulo three, followed by
/// up to 65 little-endian (x, unused) pairs. Partial trailing pairs are ignored.
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
    fn bounded_contracts_accept_valid_non_cr_results() {
        for (op, x) in [
            (Operation::Erfcx, 1.0),
            (Operation::Cdf, -8.0),
            (Operation::Cdf, 1.0),
            (Operation::LogCdf, 1.0),
        ] {
            let (lo, hi) = op.enclosure(x, 256);
            let rounded = lo.to_f64_round(Round::Nearest);
            assert_eq!(rounded.to_bits(), hi.to_f64_round(Round::Nearest).to_bits());
            op.check(x, rounded.next_up());
        }
    }

    #[test]
    fn retained_lower_tail_witness_replays() {
        check_input(include_bytes!("../regressions/fast_normal/cdf-lower-tail"));
    }

    #[test]
    fn directed_composition_encloses_higher_precision_results() {
        for op in Operation::ALL {
            for x in [-22.5, -8.0, -0.5, -1e-9, 1e-9, 0.5, 8.0, 15.99] {
                if !op.accelerated(x) {
                    continue;
                }
                let (lo, hi) = op.enclosure(x, 256);
                let (fine_lo, fine_hi) = op.enclosure(x, 1024);
                assert!(lo <= fine_lo && fine_hi <= hi, "{op:?}: {x}");
                op.check(x, op.evaluate(x));
            }
        }
    }

    #[test]
    fn cdf_lower_tail_enforces_relative_as_well_as_absolute_error() {
        let op = Operation::Cdf;
        let x = -22.5;
        let (lo, hi) = op.enclosure(x, 256);
        let wrong = op.evaluate(x) * (1.0 + f64::from_bits((1023 - 40) << 52));
        assert_eq!(
            within_bound(wrong, &lo, &hi, Bound::Absolute(49)),
            Some(true)
        );
        assert_eq!(
            within_bound(wrong, &lo, &hi, Bound::Relative(48)),
            Some(false)
        );
        assert!(std::panic::catch_unwind(|| op.check(x, wrong)).is_err());
    }

    #[test]
    fn oracle_rejects_wrong_sign_range_and_excess_error() {
        for (op, x, wrong) in [
            (Operation::Erfcx, 1.0, 1.0),
            (Operation::Erfcx, -0.5, -1.0),
            (Operation::Cdf, 1.0, 0.5),
            (Operation::Cdf, -8.0, 0.0),
            (Operation::Cdf, 1.0, 1.1),
            (Operation::LogCdf, -8.0, -32.0),
            (Operation::LogCdf, 1.0, 0.0),
        ] {
            assert!(std::panic::catch_unwind(|| op.check(x, wrong)).is_err());
        }
    }

    #[test]
    fn fallback_checks_include_signed_zero_and_nan_payloads() {
        for op in Operation::ALL {
            for x in [
                0.0,
                -0.0,
                -30.0,
                32.0,
                f64::INFINITY,
                f64::NEG_INFINITY,
                f64::from_bits(0x7ff0_0000_0000_0042),
                f64::from_bits(0xfff8_0000_0000_1234),
            ] {
                assert!(!op.accelerated(x));
                let correct = op.evaluate(x);
                op.check(x, correct);
                let wrong = f64::from_bits(correct.to_bits() ^ 1);
                assert!(std::panic::catch_unwind(|| op.check(x, wrong)).is_err());
            }
        }
    }

    #[test]
    fn public_domain_endpoints_and_neighbors() {
        let tiny = f64::from_bits((1023 - 33) << 52);
        for op in Operation::ALL {
            for edge in [-22.5_f64, -8.0, -0.5, -tiny, tiny, 8.0, 16.0] {
                for x in [edge.next_down(), edge, edge.next_up()] {
                    op.check(x, op.evaluate(x));
                }
            }
        }
        assert!(Operation::Erfcx.accelerated(-0.5));
        assert!(!Operation::Erfcx.accelerated((-0.5_f64).next_down()));
        assert!(!Operation::Erfcx.accelerated(16.0));
        for op in [Operation::Cdf, Operation::LogCdf] {
            assert!(op.accelerated(-22.5));
            assert!(!op.accelerated((-22.5_f64).next_down()));
            assert!(op.accelerated(8.0));
            assert!(!op.accelerated(8.0_f64.next_up()));
            assert!(op.accelerated(tiny));
            assert!(!op.accelerated(tiny.next_down()));
        }
    }

    #[test]
    fn absolute_and_mixed_allowances_preserve_exact_boundary_and_floor() {
        let zero = Float::with_val(256, 0);
        for bound in [
            Bound::Absolute(48),
            Bound::Mixed {
                relative: 51,
                absolute: 48,
            },
        ] {
            let floor = f64::from_bits((1023 - 48) << 52);
            assert_eq!(within_bound(floor, &zero, &zero, bound), Some(true));
            assert_eq!(
                within_bound(floor.next_up(), &zero, &zero, bound),
                Some(false)
            );
        }
        let exact = Float::with_val(256, -8);
        let bound = Bound::Mixed {
            relative: 51,
            absolute: 48,
        };
        let edge = -8.0 + f64::from_bits((1023 - 47) << 52);
        assert_eq!(within_bound(edge, &exact, &exact, bound), Some(true));
        assert_eq!(
            within_bound(edge.next_up(), &exact, &exact, bound),
            Some(false)
        );
        let lo = Float::with_val(256, -8);
        let hi = Float::with_val(256, -8.0 + f64::from_bits((1023 - 45) << 52));
        let midpoint = -8.0 + f64::from_bits((1023 - 46) << 52);
        for bound in [Bound::Absolute(48), bound] {
            assert_eq!(within_bound(midpoint, &lo, &hi, bound), None);
        }
    }

    #[test]
    fn packets_cover_empty_short_fixed_lengths_and_remainders() {
        for selector in [0_u8, 1, 2, 255] {
            for count in 0..=65 {
                let mut data = vec![selector];
                for i in 0..count {
                    let x: f64 = [-22.5, -0.5, 0.5, 1.0, 8.0, 16.0, -0.0][i % 7];
                    data.extend_from_slice(&x.to_bits().to_le_bytes());
                    data.extend_from_slice(&0_u64.to_le_bytes());
                }
                data.extend_from_slice(&[0; 7]); // incomplete pair has no effect
                check_input(&data);
            }
        }
    }
}
