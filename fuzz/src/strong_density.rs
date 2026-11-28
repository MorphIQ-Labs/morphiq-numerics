//! Full-domain independent checks of the strong density, CCDF, centered CDF
//! and log-density contracts in docs/normal.md and docs/log_norm_pdf.md.
use super::{Bound, normal_reference, within_bound};
use morphiq_numerics::normal;
use rug::{Float, float::Round};

/// Log-density regime limits 2^-27 and 2^500.
const TINY: f64 = f64::from_bits(0x3e40_0000_0000_0000);
const HUGE: f64 = f64::from_bits(0x5f30_0000_0000_0000);

#[derive(Clone, Copy, Debug)]
enum Operation {
    Pdf,
    Ccdf,
    Centered,
    LogPdf,
}

impl Operation {
    const ALL: [Self; 4] = [Self::Pdf, Self::Ccdf, Self::Centered, Self::LogPdf];

    fn evaluate(self, x: f64) -> f64 {
        match self {
            Self::Pdf => normal::norm_pdf(x),
            Self::Ccdf => normal::norm_ccdf(x),
            Self::Centered => normal::norm_cdf_centered(x),
            Self::LogPdf => normal::log_norm_pdf(x),
        }
    }

    fn slice(self, xs: &[f64], out: &mut [f64]) {
        match self {
            Self::Pdf => normal::norm_pdf_slice(xs, out),
            Self::Ccdf => normal::norm_ccdf_slice(xs, out),
            Self::Centered => normal::norm_cdf_centered_slice(xs, out),
            // There is no log-density slice; the scalar is checked per lane.
            Self::LogPdf => {
                for (o, &x) in out.iter_mut().zip(xs) {
                    *o = normal::log_norm_pdf(x);
                }
            }
        }
    }

    fn bound(self, x: f64) -> Bound {
        let relative = match self {
            // The far-tail Q256 composition has its own pre-rounding bound.
            Self::Pdf if (23.0..=38.6).contains(&x.abs()) => 222,
            Self::Pdf => 236,
            // CCDF(x) is CDF(-x): central, reflected tail, then complement.
            Self::Ccdf if x.abs() <= 0.5 => 245,
            Self::Ccdf if x > 0.0 => 114,
            Self::Centered if x.abs() <= 0.5 => 246,
            Self::Ccdf | Self::Centered => 111,
            // (1/2 + 2^-50) ulp.
            Self::LogPdf => return Bound::Ulps(50),
        };
        Bound::Normal {
            relative_extra: Some(relative),
            absolute_extra: None,
        }
    }

    /// Exact special values and conservative far screens derived from the
    /// mathematics, not the implementation's threshold encodings.
    fn special(self, x: f64) -> Option<f64> {
        if x.is_nan() {
            return Some(x); // The public contract preserves the encoding.
        }
        match self {
            // phi(40) < exp(-800) < 2^-1100, below half the least subnormal.
            Self::Pdf if x.abs() >= 40.0 => Some(0.0),
            // Mills: Phi(-a) < exp(-a²/2)/(a sqrt(2pi)) < 2^-1100 at a >= 40.
            Self::Ccdf if x >= 40.0 => Some(0.0),
            Self::Ccdf if x <= -40.0 => Some(1.0),
            Self::Ccdf if x == 0.0 => Some(0.5),
            Self::Centered if x.abs() >= 40.0 => Some(0.5_f64.copysign(x)),
            Self::Centered if x == 0.0 => Some(x),
            Self::LogPdf if x.is_infinite() => Some(f64::NEG_INFINITY),
            _ => None,
        }
    }

    fn enclosure(self, x: f64, p: u32) -> (Float, Float) {
        assert!(p >= 256);
        match self {
            Self::Pdf => normal_reference::pdf(x, p),
            Self::Ccdf => normal_reference::cdf(-x, p),
            Self::Centered => normal_reference::centered(x, p),
            Self::LogPdf => normal_reference::log_pdf(x, p),
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
        assert!(!actual.is_nan(), "{self:?}: unexpected NaN");
        match self {
            Self::Pdf => assert!(actual >= 0.0 && !actual.is_sign_negative()),
            Self::Ccdf => assert!((0.0..=1.0).contains(&actual) && !actual.is_sign_negative()),
            // Underflowed centered results keep the input's sign.
            Self::Centered => {
                assert!(actual.abs() <= 0.5 && actual.is_sign_negative() == x.is_sign_negative())
            }
            Self::LogPdf => assert!(actual < 0.0),
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
            // Underflow and saturation are proved to round correctly, and the
            // log-density is correctly rounded in its outer regimes.
            let exact_rounding = lower.is_infinite()
                || lower == 0.0
                || matches!(self, Self::Ccdf) && lower == 1.0
                || matches!(self, Self::Centered) && lower.abs() == 0.5
                || matches!(self, Self::LogPdf) && (x.abs() < TINY || x.abs() > HUGE);
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
            "density oracle unresolved at 8192 bits: {self:?}, x={:016x}",
            x.to_bits()
        );
    }
}

/// Independent selector namespace, modulo four: PDF, CCDF, centered CDF and
/// log-PDF. Up to 65 little-endian (x, unused) pairs; incomplete pairs are
/// ignored.
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
    fn documented_boundaries_and_neighbors_satisfy_their_contracts() {
        // Thresholds and regime joins from the two contract documents, as
        // inputs only.
        for op in Operation::ALL {
            for bits in [
                0,
                1,
                0x0010_0000_0000_0000,
                0x23d0_0000_0000_0000,
                0x3de0_0000_0000_0000,
                0x3e40_0000_0000_0000,
                0x3fe0_0000_0000_0000,
                0x4020_95b0_59d6_7c4d,
                0x4020_bfaf_e7a9_1e68,
                0x4037_0000_0000_0000,
                0x4042_0000_0000_0000,
                0x4042_8000_0000_0000,
                0x4043_3e21_dc3f_3bd8,
                0x4043_4a42_9ac2_a6bc,
                0x4043_4ccc_cccc_cccd,
                0x4044_0000_0000_0000,
                0x5f30_0000_0000_0000,
                0x5ff0_0000_0000_0000,
                0x5ff6_a09e_667f_3bcd,
                0x6000_0000_0000_0000,
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
    fn enclosures_contain_higher_precision_direct_evaluations() {
        for x in [-30.0, -3.0, -0.25, 1.0e-12, 0.5, 5.0, 38.0] {
            // Direct 2048-bit formulas, independent of the endpoint ordering.
            let input = Float::with_val(2048, x);
            let two_pi: Float = Float::with_val(2048, rug::float::Constant::Pi) * 2;
            let half_square = Float::with_val(2048, &input * &input) >> 1;
            let mut density = Float::with_val(2048, -&half_square).exp();
            density /= two_pi.clone().sqrt();
            let half_log: Float = two_pi.ln() >> 1;
            let sum: Float = half_square + half_log;
            let log_density = -sum;
            let scaled = input / Float::with_val(2048, 2).sqrt();
            let centered = scaled.erf() >> 1;
            for (op, direct) in [
                (Operation::Pdf, density),
                (Operation::LogPdf, log_density),
                (Operation::Centered, centered),
            ] {
                let (lo, hi) = op.enclosure(x, 256);
                assert!(lo <= direct && direct <= hi, "{op:?}: {x}");
            }
        }
    }

    #[test]
    fn independent_oracle_rejects_wrong_values_signs_and_saturations() {
        for (op, x, wrong) in [
            (Operation::Pdf, 0.0, 0.4),
            (Operation::Pdf, -38.0, 0.0),
            (Operation::Pdf, 100.0, -0.0),
            (Operation::Ccdf, 38.0, 0.0),
            (Operation::Ccdf, -40.0, 1.0_f64.next_down()),
            (Operation::Centered, 40.0, 0.5_f64.next_down()),
            (Operation::Centered, -1.0, 0.341_344_746_068_542_9),
            (Operation::Centered, -0.0, 0.0),
            (Operation::LogPdf, 0.0, -0.9),
            (Operation::LogPdf, 1.0e100, f64::NEG_INFINITY),
            (Operation::LogPdf, f64::MAX, -f64::MAX),
        ] {
            assert!(
                std::panic::catch_unwind(|| op.check(x, wrong)).is_err(),
                "{op:?}: {x}"
            );
        }
        // Two units in the last place is outside every published bound.
        for op in Operation::ALL {
            for x in [0.25, 3.0, -12.0] {
                let wrong = op.evaluate(x).next_up().next_up();
                assert!(
                    std::panic::catch_unwind(|| op.check(x, wrong)).is_err(),
                    "{op:?}: {x}"
                );
            }
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
                // The density at zero has a bounded, not an exact, contract.
                if matches!(op, Operation::Pdf) && x == 0.0 {
                    continue;
                }
                let wrong = f64::from_bits(expected.to_bits() ^ 1);
                assert!(std::panic::catch_unwind(|| op.check(x, wrong)).is_err());
            }
        }
    }

    #[test]
    fn packets_include_empty_short_and_simd_remainders() {
        for selector in [0_u8, 1, 2, 3, 255] {
            for count in 0..=65 {
                let mut data = vec![selector];
                for i in 0..count {
                    let x: f64 = [-0.0, 0.5, -8.0, 38.0, -40.0, 64.0][i % 6];
                    data.extend_from_slice(&x.to_bits().to_le_bytes());
                    data.extend_from_slice(&0_u64.to_le_bytes());
                }
                data.extend_from_slice(&[0; 7]);
                check_input(&data);
            }
        }
    }
}
