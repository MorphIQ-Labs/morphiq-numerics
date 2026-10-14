//! Compare the normal components' actual integer significands and DW words
//! with their extracted Coq transcriptions, before final rounding can hide a
//! reduction or operation-order discrepancy.
use super::{SplitMix64, q256};
use crate::normal_distribution::{self, accurate};
use std::fmt::Write as _;
use std::string::String;
use std::vec::Vec;

pub(super) fn write(out: &mut String) {
    let mut rng = SplitMix64::new(0x6e6f_726d_636f_7101);
    let mut central = Vec::new();
    for x in [
        0.0_f64,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        f64::from_bits(0x23d0_0000_0000_0000),
        f64::from_bits(0x26f0_0000_0000_0000),
        f64::from_bits(0x3de0_0000_0000_0000),
        0.25,
        0.5,
    ] {
        for y in [x.next_down(), x, x.next_up()] {
            if y.abs() <= 0.5 {
                central.extend([y, -y]);
            }
        }
    }
    for _ in 0..256 {
        let bits = rng.next_u64() % (0.5_f64.to_bits() + 1);
        central.extend([f64::from_bits(bits), -f64::from_bits(bits)]);
    }
    for x in central {
        writeln!(
            out,
            "normal_accurate_center {:016x} : {}",
            x.to_bits(),
            q256(accurate::center(x))
        )
        .unwrap();
        writeln!(
            out,
            "normal_accurate_central_cdf {:016x} : {}",
            x.to_bits(),
            q256(accurate::central_cdf(x))
        )
        .unwrap();
    }
    let lower = f64::from_bits(0x26f0_0000_0000_0000);
    for i in 0..512 {
        let x = match i {
            0 => lower,
            1 => lower.next_up(),
            2 => 0.5,
            3 => 8.0,
            4 => 37.0,
            5 => 38.5,
            _ => f64::from_bits(
                lower.to_bits() + rng.next_u64() % (38.5_f64.to_bits() - lower.to_bits()),
            ),
        };
        writeln!(
            out,
            "normal_accurate_gaussian {:016x} : {}",
            x.to_bits(),
            q256(accurate::gaussian(x))
        )
        .unwrap();
        writeln!(
            out,
            "normal_accurate_density {:016x} : {}",
            x.to_bits(),
            q256(accurate::density(x))
        )
        .unwrap();
    }
    for i in 0..512 {
        #[allow(clippy::cast_precision_loss)] // exactly 53 random bits
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        let x = match i {
            0 => f64::from_bits(0x3de0_0000_0000_0000),
            1 => 0.5,
            2 => 37.0,
            _ => 0.5 + 36.5 * u,
        };
        let (y, k) = normal_distribution::gaussian(x);
        writeln!(
            out,
            "normal_gaussian {:016x} : {k} {:016x} {:016x}",
            x.to_bits(),
            y.hi().to_bits(),
            y.lo().to_bits()
        )
        .unwrap();
    }
}
