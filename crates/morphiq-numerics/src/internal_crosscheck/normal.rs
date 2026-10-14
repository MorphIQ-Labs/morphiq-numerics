//! Compare the normal components' actual integer significands and DW words
//! with their extracted Coq transcriptions, before final rounding can hide a
//! reduction or operation-order discrepancy.
use super::{SplitMix64, q256};
use crate::normal_distribution::{self, accurate};
use crate::q256::Q256;
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
    for i in 0..256 {
        let high = match i {
            0 => 16.0,
            1 => 16.0_f64.next_up(),
            2 => 32.0,
            3 => f64::MAX * 0.5,
            _ => f64::from_bits(
                16.0_f64.to_bits() + rng.next_u64() % (0x7fe0_0000_0000_0000 - 16.0_f64.to_bits()),
            ),
        };
        let high = Q256::from_f64(high);
        let low = high.mul_pow2(-100);
        let x = high.add(if i % 2 == 0 { low } else { low.neg() });
        writeln!(
            out,
            "normal_erfcx_asym {} : {}",
            q256(x),
            q256(crate::erfcx::accurate::asym_value(x))
        )
        .unwrap();
    }
    for i in 0..256 {
        let x = match i {
            0 => f64::from_bits(1),
            1 => f64::MIN_POSITIVE,
            2 => f64::MAX,
            3 => 23.0,
            _ => f64::from_bits(1 + rng.next_u64() % f64::MAX.to_bits()),
        };
        writeln!(
            out,
            "normal_scaled_argument {:016x} : {}",
            x.to_bits(),
            q256(accurate::scaled_argument(x))
        )
        .unwrap();
        let x = match i {
            0 => 23.0,
            1 => 38.6,
            2 => 38.5,
            _ => f64::from_bits(
                23.0_f64.to_bits() + rng.next_u64() % (38.6_f64.to_bits() - 23.0_f64.to_bits()),
            ),
        };
        writeln!(
            out,
            "normal_accurate_tail_asym {:016x} : {}",
            x.to_bits(),
            q256(accurate::tail(x))
        )
        .unwrap();
    }
    for i in 0..256 {
        let high = match i {
            0 => 0.5,
            1 => 1.0,
            2 => 2.0,
            3 => 4.0,
            4 => 8.0_f64.next_down(),
            _ => f64::from_bits(
                0.375_f64.to_bits() + rng.next_u64() % (8.0_f64.to_bits() - 0.375_f64.to_bits()),
            ),
        };
        let high = Q256::from_f64(high);
        let low = high.mul_pow2(-100);
        let x = high.add(if i % 2 == 0 { low } else { low.neg() });
        writeln!(
            out,
            "normal_erfcx_small_table {} : {}",
            q256(x),
            q256(crate::erfcx::accurate::positive(x))
        )
        .unwrap();
    }
    // Extended inputs can straddle a table boundary while rounding to the
    // boundary itself. Exercise both sides at each last-binade cell and the
    // cap just below 16, where the rounded lookup would otherwise be outside
    // the table. Check the significand before final binary64 rounding.
    let mut table = Vec::new();
    for i in 0..32 {
        let high = Q256::from_f64(8.0 + f64::from(i) * 0.25);
        for shift in [50, 60, 100, 200, 250] {
            let low = Q256::ONE.mul_pow2(-shift);
            table.extend([high.add(low.neg()), high, high.add(low)]);
        }
    }
    for shift in [49, 50, 51, 52, 60, 100, 200, 250] {
        table.push(Q256::from_f64(16.0).add(Q256::ONE.mul_pow2(-shift).neg()));
    }
    for _ in 0..256 {
        let high = Q256::from_f64(f64::from_bits(
            0.25_f64.to_bits() + rng.next_u64() % (16.0_f64.to_bits() - 0.25_f64.to_bits()),
        ));
        table.push(high.add(high.mul_pow2(-100)));
    }
    for x in table {
        writeln!(
            out,
            "normal_erfcx_extended_table {} : {}",
            q256(x),
            q256(crate::erfcx::accurate::positive(x))
        )
        .unwrap();
        writeln!(
            out,
            "normal_erfcx_positive {} : {}",
            q256(x),
            q256(crate::erfcx::accurate::positive(x))
        )
        .unwrap();
    }
    for i in 0..256 {
        let high = Q256::from_f64(match i {
            0 => 16.0,
            1 => 16.0_f64.next_up(),
            2 => f64::MAX * 0.5,
            _ => f64::from_bits(
                16.0_f64.to_bits() + rng.next_u64() % (0x7fe0_0000_0000_0000 - 16.0_f64.to_bits()),
            ),
        });
        let x = high.add(high.mul_pow2(-100));
        writeln!(
            out,
            "normal_erfcx_positive {} : {}",
            q256(x),
            q256(crate::erfcx::accurate::positive(x))
        )
        .unwrap();
    }
    for i in 0..512 {
        let x = match i {
            0 => 0.5,
            1 => 0.5_f64.next_up(),
            2 => 1.0,
            3 => 8.0,
            4 => 23.0,
            5 => 38.6,
            _ => f64::from_bits(
                0.5_f64.to_bits() + rng.next_u64() % (38.6_f64.to_bits() - 0.5_f64.to_bits()),
            ),
        };
        writeln!(
            out,
            "normal_accurate_tail {:016x} : {}",
            x.to_bits(),
            q256(accurate::tail(x))
        )
        .unwrap();
    }
}
