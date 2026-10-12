//! The 512-entry exponential stages for `exp2` (docs/exp2.md).
//! `formal/exp/Exp2Stages.v` proves the reduction, both evaluations and tests.

use super::tables::{LN2_HI, LN2_LO};
use crate::eft::two_prod;
use crate::exp::{decide, stage_a_at, stage_b_at};

const SHIFTER: f64 = f64::from_bits(0x4338_0000_0000_0000);
/// Stage A includes the error of rounding ln(2) before multiplying.
const E_A: f64 = f64::from_bits(0x3c40_0000_0000_0000); // 2^-59
/// The compensated product satisfies exp's original stage B bound.
const E_B: f64 = f64::from_bits(0x3b90_0000_0000_0000); // 2^-70
const FLOOR: u64 = (1023 - 55) << 52;
const LIMIT: u64 = 1016.0_f64.to_bits();

#[inline]
pub(crate) fn stages(x: f64) -> Option<f64> {
    let magnitude = x.to_bits() & !(1 << 63);
    if !(FLOOR..LIMIT).contains(&magnitude) {
        return None;
    }
    let reduced = Stages::of(x);
    let (y, l) = reduced.a_value();
    if let Some(v) = decide(y, l, E_A, reduced.k) {
        return Some(v);
    }
    let (y, l) = reduced.b_value();
    decide(y, l, E_B, reduced.k)
}

pub(super) struct Stages {
    pub(super) k: i64,
    j: usize,
    d: f64,
}

impl Stages {
    pub(super) fn of(x: f64) -> Self {
        let t = x * 512.0 + SHIFTER;
        let n = t - SHIFTER;
        #[allow(clippy::cast_possible_wrap)] // both encodings are below 2^63
        let ni = t.to_bits() as i64 - SHIFTER.to_bits() as i64;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // nine bits
        let j = (ni & 511) as usize;
        Self {
            j,
            k: ni >> 9,
            d: x - n * (1.0 / 512.0),
        }
    }

    pub(super) fn a_value(&self) -> (f64, f64) {
        stage_a_at(self.j, self.d * LN2_HI)
    }

    pub(super) fn b_value(&self) -> (f64, f64) {
        let (p, e) = two_prod(self.d, LN2_HI);
        let rl = e + self.d * LN2_LO;
        let rh = (p + 6144.0) - 6144.0;
        let rt = (p - rh) + rl;
        stage_b_at(self.j, rh, rt)
    }
}
