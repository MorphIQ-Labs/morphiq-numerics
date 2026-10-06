//! `sqrt` against the definition of rounding to nearest, decided exactly.

use super::sqrt;
use crate::random::SplitMix64;
use crate::test_exact::Exact;
use core::cmp::Ordering;

/// `r` is `RN(√x)`: `(r − ulp/2)² < x < (r + ulp/2)²`, strictly, since a
/// square root is never a midpoint.
fn check(x: f64) {
    let r = sqrt(x);
    let half_ulp = Exact::of_f64(crate::ulp::ulp(r)).mul(&Exact::pow2(-1));
    let (r, x_exact) = (Exact::of_f64(r), Exact::of_f64(x));
    let below = r.sub(&half_ulp);
    let above = r.add(&half_ulp);
    assert_eq!(
        below.mul(&below).cmp(&x_exact),
        Ordering::Less,
        "sqrt({x:e})"
    );
    assert_eq!(
        above.mul(&above).cmp(&x_exact),
        Ordering::Greater,
        "sqrt({x:e})"
    );
}

#[test]
fn sqrt_rounds_to_nearest() {
    let mut rng = SplitMix64::new(0x7371_7274_0000_0001);
    for _ in 0..100_000 {
        check(f64::from_bits((rng.next_u64() % 0x7ff0_0000_0000_0000) | 1));
    }
    for _ in 0..20_000 {
        // y² and y·next_up(y) = (y + ulp/2)² − ulp²/4, and their neighbours:
        // roots just beside a binary64 number or a midpoint.
        let y = f64::from_bits(0x3ff0_0000_0000_0000 | (rng.next_u64() >> 12));
        let up = f64::from_bits(y.to_bits() + 1);
        for x in [y * y, y * up] {
            for b in [x.to_bits() - 1, x.to_bits(), x.to_bits() + 1] {
                check(f64::from_bits(b));
            }
        }
    }
    for bits in [
        1,
        2,
        3,
        0x000f_ffff_ffff_ffff,
        0x0010_0000_0000_0000,
        0x3ff0_0000_0000_0001,
        0x3fef_ffff_ffff_ffff,
        0x4000_0000_0000_0000,
        0x7fef_ffff_ffff_ffff,
    ] {
        check(f64::from_bits(bits));
    }
}

#[test]
fn sqrt_is_exact_on_squares_and_handles_special_values() {
    let mut rng = SplitMix64::new(0x7371_7274_0000_0002);
    for _ in 0..10_000 {
        // A 26-bit integer times a power of two squares exactly.
        #[allow(clippy::cast_precision_loss)] // below 2^26
        let k = ((rng.next_u64() >> 38) | 1) as f64;
        let y = k * f64::from_bits((1023 + (rng.next_u64() % 400) - 200) << 52);
        assert_eq!(sqrt(y * y).to_bits(), y.to_bits());
    }
    assert_eq!(sqrt(0.0).to_bits(), 0);
    assert_eq!(sqrt(-0.0).to_bits(), 1 << 63);
    assert_eq!(sqrt(f64::INFINITY), f64::INFINITY);
    assert!(sqrt(-1.0).is_nan());
    assert!(sqrt(f64::NEG_INFINITY).is_nan());
    assert!(sqrt(f64::NAN).is_nan());
    assert!(sqrt(-f64::from_bits(1)).is_nan());
}
