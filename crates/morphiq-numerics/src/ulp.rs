//! Units in the last place, and distances measured in them.
//!
//! The definitions and their derivation from the binary64 encoding are in
//! [`docs/ulp.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/ulp.md).

/// Width of the trailing significand field.
const SIGNIFICAND_BITS: u64 = 52;
/// Mask of the biased exponent field, after shifting it to the low bits.
const EXPONENT_MASK: u64 = 0x7ff;

/// The unit in the last place of `x`: the spacing of the binary64 numbers in
/// the binade that contains `|x|`.
///
/// For finite nonzero `x` with `2^e <= |x| < 2^(e+1)`, the result is
/// `2^(max(e, -1022) - 52)`. Every normal binade has 2^52 equally spaced
/// numbers, and the subnormals share the spacing of the smallest normal
/// binade. `ulp(±0)` is the smallest subnormal, `2^-1074`.
///
/// `ulp(±∞)` is `+∞`, and a NaN is returned unchanged.
///
/// The result is always exact, because it is a power of two that binary64
/// represents. It equals `x.abs().next_up() - x.abs()` for every finite `x`
/// below the largest finite magnitude, where that difference is itself exact.
#[must_use]
pub const fn ulp(x: f64) -> f64 {
    let biased = (x.to_bits() >> SIGNIFICAND_BITS) & EXPONENT_MASK;
    if biased == EXPONENT_MASK {
        // Infinity or NaN: ulp(±∞) = +∞, and a NaN propagates.
        return if x.is_nan() { x } else { f64::INFINITY };
    }
    if biased > SIGNIFICAND_BITS {
        // 2^(biased - 1075) is normal: its biased exponent is biased - 52.
        f64::from_bits((biased - SIGNIFICAND_BITS) << SIGNIFICAND_BITS)
    } else if biased == 0 {
        // Zero and the subnormals share the smallest normal binade's spacing.
        f64::from_bits(1)
    } else {
        // 2^(biased - 1075) is subnormal: a single significand bit.
        f64::from_bits(1 << (biased - 1))
    }
}

/// The position of `x` on a line of integers that increases with `x`.
///
/// Consecutive binary64 numbers map to consecutive integers: `+0` and `-0`
/// both map to `0`, the smallest positive subnormal to `1`, `+∞` to one more
/// than the largest finite number, and negative numbers to the negatives of
/// their magnitudes' positions. So `ordered_bits(y) - ordered_bits(x)` is the
/// number of binary64 steps from `x` to `y`.
///
/// A positive NaN maps above `+∞` and a negative NaN below `-∞`. Those
/// positions order NaNs consistently, but they don't measure a distance; see
/// [`ulps_between`].
#[must_use]
pub const fn ordered_bits(x: f64) -> i64 {
    let magnitude = (x.to_bits() & !(1 << 63)) as i64;
    if x.is_sign_negative() {
        -magnitude
    } else {
        magnitude
    }
}

/// The number of binary64 steps between `a` and `b`, or `None` if either is
/// a NaN.
///
/// It is `|ordered_bits(b) - ordered_bits(a)|`, so `±0` are zero steps
/// apart, and the largest finite number is one step from `+∞`.
#[must_use]
pub const fn ulps_between(a: f64, b: f64) -> Option<u64> {
    if a.is_nan() || b.is_nan() {
        None
    } else {
        Some(ordered_bits(a).abs_diff(ordered_bits(b)))
    }
}

#[cfg(test)]
mod tests {
    use super::{ordered_bits, ulp, ulps_between};

    /// Every binade's least and greatest member, of both signs, and the
    /// numbers around zero.
    fn binade_edges() -> impl Iterator<Item = f64> {
        (0_u64..=2046).flat_map(|biased| {
            let least = f64::from_bits(biased << 52);
            let greatest = f64::from_bits((biased << 52) | ((1 << 52) - 1));
            [least, greatest, -least, -greatest]
        })
    }

    #[test]
    fn ulp_is_the_spacing_to_the_next_magnitude_in_every_binade() {
        for x in binade_edges() {
            let magnitude = x.abs();
            let expected = if magnitude == f64::MAX {
                magnitude - magnitude.next_down()
            } else {
                magnitude.next_up() - magnitude
            };
            assert_eq!(ulp(x).to_bits(), expected.to_bits(), "ulp({x:e})");
        }
    }

    #[test]
    fn ulp_of_zero_infinity_and_nan() {
        assert_eq!(ulp(0.0).to_bits(), f64::from_bits(1).to_bits());
        assert_eq!(ulp(-0.0).to_bits(), f64::from_bits(1).to_bits());
        assert_eq!(ulp(f64::INFINITY), f64::INFINITY);
        assert_eq!(ulp(f64::NEG_INFINITY), f64::INFINITY);
        let nan = f64::from_bits(0x7ff8_0000_0000_0dad);
        assert_eq!(ulp(nan).to_bits(), nan.to_bits());
    }

    #[test]
    fn ulp_matches_the_spacing_at_seeded_random_magnitudes() {
        // A fixed xorshift64 sequence: the inputs are reproducible and need
        // no platform function.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        for _ in 0..100_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let x = f64::from_bits(state);
            if !x.is_finite() || x.abs() == f64::MAX {
                continue;
            }
            let magnitude = x.abs();
            assert_eq!(
                ulp(x).to_bits(),
                (magnitude.next_up() - magnitude).to_bits(),
                "ulp({x:e})"
            );
        }
    }

    #[test]
    fn ordered_bits_advance_by_one_per_binary64_step() {
        for x in binade_edges().chain([0.0, -0.0]) {
            if x.is_finite() && x != f64::MAX {
                assert_eq!(ordered_bits(x.next_up()), ordered_bits(x) + 1, "{x:e}");
            }
            if x.is_finite() && x != f64::MIN {
                assert_eq!(ordered_bits(x.next_down()), ordered_bits(x) - 1, "{x:e}");
            }
        }
        assert_eq!(ordered_bits(f64::MAX) + 1, ordered_bits(f64::INFINITY));
        assert_eq!(ordered_bits(f64::MIN) - 1, ordered_bits(f64::NEG_INFINITY));
    }

    #[test]
    fn ordered_bits_identify_the_signed_zeros() {
        assert_eq!(ordered_bits(0.0), 0);
        assert_eq!(ordered_bits(-0.0), 0);
        assert_eq!(ordered_bits(f64::from_bits(1)), 1);
        assert_eq!(ordered_bits(-f64::from_bits(1)), -1);
    }

    #[test]
    fn ordered_bits_place_nans_outside_the_infinities() {
        let positive = f64::from_bits(0x7ff8_0000_0000_0000);
        let negative = f64::from_bits(0xfff8_0000_0000_0000);
        assert!(ordered_bits(positive) > ordered_bits(f64::INFINITY));
        assert!(ordered_bits(negative) < ordered_bits(f64::NEG_INFINITY));
    }

    #[test]
    fn ulps_between_counts_steps_and_refuses_nans() {
        assert_eq!(ulps_between(0.0, -0.0), Some(0));
        assert_eq!(ulps_between(1.0, 1.0_f64.next_up()), Some(1));
        assert_eq!(ulps_between(-f64::from_bits(1), f64::from_bits(1)), Some(2));
        assert_eq!(ulps_between(f64::MAX, f64::INFINITY), Some(1));
        // From the largest subnormal across the boundary to the smallest normal.
        assert_eq!(
            ulps_between(f64::from_bits((1 << 52) - 1), f64::MIN_POSITIVE),
            Some(1)
        );
        assert_eq!(ulps_between(f64::NAN, 1.0), None);
        assert_eq!(ulps_between(1.0, f64::NAN), None);
        // Symmetric.
        assert_eq!(ulps_between(-3.5, 2.0), ulps_between(2.0, -3.5));
    }
}
