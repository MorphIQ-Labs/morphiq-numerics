use super::*;

#[test]
fn special_values_follow_the_contract() {
    assert!(asinh(f64::NAN).is_nan());
    assert_eq!(asinh(f64::INFINITY), f64::INFINITY);
    assert_eq!(asinh(f64::NEG_INFINITY), f64::NEG_INFINITY);
    assert_eq!(asinh(0.0).to_bits(), 0.0f64.to_bits());
    assert_eq!(asinh(-0.0).to_bits(), (-0.0f64).to_bits());
    assert_eq!(asinh(f64::from_bits(1)), f64::from_bits(1));
    assert_eq!(asinh(ASINH_IS_X), ASINH_IS_X);
    assert!(asinh(ASINH_IS_X.next_up()) < ASINH_IS_X.next_up());
    assert!(asinh(f64::MAX) > 710.0 && asinh(f64::MAX) < 711.0);
}

/// SplitMix64 (Steele, Lea and Flood, OOPSLA 2014).
fn splitmix64(seed: u64) -> impl Iterator<Item = u64> {
    let mut state = seed;
    core::iter::repeat_with(move || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    })
}

/// Every positive argument the algorithm serves: all binades from
/// `ASINH_IS_X` to the largest finite, with the regions' edges weighted.
fn arguments(seed: u64, count: usize) -> impl Iterator<Item = f64> {
    let mut words = splitmix64(seed);
    core::iter::repeat_with(move || {
        let w = words.next().unwrap();
        let fraction = words.next().unwrap() >> 12;
        let biased = match w % 4 {
            // 2^-26 .. 2^-7, 2^-7 .. 2^28, 2^28 .. 2^1024, anywhere.
            0 => 997 + (w >> 8) % 20,
            1 => 1016 + (w >> 8) % 35,
            2 => 1051 + (w >> 8) % 973,
            _ => 997 + (w >> 8) % 1027,
        };
        f64::from_bits((biased << 52) | fraction)
    })
    .filter(|&x| x > ASINH_IS_X && x.is_finite())
    .take(count)
}

#[test]
fn asinh_is_odd() {
    for x in arguments(0x6173_696e_685f_6f64, 2000) {
        assert_eq!(asinh(-x).to_bits(), (-asinh(x)).to_bits(), "x = {x:e}");
    }
}

#[test]
fn the_fast_path_never_decides_against_the_accurate_path() {
    let mut undecided = 0usize;
    let count = 100_000;
    for x in arguments(0x6173_696e_685f_6661, count) {
        let y = fast(x);
        let accurate = accurate(x, y);
        match decide_with(y, EPS) {
            Some(fast) => assert_eq!(fast.to_bits(), accurate.to_bits(), "x = {x:e}"),
            None => undecided += 1,
        }
    }
    // §5: the test sends about one argument in 2^8.4 to the accurate path.
    assert!(
        undecided * 100 < count,
        "{undecided} of {count} arguments reach the accurate path"
    );
}

#[test]
fn the_regions_agree_where_they_meet() {
    // Each side of a boundary is a different formula; the results are still
    // neighbouring values of one increasing function.
    for edge in [TWO_M7, TWO_28] {
        let below = asinh(edge.next_down());
        let above = asinh(edge);
        assert!(
            below <= above && above - below <= below * 4.0 * f64::EPSILON,
            "{edge:e}"
        );
    }
}

#[test]
fn the_accurate_path_agrees_with_the_fast_value() {
    // The Newton step moves the fast value by its error, 2^-63 relatively.
    for x in arguments(0x6173_696e_685f_6163, 20_000) {
        let y = fast(x);
        let fast_value = y.hi() + y.lo();
        let accurate_value = accurate_value(x, y).to_f64();
        assert!(
            (fast_value - accurate_value).abs()
                <= accurate_value * f64::from_bits(0x3c10_0000_0000_0000),
            "x = {x:e}"
        );
    }
}
