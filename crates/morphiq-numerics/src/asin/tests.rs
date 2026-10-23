use super::*;

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

/// `2^e` exactly, for a normal exponent.
fn pow2(e: i32) -> f64 {
    #[allow(clippy::cast_sign_loss)] // 1023 + e > 0
    f64::from_bits(((1023 + e) as u64) << 52)
}

/// Every positive argument the algorithm serves: all binades from `ASIN_IS_X`
/// to 1, and near 1 where the complement branch's `δ` is small.
fn arguments(seed: u64, count: usize) -> impl Iterator<Item = f64> {
    let mut words = splitmix64(seed);
    core::iter::repeat_with(move || {
        let w = words.next().unwrap();
        let unit = (words.next().unwrap() >> 11) as f64 * pow2(-53);
        match w % 4 {
            0 => (1.0 + unit) * pow2(-26 + ((w >> 8) % 26) as i32),
            1 => 0.5 + 0.5 * unit,
            2 => 1.0 - (1.0 + unit) * pow2(-2 - ((w >> 8) % 51) as i32),
            _ => unit,
        }
    })
    .filter(|&x| (ASIN_IS_X..1.0).contains(&x))
    .take(count)
}

#[test]
fn special_values_follow_the_contract() {
    assert!(asin(f64::NAN).is_nan());
    assert!(asin(f64::INFINITY).is_nan());
    assert!(asin(f64::NEG_INFINITY).is_nan());
    assert!(asin(1.0 + f64::EPSILON).is_nan());
    assert!(asin(-1.0 - f64::EPSILON).is_nan());
    assert_eq!(asin(0.0).to_bits(), 0.0f64.to_bits());
    assert_eq!(asin(-0.0).to_bits(), (-0.0f64).to_bits());
    assert_eq!(asin(1.0), HALF_PI_F64);
    assert_eq!(asin(-1.0), -HALF_PI_F64);
    assert_eq!(asin(f64::from_bits(1)), f64::from_bits(1));
    assert_eq!(asin(ASIN_IS_X.next_down()), ASIN_IS_X.next_down());
    assert!(asin(ASIN_IS_X) > ASIN_IS_X);
}

#[test]
fn asin_is_odd() {
    for x in arguments(0x6173_696e_5f6f_6464, 2000) {
        assert_eq!(asin(-x).to_bits(), (-asin(x)).to_bits(), "x = {x:e}");
    }
}

#[test]
fn the_fast_path_never_decides_against_the_accurate_path() {
    let mut undecided = 0usize;
    let count = 200_000;
    for x in arguments(0x6173_696e_5f66_6173, count) {
        let reduced = Reduced::of(x);
        let (y, start) = reduced.fast();
        let accurate = reduced.accurate(start);
        match decide_with(y, EPS) {
            Some(fast) => assert_eq!(fast.to_bits(), accurate.to_bits(), "x = {x:e}"),
            None => undecided += 1,
        }
    }
    // §6: the test sends about one argument in 2^8.4 to the accurate path.
    assert!(
        undecided * 100 < count,
        "{undecided} of {count} arguments reach the accurate path"
    );
}

#[test]
fn the_branches_agree_at_their_boundary() {
    // Either side of SPLIT is served by a different formula; the results must
    // still be the neighbouring binary64 numbers of a continuous function.
    let below = asin(SPLIT);
    let above = asin(SPLIT.next_up());
    assert!(below < above);
    assert!(above - below < 4.0 * f64::EPSILON);
}
