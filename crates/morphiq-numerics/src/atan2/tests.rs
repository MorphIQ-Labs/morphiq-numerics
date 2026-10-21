use super::*;

#[test]
fn special_values_follow_the_contract() {
    let nan = f64::NAN;
    let inf = f64::INFINITY;
    assert!(atan2(nan, 1.0).is_nan() && atan2(1.0, nan).is_nan() && atan2(nan, nan).is_nan());
    assert_eq!(atan2(0.0, 0.0).to_bits(), 0.0f64.to_bits());
    assert_eq!(atan2(-0.0, 0.0).to_bits(), (-0.0f64).to_bits());
    assert_eq!(atan2(0.0, -0.0), PI_F64);
    assert_eq!(atan2(-0.0, -0.0), -PI_F64);
    assert_eq!(atan2(0.0, -1.0), PI_F64);
    assert_eq!(atan2(-0.0, 1.0).to_bits(), (-0.0f64).to_bits());
    assert_eq!(atan2(1.0, 0.0), HALF_PI_F64);
    assert_eq!(atan2(-1.0, -0.0), -HALF_PI_F64);
    assert_eq!(atan2(inf, inf), QUARTER_PI_F64);
    assert_eq!(atan2(-inf, -inf), -THREE_QUARTER_PI_F64);
    assert_eq!(atan2(inf, -inf), THREE_QUARTER_PI_F64);
    assert_eq!(atan2(inf, 5.0), HALF_PI_F64);
    assert_eq!(atan2(5.0, inf).to_bits(), 0.0f64.to_bits());
    assert_eq!(atan2(-5.0, inf).to_bits(), (-0.0f64).to_bits());
    assert_eq!(atan2(5.0, -inf), PI_F64);
    assert_eq!(atan2(1.0, 1.0), QUARTER_PI_F64);
    assert_eq!(atan2(1.0, -1.0), THREE_QUARTER_PI_F64);
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

/// Pairs `(n, d)` with `n ≤ d` whose ratio is at least `2^-900`: random
/// significands, ratios across the unit interval and out to `2^-60`, at any
/// scale, subnormal operands included.
fn pairs(seed: u64, count: usize) -> impl Iterator<Item = (f64, f64)> {
    let mut words = splitmix64(seed);
    core::iter::repeat_with(move || {
        let w = words.next().unwrap();
        let unit = (words.next().unwrap() >> 11) as f64 * pow2(-53);
        let scale = pow2(-1000 + (w >> 8) as i32 % 1900);
        let t = match w % 3 {
            0 => unit,
            1 => (1.0 + unit) * pow2(-(((w >> 20) % 60) as i32) - 1),
            _ => 1.0 - unit * 0.01,
        };
        let d = (1.0 + (words.next().unwrap() >> 11) as f64 * pow2(-53)) * scale;
        (t * d, d)
    })
    .filter(|&(n, d)| n > 0.0 && n <= d && n / d >= TINY)
    .take(count)
}

#[test]
fn atan2_is_odd_in_y() {
    for (n, d) in pairs(0x6174_616e_325f_6f64, 2000) {
        for x in [d, -d] {
            assert_eq!(
                atan2(-n, x).to_bits(),
                (-atan2(n, x)).to_bits(),
                "{n:e}, {x:e}"
            );
        }
    }
}

#[test]
fn the_fast_path_never_decides_against_the_accurate_path() {
    let mut undecided = 0usize;
    let count = 60_000;
    for (n, d) in pairs(0x6174_616e_325f_6661, count) {
        for form in [
            Form::Phi,
            Form::HalfPiMinus,
            Form::PiMinus,
            Form::HalfPiPlus,
        ] {
            let (y, phi) = fast(n, d, form);
            let accurate = accurate(n, d, form, phi);
            match decide_with(y, EPS) {
                Some(fast) => assert_eq!(fast.to_bits(), accurate.to_bits(), "{n:e}/{d:e}"),
                None => undecided += 1,
            }
        }
    }
    // §6: the test sends about one argument in 2^8.4 to the accurate path.
    assert!(
        undecided * 100 < count * 4,
        "{undecided} of {} reach the accurate path",
        count * 4
    );
}

#[test]
fn the_forms_meet_at_equal_magnitudes_and_the_axes() {
    // |y| = |x|: both forms give the same angle.
    for m in [1.0, 3.0, 1e-300, 1e300, f64::MIN_POSITIVE] {
        assert_eq!(atan2(m, m), QUARTER_PI_F64);
        assert_eq!(atan2(m, -m), THREE_QUARTER_PI_F64);
    }
    // A ratio below 2^-900 is a constant, or the ratio itself.
    assert_eq!(atan2(f64::from_bits(1), 1e300), 0.0);
    assert_eq!(atan2(1e300, 1e-300), HALF_PI_F64);
    assert_eq!(atan2(1e300, -1e-300), HALF_PI_F64);
    assert_eq!(atan2(1e-300, -1e300), PI_F64);
}
