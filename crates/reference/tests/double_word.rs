//! Double-word arithmetic against its proved relative error bounds, decided
//! in exact integer arithmetic.

use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics_reference::{Exact, Words};

/// `u = 2^-53`, the unit roundoff, to the power `k`.
fn u(k: i64) -> Exact {
    Exact::power_of_two(-53 * k)
}

fn value(x: DoubleWord) -> Exact {
    &Exact::of(x.hi()) + &Exact::of(x.lo())
}

/// `hi = RN(hi + lo)`: the result is a double-word number.
fn assert_normalized(z: DoubleWord, context: &str) {
    assert_eq!(
        (z.hi() + z.lo()).to_bits(),
        z.hi().to_bits(),
        "{context}: ({:e}, {:e}) is not a double-word number",
        z.hi(),
        z.lo()
    );
}

/// `|computed - exact| · denominator ≤ bound · |exact| · denominator`, the
/// relative error test with the bound's denominator cleared.
fn assert_within(
    computed: &Exact,
    exact: &Exact,
    bound: &Exact,
    denominator: &Exact,
    context: &str,
) {
    let error = (computed - exact).abs();
    assert!(
        &error * denominator <= &(bound * &exact.abs()) * denominator,
        "{context}: relative error exceeds the proved bound"
    );
}

/// A double-word number with a random leading word of exponent `e` and a
/// random trailing word no larger than half its unit in the last place.
fn double_word(words: &mut Words, e: i64) -> DoubleWord {
    let hi = words.with_exponent(e);
    let lo = if words.next_word().is_multiple_of(8) {
        0.0
    } else {
        {
            let k = i64::try_from(words.next_word() % 4).unwrap();
            words.with_exponent(e - 54 - k)
        }
    };
    DoubleWord::from_parts(hi, lo).expect("a trailing word below half an ulp")
}

fn exponent(words: &mut Words) -> i64 {
    i64::try_from(words.next_word() % 400).unwrap() - 200
}

const SAMPLES: usize = 100_000;

#[test]
fn add_f64_is_within_two_u_squared() {
    let mut words = Words::new(0x1234_5678_9abc_def1);
    let bound = &u(2) + &u(2);
    for _ in 0..SAMPLES {
        let e = exponent(&mut words);
        let x = double_word(&mut words, e);
        let y = {
            let k = i64::try_from(words.next_word() % 8).unwrap();
            words.with_exponent(e - k)
        };
        let z = x.add_f64(y);
        assert_normalized(z, "add_f64");
        assert_within(
            &value(z),
            &(&value(x) + &Exact::of(y)),
            &bound,
            &Exact::integer(1),
            "add_f64",
        );
    }
}

#[test]
fn add_is_within_three_u_squared_plus_thirteen_u_cubed() {
    let mut words = Words::new(0x0fed_cba9_8765_4321);
    let bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(13) * &u(3));
    for _ in 0..SAMPLES {
        let e = exponent(&mut words);
        let x = double_word(&mut words, e);
        let y = {
            let k = i64::try_from(words.next_word() % 8).unwrap();
            double_word(&mut words, e - k)
        };
        for (a, b) in [(x, y), (x, y.neg())] {
            let z = a.add(b);
            assert_normalized(z, "add");
            assert_within(
                &value(z),
                &(&value(a) + &value(b)),
                &bound,
                &Exact::integer(1),
                "add",
            );
        }
    }
}

#[test]
fn mul_f64_is_within_one_and_a_half_u_squared_plus_four_u_cubed() {
    let mut words = Words::new(0x5555_aaaa_3333_cccc);
    // 1.5u² + 4u³, scaled by 2 to stay integral: 3u² + 8u³ against 2|exact|.
    let bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(8) * &u(3));
    for _ in 0..SAMPLES {
        let x = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let y = {
            let e = exponent(&mut words);
            words.with_exponent(e)
        };
        let z = x.mul_f64(y);
        assert_normalized(z, "mul_f64");
        let exact = &value(x) * &Exact::of(y);
        let error = (&value(z) - &exact).abs();
        assert!(
            &error * &Exact::integer(2) <= &bound * &exact.abs(),
            "mul_f64"
        );
    }
}

#[test]
fn mul_is_within_five_u_squared_over_one_plus_u_squared() {
    let mut words = Words::new(0x0123_4567_89ab_cdef);
    let bound = &Exact::integer(5) * &u(2);
    let one_plus_u = &Exact::integer(1) + &u(1);
    let denominator = &one_plus_u * &one_plus_u;
    for _ in 0..SAMPLES {
        let x = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let y = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let z = x.mul(y);
        assert_normalized(z, "mul");
        assert_within(
            &value(z),
            &(&value(x) * &value(y)),
            &bound,
            &denominator,
            "mul",
        );
    }
}

#[test]
fn div_f64_is_within_three_u_squared() {
    let mut words = Words::new(0xfeed_face_cafe_beef);
    let bound = &Exact::integer(3) * &u(2);
    for _ in 0..SAMPLES {
        let x = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let y = {
            let e = exponent(&mut words);
            words.with_exponent(e)
        };
        let z = x.div_f64(y);
        assert_normalized(z, "div_f64");
        // |z - x/y| ≤ B|x/y|  ⇔  |z·y - x| ≤ B|x|, since y ≠ 0.
        let residual = (&(&value(z) * &Exact::of(y)) - &value(x)).abs();
        assert!(residual <= &bound * &value(x).abs(), "div_f64");
    }
}

#[test]
fn div_is_within_fifteen_u_squared_plus_fifty_six_u_cubed() {
    let mut words = Words::new(0xa5a5_5a5a_c3c3_3c3c);
    let bound = &(&Exact::integer(15) * &u(2)) + &(&Exact::integer(56) * &u(3));
    for _ in 0..SAMPLES {
        let x = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let y = {
            let e = exponent(&mut words);
            double_word(&mut words, e)
        };
        let z = x.div(y);
        assert_normalized(z, "div");
        let residual = (&(&value(z) * &value(y)) - &value(x)).abs();
        assert!(residual <= &bound * &value(x).abs(), "div");
    }
}

#[test]
fn add_f64_attains_its_bound_on_the_published_worst_case() {
    // Joldes, Muller and Popescu 2017, after Theorem 2.2: x_h = 1,
    // x_l = (2^53 - 1)·2^-106, y = -(1 - 2^-53)/2, with relative error
    // 2u²/(1 + 3u - 2u²) = 2u² - 6u³ + ….
    let x = DoubleWord::from_parts(
        1.0,
        9_007_199_254_740_991.0 * f64::from_bits((1023 - 106) << 52),
    )
    .expect("a double-word number");
    let y = -(1.0 - f64::from_bits((1023 - 53) << 52)) / 2.0;
    let z = x.add_f64(y);
    let exact = &value(x) + &Exact::of(y);
    let error = (&value(z) - &exact).abs();
    // Above 1.99u² and within 2u².
    assert!(&error * &Exact::integer(100) > &(&Exact::integer(199) * &u(2)) * &exact.abs());
    assert!(error <= &(&Exact::integer(2) * &u(2)) * &exact.abs());
}

#[test]
fn add_attains_its_bound_on_the_published_worst_case() {
    // Muller and Rideau 2022, Property 2.1: x = (1, u - u²),
    // y = (-1/2 + u/2, -u²/2 + u³), with relative error
    // (3u² - 2u³)/(1 + 3u - 3u² + 2u³) = 3u² - 11u³ + ….
    let u1 = f64::from_bits((1023 - 53) << 52);
    let u2 = f64::from_bits((1023 - 106) << 52);
    let u3 = f64::from_bits((1023 - 159) << 52);
    let x = DoubleWord::from_parts(1.0, u1 - u2).expect("a double-word number");
    let y = DoubleWord::from_parts(-0.5 + u1 / 2.0, -u2 / 2.0 + u3).expect("a double-word number");
    let z = x.add(y);
    let exact = &value(x) + &value(y);
    let error = (&value(z) - &exact).abs();
    // Above 2.99u², which no random sample approaches.
    assert!(&error * &Exact::integer(100) > &(&Exact::integer(299) * &u(2)) * &exact.abs());
}

#[test]
fn from_parts_admits_only_double_word_numbers() {
    let half_ulp = f64::from_bits((1023 - 53) << 52);
    assert!(DoubleWord::from_parts(1.0, half_ulp).is_some());
    // 1 + ulp(1) rounds away from 1.
    assert!(DoubleWord::from_parts(1.0, 2.0 * half_ulp).is_none());
    assert!(DoubleWord::from_parts(f64::INFINITY, 0.0).is_none());
    assert!(DoubleWord::from_parts(1.0, f64::NAN).is_none());
}

#[test]
fn sum_product_and_negation_are_exact() {
    let mut words = Words::new(0x3c6e_f372_fe94_f82b);
    for _ in 0..10_000 {
        let (a, b) = (
            {
                let e = exponent(&mut words);
                words.with_exponent(e)
            },
            {
                let e = exponent(&mut words);
                words.with_exponent(e)
            },
        );
        assert_eq!(value(DoubleWord::sum(a, b)), &Exact::of(a) + &Exact::of(b));
        assert_eq!(
            value(DoubleWord::product(a, b)),
            &Exact::of(a) * &Exact::of(b)
        );
        let x = DoubleWord::sum(a, b);
        assert_eq!(value(x.neg()), -&value(x));
        assert_eq!(value(x.sub(x)), Exact::integer(0));
    }
}
