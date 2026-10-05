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

/// `|computed - exact| · denominator ≤ bound · |exact|`: the relative error
/// test against `bound / denominator`, with the denominator cleared.
fn assert_within(
    computed: &Exact,
    exact: &Exact,
    bound: &Exact,
    denominator: &Exact,
    context: &str,
) {
    let error = (computed - exact).abs();
    assert!(
        &error * denominator <= bound * &exact.abs(),
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

/// A double-word number whose leading word has exponent `e` near the bottom
/// of the range (`-1022 ≤ e ≤ -970`), so its trailing word, below half an
/// ulp of the leading one, is subnormal or zero.
fn subnormal_tailed(words: &mut Words, e: i64) -> DoubleWord {
    let hi = words.with_exponent(e);
    // Half an ulp of `hi` is `2^(e - 53)`, which is `2^(e + 1021)` subnormal
    // steps; at `e = -1022` it is below the least subnormal, so `lo` is zero.
    let below = 1_u64 << u32::try_from((e + 1021).max(0)).unwrap();
    let lo = f64::from_bits(words.next_word() % below);
    let lo = if words.next_word().is_multiple_of(2) {
        lo
    } else {
        -lo
    };
    DoubleWord::from_parts(hi, lo).expect("a trailing word below half an ulp")
}

/// The additive operations at the bottom of the range, where their trailing
/// words and intermediates are subnormal and sums cancel into the subnormal
/// range. Their bounds are proved there with gradual underflow
/// (`formal/binary64/Binary64Add.v`); the theorems exclude a zero sum.
#[test]
fn additive_operations_keep_their_bounds_with_subnormal_words() {
    let mut words = Words::new(0x05ab_0b0e_5ab0_b0e5);
    let add_f64_bound = &u(2) + &u(2);
    let add_bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(13) * &u(3));
    for _ in 0..SAMPLES {
        let e = -1022 + i64::try_from(words.next_word() % 53).unwrap();
        let x = subnormal_tailed(&mut words, e);
        let near = subnormal_tailed(&mut words, e);
        // Opposite leading words of equal exponent cancel into the subnormal
        // range; a subnormal y exercises a subnormal operand directly.
        let opposite = DoubleWord::from_parts(-near.hi().copysign(x.hi()), near.lo())
            .expect("negating the leading word keeps a double-word number");
        let y = if words.next_word().is_multiple_of(2) {
            -near.hi().copysign(x.hi())
        } else {
            f64::from_bits(words.next_word() % (1 << 52))
        };
        let sum = &value(x) + &Exact::of(y);
        if sum != Exact::integer(0) {
            let z = x.add_f64(y);
            assert_normalized(z, "add_f64");
            assert_within(
                &value(z),
                &sum,
                &add_f64_bound,
                &Exact::integer(1),
                "add_f64",
            );
        }
        for (z, exact) in [
            (x.add(opposite), &value(x) + &value(opposite)),
            (x.sub(near), &value(x) - &value(near)),
        ] {
            if exact != Exact::integer(0) {
                assert_normalized(z, "add");
                assert_within(&value(z), &exact, &add_bound, &Exact::integer(1), "add");
            }
        }
    }
}

/// The additive operations at the top of their domain, every word at most
/// `2^1018` for `add_f64` and `2^1016` for `add` and `sub`: no operation
/// overflows (`formal/binary64/IEEE64Add.v`), so every result is finite and
/// within its bound.
#[test]
fn additive_operations_keep_their_bounds_at_the_overflow_edge() {
    let mut words = Words::new(0x0ed6_e00e_d6e0_0001);
    let add_f64_bound = &u(2) + &u(2);
    let add_bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(13) * &u(3));
    for _ in 0..SAMPLES {
        let k = i64::try_from(words.next_word() % 4).unwrap();
        let x = double_word(&mut words, 1017);
        let f = words.with_exponent(1017 - k);
        let a = double_word(&mut words, 1015);
        let b = double_word(&mut words, 1015 - k);
        for (z, exact, bound, name) in [
            (
                x.add_f64(f),
                &value(x) + &Exact::of(f),
                &add_f64_bound,
                "add_f64",
            ),
            (a.add(b), &value(a) + &value(b), &add_bound, "add"),
            (a.sub(b), &value(a) - &value(b), &add_bound, "sub"),
        ] {
            assert!(
                z.hi().is_finite() && z.lo().is_finite(),
                "{name} overflowed"
            );
            if exact != Exact::integer(0) {
                assert_normalized(z, name);
                assert_within(&value(z), &exact, bound, &Exact::integer(1), name);
            }
        }
    }
}

/// The products at the top of their domain, every word below `2^508`: no
/// operation overflows (`formal/binary64/IEEE64Mul.v`).
#[test]
fn multiplicative_operations_keep_their_bounds_at_the_overflow_edge() {
    let mut words = Words::new(0x0508_0508_0508_0508);
    // 1.5u² + 4u³ with its denominator 2 cleared, and 5u²/(1 + u)².
    let mul_f64_bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(8) * &u(3));
    let mul_bound = &Exact::integer(5) * &u(2);
    let one_plus_u = &Exact::integer(1) + &u(1);
    let mul_denominator = &one_plus_u * &one_plus_u;
    for _ in 0..SAMPLES {
        let k = i64::try_from(words.next_word() % 4).unwrap();
        let x = double_word(&mut words, 507);
        let y = double_word(&mut words, 507 - k);
        let f = y.hi();
        let z = x.mul_f64(f);
        assert!(
            z.hi().is_finite() && z.lo().is_finite(),
            "mul_f64 overflowed"
        );
        assert_normalized(z, "mul_f64");
        assert_within(
            &value(z),
            &(&value(x) * &Exact::of(f)),
            &mul_f64_bound,
            &Exact::integer(2),
            "mul_f64",
        );
        let z = x.mul(y);
        assert!(z.hi().is_finite() && z.lo().is_finite(), "mul overflowed");
        assert_normalized(z, "mul");
        assert_within(
            &value(z),
            &(&value(x) * &value(y)),
            &mul_bound,
            &mul_denominator,
            "mul",
        );
    }
}

/// The multiplicative operations at the bottom of their binary64 domain
/// (`formal/binary64/Binary64Mul.v`): leading-word products from `2^-969`
/// (`two_prod`'s domain) and trailing-word products from `2^-1022`.
///
/// `double_word` draws a trailing word with exponent `e - 54 - k`, `k < 4`, so
/// a leading exponent sum of at least `-965` puts every trailing-word product
/// at `2^-1022` or above; the `-969` edge is checked with zero trailing words.
#[test]
fn multiplicative_operations_keep_their_bounds_at_the_bottom_of_their_domain() {
    let mut words = Words::new(0x0b07_7041_d0a1_0b07);
    // 1.5u² + 4u³ with its denominator 2 cleared, and 5u²/(1 + u)².
    let mul_f64_bound = &(&Exact::integer(3) * &u(2)) + &(&Exact::integer(8) * &u(3));
    let mul_bound = &Exact::integer(5) * &u(2);
    let one_plus_u = &Exact::integer(1) + &u(1);
    let mul_denominator = &one_plus_u * &one_plus_u;
    for _ in 0..SAMPLES {
        let ex = -600 + i64::try_from(words.next_word() % 200).unwrap();
        let edge = words.next_word().is_multiple_of(16);
        let sum = if edge {
            -969
        } else {
            -965 + i64::try_from(words.next_word() % 66).unwrap()
        };
        let ey = sum - ex;
        let (x, y) = if edge {
            let hi = words.with_exponent(ex);
            let other = words.with_exponent(ey);
            (
                DoubleWord::from_parts(hi, 0.0).unwrap(),
                DoubleWord::from_parts(other, 0.0).unwrap(),
            )
        } else {
            (double_word(&mut words, ex), double_word(&mut words, ey))
        };
        let f = y.hi();
        let z = x.mul_f64(f);
        assert_normalized(z, "mul_f64");
        assert_within(
            &value(z),
            &(&value(x) * &Exact::of(f)),
            &mul_f64_bound,
            &Exact::integer(2),
            "mul_f64",
        );
        let z = x.mul(y);
        assert_normalized(z, "mul");
        assert_within(
            &value(z),
            &(&value(x) * &value(y)),
            &mul_bound,
            &mul_denominator,
            "mul",
        );
    }
}

/// A double-word number whose words are zero or have exponents in
/// `[low, high]`: the leading word's exponent is drawn from that range, and
/// a trailing word that would fall below `2^low` is zero.
fn ranged_double_word(words: &mut Words, low: i64, high: i64) -> DoubleWord {
    let span = u64::try_from(high - low + 1).unwrap();
    let e = low + i64::try_from(words.next_word() % span).unwrap();
    if e - 57 >= low {
        double_word(words, e)
    } else {
        DoubleWord::from_parts(words.with_exponent(e), 0.0).unwrap()
    }
}

/// The divisions across their binary64 domain (`formal/binary64/Binary64Div.v`):
/// for `L, H ≥ 0` with `2L + 2H ≤ 917`, every nonzero word `w` of `x` and `y`
/// has `2^-L ≤ |w| < 2^H`. Each corner of that region is sampled.
#[test]
fn divisions_keep_their_bounds_across_their_binary64_domain() {
    let mut words = Words::new(0x0d17_1d00_0d17_1d00);
    let div_f64_bound = &Exact::integer(3) * &u(2);
    let div_bound = &(&Exact::integer(15) * &u(2)) + &(&Exact::integer(56) * &u(3));
    for (l, h) in [(458, 0), (229, 229), (0, 458)] {
        for _ in 0..SAMPLES / 3 {
            // Exponents in [-L, H - 1] give 2^-L ≤ |w| < 2^H.
            let x = ranged_double_word(&mut words, -l, h - 1);
            let y = ranged_double_word(&mut words, -l, h - 1);
            let f = y.hi();
            let z = x.div_f64(f);
            assert_normalized(z, "div_f64");
            // |z - x/y| ≤ B|x/y|  ⇔  |z·y - x| ≤ B|x|, since y ≠ 0.
            let residual = (&(&value(z) * &Exact::of(f)) - &value(x)).abs();
            assert!(residual <= &div_f64_bound * &value(x).abs(), "div_f64");
            let z = x.div(y);
            assert_normalized(z, "div");
            let residual = (&(&value(z) * &value(y)) - &value(x)).abs();
            assert!(residual <= &div_bound * &value(x).abs(), "div");
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
