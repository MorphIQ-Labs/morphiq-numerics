//! The error-free transforms against exact integer arithmetic.

use morphiq_numerics::eft::{fast_two_sum, two_prod, two_sum};
use morphiq_numerics_reference::{Exact, Words};

fn assert_exact_sum(a: f64, b: f64, (s, t): (f64, f64)) {
    assert_eq!(s.to_bits(), (a + b).to_bits(), "s = RN({a:e} + {b:e})");
    assert_eq!(
        &Exact::of(s) + &Exact::of(t),
        &Exact::of(a) + &Exact::of(b),
        "{s:e} + {t:e} != {a:e} + {b:e}"
    );
}

fn assert_exact_product(a: f64, b: f64) {
    let (p, e) = two_prod(a, b);
    assert_eq!(p.to_bits(), (a * b).to_bits(), "p = RN({a:e} · {b:e})");
    assert_eq!(
        &Exact::of(p) + &Exact::of(e),
        &Exact::of(a) * &Exact::of(b),
        "{p:e} + {e:e} != {a:e} · {b:e}"
    );
}

#[test]
fn two_sum_is_exact_for_operands_of_any_relative_size() {
    let mut words = Words::new(0x2545_f491_4f6c_dd1d);
    for _ in 0..200_000 {
        let ea = i64::try_from(words.next_word() % 1200).unwrap() - 600;
        let eb = ea - i64::try_from(words.next_word() % 120).unwrap() + 60;
        let (a, b) = (words.with_exponent(ea), words.with_exponent(eb));
        assert_exact_sum(a, b, two_sum(a, b));
        assert_exact_sum(b, a, two_sum(b, a));
    }
}

#[test]
fn two_sum_is_exact_in_the_subnormal_range_and_at_zero() {
    let tiny = f64::from_bits(1);
    for (a, b) in [
        (tiny, -tiny),
        (f64::MIN_POSITIVE, -tiny),
        (f64::from_bits(0x000f_ffff_ffff_ffff), tiny),
        (0.0, -0.0),
        (1.0, -1.0),
    ] {
        assert_exact_sum(a, b, two_sum(a, b));
    }
}

#[test]
fn fast_two_sum_is_exact_when_the_first_operand_dominates() {
    let mut words = Words::new(0x9e37_79b9_7f4a_7c15);
    for _ in 0..200_000 {
        let ea = i64::try_from(words.next_word() % 1200).unwrap() - 600;
        let eb = ea - i64::try_from(words.next_word() % 60).unwrap();
        let (a, b) = (words.with_exponent(ea), words.with_exponent(eb));
        assert_exact_sum(a, b, fast_two_sum(a, b));
    }
}

#[test]
fn two_prod_is_exact_across_its_domain() {
    let mut words = Words::new(0xd1b5_4a32_d192_ed03);
    let mut checked = 0;
    while checked < 200_000 {
        let ea = i64::try_from(words.next_word() % 2018).unwrap() - 1022;
        let eb = i64::try_from(words.next_word() % 2018).unwrap() - 1022;
        if !(-969..=1021).contains(&(ea + eb)) {
            continue;
        }
        assert_exact_product(words.with_exponent(ea), words.with_exponent(eb));
        checked += 1;
    }
}

#[test]
fn two_prod_is_exact_at_the_edges_of_its_domain() {
    let mut words = Words::new(0x6a09_e667_f3bc_c909);
    // e_a + e_b at both ends of the proved domain, with the largest and smallest
    // significands.
    for (ea, eb) in [
        (-1022, 53),
        (53, -1022),
        (-485, -484),
        (995, 26),
        (510, 511),
    ] {
        let all_ones =
            |e: i64| f64::from_bits(u64::try_from(e + 1023).unwrap() << 52 | ((1 << 52) - 1));
        let power = |e: i64| f64::from_bits(u64::try_from(e + 1023).unwrap() << 52);
        for (a, b) in [
            (all_ones(ea), all_ones(eb)),
            (power(ea), all_ones(eb)),
            (-all_ones(ea), power(eb)),
            (words.with_exponent(ea), words.with_exponent(eb)),
        ] {
            assert_exact_product(a, b);
        }
    }
    // The splitting's largest admissible magnitude.
    let limit = f64::from_bits((996 + 1023) << 52);
    assert_exact_product(limit, 0.75);
    assert_exact_product(-limit, f64::from_bits((25 + 1023) << 52 | ((1 << 52) - 1)));
    // Subnormal operands, which the proved domain admits.
    let subnormal = f64::from_bits(0x0000_0000_0123_4567);
    assert_exact_product(subnormal, f64::from_bits((100 + 1023) << 52) * 1.75);
    assert_exact_product(-f64::from_bits(1), f64::from_bits((994 + 1023) << 52));
    assert_exact_product(0.0, -3.5);
    assert_exact_product(-0.0, 0.0);
}

#[test]
fn two_prod_reproduces_the_exact_square_of_a_split_tie() {
    // 1 + 2^-26 + 2^-52: its square needs the head and tail cross terms.
    let x = 1.0 + f64::from_bits((1023 - 26) << 52) + f64::from_bits((1023 - 52) << 52);
    assert_exact_product(x, x);
    assert_exact_product(x, -x);
}

#[test]
fn every_check_sees_an_inexact_sum_or_product() {
    // Guards the oracle: each check above must be able to fail.
    let (a, b) = (1.0, f64::from_bits((1023 - 60) << 52));
    let (s, t) = two_sum(a, b);
    assert_ne!(t, 0.0);
    assert_ne!(Exact::of(s), &Exact::of(a) + &Exact::of(b));
    let (p, e) = two_prod(0.1, 0.3);
    assert_ne!(e, 0.0);
    assert_ne!(Exact::of(p), &Exact::of(0.1) * &Exact::of(0.3));
}
