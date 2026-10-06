//! Checked double-word arithmetic against an independent statement of each
//! theorem's hypotheses, decided in exact rational arithmetic, and against the
//! theorems themselves (`formal/binary64/IEEE64*.v`).
//!
//! - Every checked operation admits exactly the operands the oracle admits,
//!   with the same reason when it doesn't.
//! - An admitted result is the unchecked operation's, bit for bit, finite, a
//!   double-word number, and within its proved bound.
//! - Each boundary is tested with the representable values on either side,
//!   including a product whose rounding reaches `2^−969` while the exact
//!   product stays below it.
//! - The theorems' statements still carry the constants the checks use.

use morphiq_numerics::double_word::{CheckError, DoubleWord, Hypothesis};
use morphiq_numerics_reference::{Exact, Words};

const OUTSIDE_MAGNITUDE: CheckError = CheckError::OutsideProvenDomain(Hypothesis::Magnitude);
const OUTSIDE_UNDERFLOW: CheckError = CheckError::OutsideProvenDomain(Hypothesis::ProductUnderflow);
const OUTSIDE_RANGE: CheckError = CheckError::OutsideProvenDomain(Hypothesis::QuotientRange);

fn two(k: i64) -> Exact {
    Exact::power_of_two(k)
}

fn pow2(k: i32) -> f64 {
    f64::from_bits(u64::try_from(1023 + k).unwrap() << 52)
}

fn up(x: f64) -> f64 {
    if x >= 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

fn down(x: f64) -> f64 {
    -up(-x)
}

fn dw(hi: f64, lo: f64) -> DoubleWord {
    DoubleWord::from_parts(hi, lo).expect("a double-word number")
}

fn value(x: DoubleWord) -> Exact {
    &Exact::of(x.hi()) + &Exact::of(x.lo())
}

// The oracle: each hypothesis as the Coq statements write it, in exact
// arithmetic.

fn at_most(w: f64, k: i64) -> bool {
    Exact::of(w).abs() <= two(k)
}

/// `in_two_prod_domain a b`: `a·b = 0 ∨ 2^−969 ≤ |a·b|`.
fn in_two_prod_domain(a: f64, b: f64) -> bool {
    let p = &Exact::of(a) * &Exact::of(b);
    p.is_zero() || p.abs() >= two(-969)
}

/// `normal_or_zero (a·b)`: `a·b = 0 ∨ 2^−1022 ≤ |a·b|`.
fn normal_or_zero(a: f64, b: f64) -> bool {
    let p = &Exact::of(a) * &Exact::of(b);
    p.is_zero() || p.abs() >= two(-1022)
}

/// `in_range L H w`: `w = 0 ∨ (2^−L ≤ |w| ∧ |w| < 2^H)`.
fn in_range(l: i64, h: i64, w: f64) -> bool {
    let a = Exact::of(w).abs();
    a.is_zero() || (a >= two(-l) && a < two(h))
}

/// Some `L, H ≥ 0` with `2L + 2H ≤ 917` put every word in range: searched.
fn quotient_range(words: &[f64]) -> bool {
    (0..=458).any(|l| {
        let h = 458 - l; // the largest H for this L; in_range is monotone in H
        words.iter().all(|&w| in_range(l, h, w))
    })
}

/// `two_prod_ieee`: exponents `−537 ≤ e_a, e_b ≤ 994`, `e_a + e_b ≤ 1020`,
/// `|a| ≤ 2^e_a`, `|b| ≤ 2^e_b`: searched.
fn two_prod_magnitude(a: f64, b: f64) -> bool {
    let fits = |x: f64| (-537..=994).find(|&e| at_most(x, e));
    match (fits(a), fits(b)) {
        (Some(ea), Some(eb)) => ea + eb <= 1020,
        _ => false,
    }
}

/// The relative error test: `|computed − exact| ≤ bound·|exact|`.
fn assert_within(z: DoubleWord, exact: &Exact, bound: &Exact, context: &str) {
    assert!(
        z.hi().is_finite() && z.lo().is_finite(),
        "{context}: not finite"
    );
    assert_eq!(
        (z.hi() + z.lo()).to_bits(),
        z.hi().to_bits(),
        "{context}: not normalized"
    );
    let error = (&value(z) - exact).abs();
    assert!(
        error <= bound * &exact.abs(),
        "{context}: outside the proved bound"
    );
}

fn u2(k: i64) -> Exact {
    &Exact::integer(k) * &two(-106)
}

fn u3(k: i64) -> Exact {
    &Exact::integer(k) * &two(-159)
}

/// One result against the oracle's verdict, and, when admitted, against the
/// unchecked operation and the bound.
fn check(
    got: Result<DoubleWord, CheckError>,
    expected: Result<(), CheckError>,
    unchecked: DoubleWord,
    exact: &Exact,
    bound: &Exact,
    context: &str,
) {
    match (got, expected) {
        (Ok(z), Ok(())) => {
            assert_eq!(
                (z.hi().to_bits(), z.lo().to_bits()),
                (unchecked.hi().to_bits(), unchecked.lo().to_bits()),
                "{context}"
            );
            if exact.is_zero() {
                assert!(value(z).is_zero(), "{context}: the exact result is zero");
            } else {
                assert_within(z, exact, bound, context);
            }
        }
        (got, expected) => assert_eq!(got.map(|_| ()), expected, "{context}"),
    }
}

/// A double-word number with leading exponent `e` and a trailing word up to
/// half an ulp, sometimes zero, sometimes subnormal.
fn random_dw(words: &mut Words, e: i64) -> DoubleWord {
    let hi = words.with_exponent(e);
    let lo = match words.next_word() % 6 {
        0 => 0.0,
        _ if e - 54 < -1022 => 0.0,
        _ => {
            let k = i64::try_from(words.next_word() % 4).unwrap();
            words.with_exponent((e - 54 - k).max(-1022))
        }
    };
    DoubleWord::from_parts(hi, lo).unwrap_or_else(|| dw(hi, 0.0))
}

/// Exponents across and past every operation's domain.
fn random_exponent(words: &mut Words) -> i64 {
    match words.next_word() % 4 {
        0 => i64::try_from(words.next_word() % 2046).unwrap() - 1022,
        1 => 480 + i64::try_from(words.next_word() % 60).unwrap(),
        2 => -520 + i64::try_from(words.next_word() % 60).unwrap(),
        _ => i64::try_from(words.next_word() % 600).unwrap() - 300,
    }
}

#[test]
fn checked_operations_admit_exactly_the_theorems_hypotheses() {
    let mut words = Words::new(0x6368_6563_6b65_6401);
    for i in 0..4000 {
        let ex = random_exponent(&mut words);
        let x = random_dw(&mut words, ex);
        let ey = random_exponent(&mut words);
        let y = random_dw(&mut words, ey);
        let ef = random_exponent(&mut words);
        let f = words.with_exponent(ef);
        let (xh, xl, yh, yl) = (x.hi(), x.lo(), y.hi(), y.lo());
        let c = format!("case {i}: x = ({xh:e}, {xl:e}), y = ({yh:e}, {yl:e}), f = {f:e}");

        let exact = &value(x) + &Exact::of(f);
        let expected = if [xh, xl, f].iter().all(|&w| at_most(w, 1018)) {
            Ok(())
        } else {
            Err(OUTSIDE_MAGNITUDE)
        };
        check(
            x.checked_add_f64(f),
            expected,
            x.add_f64(f),
            &exact,
            &u2(2),
            &format!("add_f64, {c}"),
        );

        let four_words = [xh, xl, yh, yl];
        let expected = if four_words.iter().all(|&w| at_most(w, 1016)) {
            Ok(())
        } else {
            Err(OUTSIDE_MAGNITUDE)
        };
        // 3u²/(1 − 4u) < 3u² + 13u³.
        let add_bound = &u2(3) + &u3(13);
        check(
            x.checked_add(y),
            expected,
            x.add(y),
            &(&value(x) + &value(y)),
            &add_bound,
            &format!("add, {c}"),
        );
        check(
            x.checked_sub(y),
            expected,
            x.sub(y),
            &(&value(x) - &value(y)),
            &add_bound,
            &format!("sub, {c}"),
        );

        let exact = &value(x) * &Exact::of(f);
        let expected = if ![xh, xl, f].iter().all(|&w| at_most(w, 508)) {
            Err(OUTSIDE_MAGNITUDE)
        } else if !(in_two_prod_domain(xh, f) && normal_or_zero(xl, f)) {
            Err(OUTSIDE_UNDERFLOW)
        } else {
            Ok(())
        };
        let bound = &(&u2(3) * &Exact::power_of_two(-1)) + &u3(4);
        check(
            x.checked_mul_f64(f),
            expected,
            x.mul_f64(f),
            &exact,
            &bound,
            &format!("mul_f64, {c}"),
        );

        let expected = if !four_words.iter().all(|&w| at_most(w, 508)) {
            Err(OUTSIDE_MAGNITUDE)
        } else if !(in_two_prod_domain(xh, yh) && normal_or_zero(xh, yl) && normal_or_zero(xl, yh))
        {
            Err(OUTSIDE_UNDERFLOW)
        } else {
            Ok(())
        };
        check(
            x.checked_mul(y),
            expected,
            x.mul(y),
            &(&value(x) * &value(y)),
            &u2(5),
            &format!("mul, {c}"),
        );

        // Quotients: compare q·divisor with the dividend, as Exact has no division.
        let expected = if quotient_range(&[xh, xl, f]) {
            Ok(())
        } else {
            Err(OUTSIDE_RANGE)
        };
        match (x.checked_div_f64(f), expected) {
            (Ok(q), Ok(())) => {
                assert_eq!(q, x.div_f64(f), "div_f64, {c}");
                let error = (&(&value(q) * &Exact::of(f)) - &value(x)).abs();
                assert!(
                    error <= &u2(3) * &value(x).abs(),
                    "div_f64, {c}: outside the proved bound"
                );
            }
            (got, expected) => assert_eq!(got.map(|_| ()), expected, "div_f64, {c}"),
        }
        let expected = if quotient_range(&four_words) {
            Ok(())
        } else {
            Err(OUTSIDE_RANGE)
        };
        match (x.checked_div(y), expected) {
            (Ok(q), Ok(())) => {
                assert_eq!(q, x.div(y), "div, {c}");
                let error = (&(&value(q) * &value(y)) - &value(x)).abs();
                let bound = &(&u2(15) + &u3(56)) * &value(x).abs();
                assert!(error <= bound, "div, {c}: outside the proved bound");
            }
            (got, expected) => assert_eq!(got.map(|_| ()), expected, "div, {c}"),
        }

        let expected = if at_most(xh, 1020) && at_most(f, 1020) {
            Ok(())
        } else {
            Err(OUTSIDE_MAGNITUDE)
        };
        let exact = &Exact::of(xh) + &Exact::of(f);
        assert_eq!(
            DoubleWord::checked_sum(xh, f).map(|_| ()),
            expected,
            "sum, {c}"
        );
        if let Ok(s) = DoubleWord::checked_sum(xh, f) {
            assert!(
                &value(s) - &exact == Exact::integer(0),
                "sum, {c}: not exact"
            );
        }

        let expected = if !two_prod_magnitude(xh, f) {
            Err(OUTSIDE_MAGNITUDE)
        } else if !in_two_prod_domain(xh, f) {
            Err(OUTSIDE_UNDERFLOW)
        } else {
            Ok(())
        };
        assert_eq!(
            DoubleWord::checked_product(xh, f).map(|_| ()),
            expected,
            "product, {c}"
        );
        if let Ok(p) = DoubleWord::checked_product(xh, f) {
            assert!(
                &value(p) - &(&Exact::of(xh) * &Exact::of(f)) == Exact::integer(0),
                "product, {c}: not exact"
            );
        }
    }
}

#[test]
fn each_magnitude_limit_admits_its_boundary_and_rejects_the_next_value() {
    let one = dw(1.0, 0.0);
    for (k, op) in [
        (
            1018,
            (|w: f64| dw(1.0, 0.0).checked_add_f64(w)) as fn(f64) -> Result<DoubleWord, CheckError>,
        ),
        (1016, |w| dw(1.0, 0.0).checked_add(dw(w, 0.0))),
        (1016, |w| dw(1.0, 0.0).checked_sub(dw(w, 0.0))),
        (508, |w| dw(1.0, 0.0).checked_mul_f64(w)),
        (508, |w| dw(1.0, 0.0).checked_mul(dw(w, 0.0))),
        (1020, |w| DoubleWord::checked_sum(1.0, w)),
    ] {
        let edge = pow2(k);
        assert!(op(edge).is_ok() && op(-edge).is_ok(), "2^{k} is inside");
        assert_eq!(op(up(edge)), Err(OUTSIDE_MAGNITUDE), "above 2^{k}");
        assert_eq!(op(down(-edge)), Err(OUTSIDE_MAGNITUDE), "below -2^{k}");
    }
    // The trailing word counts too: (2^509, 2^455) has hi beyond 2^508.
    assert_eq!(
        one.checked_mul(dw(pow2(509), pow2(455))),
        Err(OUTSIDE_MAGNITUDE)
    );
    // product: e_a + e_b <= 1020, each at most 994.
    assert!(DoubleWord::checked_product(pow2(994), pow2(26)).is_ok());
    assert_eq!(
        DoubleWord::checked_product(pow2(994), up(pow2(26))),
        Err(OUTSIDE_MAGNITUDE)
    );
    assert_eq!(
        DoubleWord::checked_product(up(pow2(994)), 1.0),
        Err(OUTSIDE_MAGNITUDE)
    );
}

/// Significands `ma, mb` with `2^105 − 2^51 ≤ ma·mb < 2^105`: their product
/// rounds to `2^105` at 53 bits, though it is below it.
fn rounding_up_to_a_power_of_two() -> (u64, u64) {
    let target = 1u128 << 105;
    for ma in ((1u64 << 52) + 1..(1u64 << 53)).step_by(2) {
        let mb = u64::try_from((target - 1) / u128::from(ma)).unwrap();
        let p = u128::from(ma) * u128::from(mb);
        if mb >= 1 << 52 && p >= target - (1 << 51) {
            return (ma, mb);
        }
    }
    unreachable!()
}

#[test]
fn product_conditions_are_decided_exactly_at_their_boundaries() {
    let (ma, mb) = rounding_up_to_a_power_of_two();
    // a·b = ma·mb·2^(−582 − 492) = (ma·mb / 2^105)·2^−969, just below.
    #[allow(clippy::cast_precision_loss)] // 53-bit integers
    let (a, b) = (ma as f64 * pow2(-582), mb as f64 * pow2(-492));
    assert_eq!(
        a * b,
        pow2(-969),
        "the rounded product reaches the boundary"
    );
    assert!(!in_two_prod_domain(a, b), "the exact product doesn't");
    assert_eq!(DoubleWord::checked_product(a, b), Err(OUTSIDE_UNDERFLOW));
    assert_eq!(dw(a, 0.0).checked_mul_f64(b), Err(OUTSIDE_UNDERFLOW));
    assert_eq!(dw(a, 0.0).checked_mul(dw(b, 0.0)), Err(OUTSIDE_UNDERFLOW));
    // Exactly 2^-969 is inside; one encoding less is outside.
    assert!(DoubleWord::checked_product(pow2(-500), pow2(-469)).is_ok());
    assert_eq!(
        DoubleWord::checked_product(pow2(-500), down(pow2(-469))),
        Err(OUTSIDE_UNDERFLOW)
    );

    // x_lo·y against 2^-1022: x = (2^-400, 2^-454) times y = 2^-568 gives
    // x_lo·y = 2^-1022 exactly; the next smaller y gives less.
    let x = dw(pow2(-400), pow2(-454));
    assert!(x.checked_mul_f64(pow2(-568)).is_ok());
    assert_eq!(x.checked_mul_f64(down(pow2(-568))), Err(OUTSIDE_UNDERFLOW));
    assert!(x.checked_mul(dw(pow2(-568), 0.0)).is_ok());
    assert_eq!(
        x.checked_mul(dw(down(pow2(-568)), 0.0)),
        Err(OUTSIDE_UNDERFLOW)
    );
    assert_eq!(
        dw(pow2(-568), 0.0).checked_mul(dw(down(pow2(-400)), pow2(-454) * 0.5)),
        Err(OUTSIDE_UNDERFLOW)
    );
}

#[test]
fn the_quotient_range_is_decided_at_its_boundary() {
    // L = 229, H = 229: 2L + 2H = 916 <= 917.
    let top = down(pow2(229)); // below 2^229, exponent 228
    assert!(dw(pow2(-229), 0.0).checked_div_f64(top).is_ok());
    assert!(dw(top, 0.0).checked_div(dw(pow2(-229), 0.0)).is_ok());
    // 2^229 itself needs H = 230: 918.
    assert_eq!(
        dw(pow2(-229), 0.0).checked_div_f64(pow2(229)),
        Err(OUTSIDE_RANGE)
    );
    // A word below 2^-229 needs L = 230: 918.
    assert_eq!(
        dw(top, 0.0).checked_div_f64(down(pow2(-229))),
        Err(OUTSIDE_RANGE)
    );
    // Uneven splits: L = 0, H = 458.
    assert!(dw(1.0, 0.0).checked_div_f64(down(pow2(458))).is_ok());
    assert_eq!(dw(1.0, 0.0).checked_div_f64(pow2(458)), Err(OUTSIDE_RANGE));
    // Zero words impose nothing.
    assert!(dw(0.0, 0.0).checked_div_f64(down(pow2(458))).is_ok());
}

#[test]
fn zero_results_and_invalid_operands() {
    let x = dw(1.5, pow2(-60));
    for z in [
        x.checked_sub(x),
        x.checked_add(x.neg()),
        dw(-2.5, 0.0).checked_add_f64(2.5),
        x.checked_mul_f64(0.0),
        x.checked_mul(dw(0.0, 0.0)),
        dw(0.0, 0.0).checked_div_f64(3.0),
        dw(0.0, 0.0).checked_div(x),
    ] {
        let z = z.expect("an exact zero result is admitted");
        assert!(z.hi() == 0.0 && z.lo() == 0.0);
    }
    assert_eq!(x.checked_div_f64(0.0), Err(CheckError::DivisionByZero));
    assert_eq!(x.checked_div(dw(0.0, 0.0)), Err(CheckError::DivisionByZero));
    let infinite = DoubleWord::from_f64(f64::INFINITY);
    let nan = DoubleWord::from_f64(f64::NAN);
    for bad in [infinite, nan] {
        assert_eq!(bad.checked_add(x), Err(CheckError::InvalidOperand));
        assert_eq!(x.checked_mul(bad), Err(CheckError::InvalidOperand));
        assert_eq!(bad.checked_div_f64(1.0), Err(CheckError::InvalidOperand));
    }
    assert_eq!(x.checked_add_f64(f64::NAN), Err(CheckError::InvalidOperand));
    assert_eq!(
        DoubleWord::checked_product(f64::INFINITY, 1.0),
        Err(CheckError::InvalidOperand)
    );
    assert_eq!(
        DoubleWord::checked_sum(1.0, f64::NAN),
        Err(CheckError::InvalidOperand)
    );
}

/// The statement of `theorem` in `file`, from `Theorem` to `Proof.`.
fn statement<'a>(file: &'a str, theorem: &str) -> &'a str {
    let start = file.find(&format!("Theorem {theorem} ")).expect(theorem);
    let end = start + file[start..].find("Proof.").unwrap();
    &file[start..end]
}

/// The checks are bound to the theorems: if a proof's domain changes, its
/// statement no longer carries these constants and this fails.
#[test]
fn the_theorems_still_state_the_checked_hypotheses() {
    let add = include_str!("../../../formal/binary64/IEEE64Add.v");
    let mul = include_str!("../../../formal/binary64/IEEE64Mul.v");
    let div = include_str!("../../../formal/binary64/IEEE64Div.v");
    let eft = include_str!("../../../formal/binary64/IEEE64Eft.v");
    let binary64_mul = include_str!("../../../formal/binary64/Binary64Mul.v");
    let binary64_div = include_str!("../../../formal/binary64/Binary64Div.v");
    for (file, theorem, needles) in [
        (add, "add_f64_ieee", &["bpow radix2 1018"][..]),
        (add, "add_ieee", &["bpow radix2 1016", "<> 0"][..]),
        (add, "sub_ieee", &["bpow radix2 1016", "<> 0"][..]),
        (
            mul,
            "mul_f64_ieee",
            &[
                "bpow radix2 508",
                "in_two_prod_domain (B xh) (B y)",
                "normal_or_zero (B xl * B y)",
            ][..],
        ),
        (
            mul,
            "mul_ieee",
            &[
                "bpow radix2 508",
                "in_two_prod_domain (B xh) (B yh)",
                "normal_or_zero (B xh * B yl)",
                "normal_or_zero (B xl * B yh)",
            ][..],
        ),
        (
            div,
            "div_f64_ieee",
            &[
                "2 * L + 2 * H <= 917",
                "B y <> 0",
                "in_range L H (B xh)",
                "in_range L H (B xl)",
                "in_range L H (B y)",
            ][..],
        ),
        (
            div,
            "div_ieee",
            &["2 * L + 2 * H <= 917", "B yh <> 0", "in_range L H (B yl)"][..],
        ),
        (eft, "two_sum_ieee", &["bpow radix2 1020"][..]),
        (
            eft,
            "two_prod_ieee",
            &[
                "-537 <= Ea <= 994",
                "Ea + Eb <= 1020",
                "in_two_prod_domain (B a) (B b)",
            ][..],
        ),
    ] {
        let s = statement(file, theorem);
        for needle in needles {
            assert!(s.contains(needle), "{theorem} no longer states `{needle}`");
        }
    }
    assert!(binary64_mul.contains("a * b = 0 \\/ bpow radix2 (-969) <= Rabs (a * b)."));
    assert!(binary64_mul.contains("z = 0 \\/ bpow radix2 (-1022) <= Rabs z."));
    assert!(
        binary64_div
            .contains("w = 0 \\/ (bpow radix2 (- L) <= Rabs w /\\ Rabs w < bpow radix2 H).")
    );
}
