//! Error-free transforms, ULP utilities and double-word arithmetic against
//! exact MPFR values and the contracts in docs/ulp.md and docs/double-word.md.
//!
//! [`WIDE`] bits hold every sum and product of up to four binary64 values
//! exactly, so quotient bounds are checked by multiplying through.
use morphiq_numerics::double_word::DoubleWord;
use morphiq_numerics::{eft, ulp};
use rug::{Float, float::Round};

/// Exceeds the span of binary64 products (2^-2148 to 2^2048).
const WIDE: u32 = 4400;

fn exact(x: f64) -> Float {
    Float::with_val(WIDE, x)
}

fn power(k: i32) -> Float {
    let one = Float::with_val(WIDE, 1);
    if k >= 0 {
        one << k as u32
    } else {
        one >> k.unsigned_abs()
    }
}

fn add(a: &Float, b: &Float) -> Float {
    let (sum, order) = Float::with_val_round(WIDE, a + b, Round::Nearest);
    assert_eq!(order, std::cmp::Ordering::Equal, "inexact oracle sum");
    sum
}

fn mul(a: &Float, b: &Float) -> Float {
    let (product, order) = Float::with_val_round(WIDE, a * b, Round::Nearest);
    assert_eq!(order, std::cmp::Ordering::Equal, "inexact oracle product");
    product
}

fn magnitude(x: &Float) -> Float {
    x.clone().abs()
}

fn at_most(x: f64, k: i32) -> bool {
    magnitude(&exact(x)) <= power(k)
}

/// `x` is `RN(value)`; the sign of an exact zero is not compared.
fn rounds_to(x: f64, value: &Float) -> bool {
    let rounded = value.to_f64_round(Round::Nearest);
    x == rounded && (x == 0.0 || x.to_bits() == rounded.to_bits())
}

fn check_transforms(a: f64, b: f64) {
    if !a.is_finite() || !b.is_finite() {
        return;
    }
    let sum = add(&exact(a), &exact(b));
    if at_most(a, 1020) && at_most(b, 1020) {
        let (s, t) = eft::two_sum(a, b);
        assert!(rounds_to(s, &sum), "two_sum head {a:e} {b:e}");
        assert_eq!(add(&exact(s), &exact(t)), sum, "two_sum {a:e} {b:e}");
    }
    let ordered = a == 0.0
        || magnitude(&exact(a)) >= magnitude(&exact(b))
        || (b != 0.0 && exact(a).get_exp() >= exact(b).get_exp());
    if ordered && at_most(a, 1021) && at_most(b, 1021) {
        let (s, t) = eft::fast_two_sum(a, b);
        assert!(rounds_to(s, &sum), "fast_two_sum head {a:e} {b:e}");
        assert_eq!(add(&exact(s), &exact(t)), sum, "fast_two_sum {a:e} {b:e}");
    }
    if product_domain(a, b) {
        let product = mul(&exact(a), &exact(b));
        let (p, e) = eft::two_prod(a, b);
        assert!(rounds_to(p, &product), "two_prod head {a:e} {b:e}");
        assert_eq!(add(&exact(p), &exact(e)), product, "two_prod {a:e} {b:e}");
    }
}

/// The least `e` with `|x| <= 2^e`; any exponent bounds zero.
fn bounding_exponent(x: f64) -> i32 {
    if x == 0.0 {
        return -1074;
    }
    let m = magnitude(&exact(x));
    let e = m.get_exp().expect("finite nonzero");
    // MPFR's exponent satisfies 2^(e-1) <= m < 2^e.
    if m == power(e - 1) { e - 1 } else { e }
}

fn zero_or_at_least(a: f64, b: f64, k: i32) -> bool {
    let p = mul(&exact(a), &exact(b));
    p.is_zero() || magnitude(&p) >= power(k)
}

fn product_domain(a: f64, b: f64) -> bool {
    let (ea, eb) = (bounding_exponent(a), bounding_exponent(b));
    ea <= 994 && eb <= 994 && ea + eb <= 1020 && zero_or_at_least(a, b, -969)
}

fn check_ulp(a: f64, b: f64) {
    let u = ulp::ulp(a);
    if a.is_nan() {
        assert_eq!(u.to_bits(), a.to_bits());
    } else if a.is_infinite() {
        assert_eq!(u, f64::INFINITY);
    } else {
        let e = if a == 0.0 {
            -1022
        } else {
            (exact(a).get_exp().expect("finite nonzero") - 1).max(-1022)
        };
        assert_eq!(exact(u), power(e - 52), "ulp {:016x}", a.to_bits());
    }
    let position = ulp::ordered_bits(a);
    assert_eq!(ulp::ordered_bits(-a), -position);
    if a == 0.0 {
        assert_eq!(position, 0);
    }
    if !a.is_nan() && a != f64::INFINITY {
        assert_eq!(ulp::ordered_bits(a.next_up()), position + 1);
    }
    let between = ulp::ulps_between(a, b);
    if a.is_nan() || b.is_nan() {
        assert_eq!(between, None);
    } else {
        assert_eq!(
            between.map(i128::from),
            Some((i128::from(ulp::ordered_bits(b)) - i128::from(position)).abs())
        );
    }
}

fn words(x: DoubleWord) -> [u64; 2] {
    [x.hi().to_bits(), x.lo().to_bits()]
}

fn value(x: DoubleWord) -> Float {
    add(&exact(x.hi()), &exact(x.lo()))
}

fn valid(x: DoubleWord) -> bool {
    x.hi().is_finite() && x.lo().is_finite() && rounds_to(x.hi(), &value(x))
}

/// A relative bound `(half_u2 / 2) u^2 + u3 u^3`, with `u = 2^-53`.
#[derive(Clone, Copy)]
struct Relative {
    half_u2: u32,
    u3: u32,
}

impl Relative {
    /// `error <= bound * scale`, all exact.
    fn admits(self, error: &Float, scale: &Float) -> bool {
        let quadratic = mul(&power(-107), &Float::with_val(WIDE, self.half_u2));
        let cubic = mul(&power(-159), &Float::with_val(WIDE, self.u3));
        magnitude(error) <= mul(&add(&quadratic, &cubic), &magnitude(scale))
    }
}

/// The checked result must exist exactly when `admitted`, repeat the unchecked
/// result bit for bit, be a double word and meet `bound` on `residual / scale`.
fn check_operation(
    name: &str,
    checked: Option<DoubleWord>,
    unchecked: impl Fn() -> DoubleWord,
    admitted: bool,
    bound: Relative,
    residual: impl Fn(&Float) -> (Float, Float),
) {
    assert_eq!(checked.is_some(), admitted, "{name}: admission");
    let Some(z) = checked else { return };
    assert_eq!(words(z), words(unchecked()), "{name}: unchecked differs");
    assert!(valid(z), "{name}: not a double word");
    let (error, scale) = residual(&value(z));
    assert!(
        bound.admits(&error, &scale),
        "{name}: bound violation, result {:?}",
        words(z)
    );
}

/// Some L, H >= 0 with 2L + 2H <= 917 hold every nonzero word in
/// [2^-L, 2^H): the least L and H decide it.
fn quotient_range(all: &[f64]) -> bool {
    let (mut l, mut h) = (0, 0);
    for &w in all.iter().filter(|w| **w != 0.0) {
        let e = exact(w).get_exp().expect("finite nonzero");
        l = l.max(1 - e);
        h = h.max(e);
    }
    2 * l + 2 * h <= 917
}

fn check_scalar_operations(x: DoubleWord, y: f64) {
    let usable = valid(x) && y.is_finite();
    let (xv, yv) = if usable {
        (value(x), exact(y))
    } else {
        (exact(0.0), exact(0.0))
    };
    let within = |k| usable && [x.hi(), x.lo(), y].iter().all(|&w| at_most(w, k));
    // A zero exact result is admitted only when the operation returns zero.
    let zero_ok = |exact_zero: bool, z: DoubleWord| !exact_zero || (z.hi() == 0.0 && z.lo() == 0.0);

    let sum = if usable { add(&xv, &yv) } else { exact(0.0) };
    check_operation(
        "add_f64",
        x.checked_add_f64(y).ok(),
        || x.add_f64(y),
        within(1018) && zero_ok(sum.is_zero(), x.add_f64(y)),
        Relative { half_u2: 4, u3: 0 },
        |z| (add(z, &-sum.clone()), sum.clone()),
    );
    let product = if usable { mul(&xv, &yv) } else { exact(0.0) };
    check_operation(
        "mul_f64",
        x.checked_mul_f64(y).ok(),
        || x.mul_f64(y),
        within(508)
            && zero_or_at_least(x.hi(), y, -969)
            && zero_or_at_least(x.lo(), y, -1022)
            && zero_ok(x.hi() == 0.0 || y == 0.0, x.mul_f64(y)),
        Relative { half_u2: 3, u3: 4 },
        |z| (add(z, &-product.clone()), product.clone()),
    );
    check_operation(
        "div_f64",
        x.checked_div_f64(y).ok(),
        || x.div_f64(y),
        usable
            && y != 0.0
            && quotient_range(&[x.hi(), x.lo(), y])
            && zero_ok(x.hi() == 0.0, x.div_f64(y)),
        Relative { half_u2: 6, u3: 0 },
        // |z - x/y| <= r |x/y| is |z y - x| <= r |x|.
        |z| (add(&mul(z, &yv), &-xv.clone()), xv.clone()),
    );
}

fn check_pair_operations(x: DoubleWord, y: DoubleWord) {
    let usable = valid(x) && valid(y);
    let (xv, yv) = if usable {
        (value(x), value(y))
    } else {
        (exact(0.0), exact(0.0))
    };
    let all = [x.hi(), x.lo(), y.hi(), y.lo()];
    let within = |k| usable && all.iter().all(|&w| at_most(w, k));
    let zero_ok = |exact_zero: bool, z: DoubleWord| !exact_zero || (z.hi() == 0.0 && z.lo() == 0.0);

    for (name, checked, apply, other) in [
        (
            "add",
            x.checked_add(y).ok(),
            DoubleWord::add as fn(DoubleWord, DoubleWord) -> DoubleWord,
            yv.clone(),
        ),
        ("sub", x.checked_sub(y).ok(), DoubleWord::sub, -yv.clone()),
    ] {
        let sum = if usable { add(&xv, &other) } else { exact(0.0) };
        check_operation(
            name,
            checked,
            || apply(x, y),
            within(1016) && zero_ok(sum.is_zero(), apply(x, y)),
            Relative { half_u2: 6, u3: 13 },
            |z| (add(z, &-sum.clone()), sum.clone()),
        );
    }
    // Only the in-range products are exact enough to form: the oracle's own
    // product of two double words needs WIDE bits at most.
    let product = if usable { mul(&xv, &yv) } else { exact(0.0) };
    check_operation(
        "mul",
        x.checked_mul(y).ok(),
        || x.mul(y),
        within(508)
            && zero_or_at_least(x.hi(), y.hi(), -969)
            && zero_or_at_least(x.hi(), y.lo(), -1022)
            && zero_or_at_least(x.lo(), y.hi(), -1022)
            && zero_ok(x.hi() == 0.0 || y.hi() == 0.0, x.mul(y)),
        Relative { half_u2: 10, u3: 0 },
        |z| (add(z, &-product.clone()), product.clone()),
    );
    check_operation(
        "div",
        x.checked_div(y).ok(),
        || x.div(y),
        usable && y.hi() != 0.0 && quotient_range(&all) && zero_ok(x.hi() == 0.0, x.div(y)),
        Relative {
            half_u2: 30,
            u3: 56,
        },
        |z| (add(&mul(z, &yv), &-xv.clone()), xv.clone()),
    );
}

fn check_exact_constructors(a: f64, b: f64) {
    let finite = a.is_finite() && b.is_finite();
    for (name, checked, unchecked, admitted, expected) in [
        (
            "sum",
            DoubleWord::checked_sum(a, b).ok(),
            DoubleWord::sum(a, b),
            finite && at_most(a, 1020) && at_most(b, 1020),
            finite.then(|| add(&exact(a), &exact(b))),
        ),
        (
            "product",
            DoubleWord::checked_product(a, b).ok(),
            DoubleWord::product(a, b),
            finite && product_domain(a, b),
            finite.then(|| mul(&exact(a), &exact(b))),
        ),
    ] {
        assert_eq!(checked.is_some(), admitted, "{name}: admission {a:e} {b:e}");
        if let Some(z) = checked {
            assert_eq!(words(z), words(unchecked), "{name}: unchecked differs");
            assert!(valid(z), "{name}: not a double word");
            assert_eq!(Some(value(z)), expected, "{name}: not exact {a:e} {b:e}");
        }
    }
}

fn check_exponential(x: DoubleWord) {
    let result = x.exp_split();
    if x.hi().is_nan() || x.hi().abs() >= 1455.0 {
        assert_eq!(result.map(|(v, n)| (words(v), n)), None);
        return;
    }
    let (v, n) = result.expect("inside the exp_split domain");
    assert!(
        valid(v) && v.hi() >= 0.9996 && v.hi() < 2.0008,
        "exp_split range"
    );
    assert!((-2100..=2099).contains(&n), "exp_split exponent");
    let argument = value(x);
    // exp is increasing, so directed argument and result roundings enclose it.
    let p = 512;
    let mut lo = Float::with_val_round(p, &argument, Round::Down).0;
    let mut hi = Float::with_val_round(p, &argument, Round::Up).0;
    lo.exp_round(Round::Down);
    hi.exp_round(Round::Up);
    let scaled = if n >= 0 {
        value(v) << n.unsigned_abs()
    } else {
        value(v) >> n.unsigned_abs()
    };
    // 16 u^2 = 2^-102.
    let allowed = Float::with_val(p, &lo) >> 102;
    for end in [&lo, &hi] {
        let error = Float::with_val_round(p, &scaled - end, Round::Up).0.abs();
        assert!(
            error <= allowed,
            "exp_split bound violation: {:?}",
            words(x)
        );
    }
}

/// Up to 16 records of four little-endian binary64 encodings `(a, b, c, d)`;
/// incomplete records are ignored. Double words are formed from `(a, b)` and
/// `(c, d)`, both as given when valid and as their rounded sums.
pub fn check_input(data: &[u8]) {
    for record in data.as_chunks::<32>().0.iter().take(16) {
        let w: [f64; 4] = std::array::from_fn(|i| {
            f64::from_bits(u64::from_le_bytes(
                record[8 * i..8 * i + 8].try_into().unwrap(),
            ))
        });
        let [a, b, c, d] = w;
        for (p, q) in [(a, b), (c, d), (a, c)] {
            check_transforms(p, q);
            check_exact_constructors(p, q);
        }
        check_ulp(a, b);
        check_ulp(c, d);
        for (p, q, s) in [(a, b, c), (c, d, a)] {
            assert_eq!(
                DoubleWord::from_parts(p, q).is_some(),
                p.is_finite() && q.is_finite() && rounds_to(p, &add(&exact(p), &exact(q))),
                "from_parts admission"
            );
            for x in [DoubleWord::from_parts(p, q), Some(DoubleWord::sum(p, q))]
                .into_iter()
                .flatten()
            {
                check_scalar_operations(x, s);
                check_exponential(x);
            }
        }
        for x in [DoubleWord::from_parts(a, b), Some(DoubleWord::sum(a, b))]
            .into_iter()
            .flatten()
        {
            for y in [DoubleWord::from_parts(c, d), Some(DoubleWord::sum(c, d))]
                .into_iter()
                .flatten()
            {
                check_pair_operations(x, y);
                check_pair_operations(x, x.neg());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet(w: [f64; 4]) -> Vec<u8> {
        w.iter().flat_map(|x| x.to_bits().to_le_bytes()).collect()
    }

    #[test]
    fn domain_boundaries_and_neighbors_satisfy_their_contracts() {
        for k in [
            -1074, -1022, -969, -537, -485, -484, -229, 0, 10, 508, 994, 1016, 1018, 1020, 1021,
        ] {
            let center = power(k).to_f64_round(Round::Nearest);
            for x in [center.next_down(), center, center.next_up()] {
                check_input(&packet([x, x * 1.0e-17, -x, 3.0]));
                check_input(&packet([x, 0.0, 1.0 / 3.0, 1.0e-18]));
                check_input(&packet([-x, f64::from_bits(1), x, -f64::from_bits(1)]));
            }
        }
        for x in [1455.0_f64, -1455.0, 0.5, -745.0, 709.0] {
            for x in [x.next_down(), x, x.next_up()] {
                check_input(&packet([x, x * 1.0e-18, 2.0, 0.0]));
            }
        }
    }

    #[test]
    fn special_encodings_are_accepted_by_the_harness() {
        let specials = [
            0.0,
            -0.0,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MAX,
            f64::from_bits(0x7ff0_0000_0000_0042),
        ];
        for a in specials {
            for b in specials {
                check_input(&packet([a, b, 1.0, b]));
            }
        }
    }

    #[test]
    fn the_bound_comparison_keeps_the_cubic_term_and_rejects_excess() {
        let bound = Relative { half_u2: 6, u3: 13 };
        let one = exact(1.0);
        let limit = add(
            &mul(&power(-106), &exact(3.0)),
            &mul(&power(-159), &exact(13.0)),
        );
        assert!(bound.admits(&limit, &one));
        assert!(!bound.admits(&add(&limit, &power(-400)), &one));
    }

    #[test]
    fn the_oracle_rejects_a_wrong_result_and_a_wrong_admission() {
        let x = DoubleWord::sum(1.0, 1.0e-20);
        let run = |z: Option<DoubleWord>, admitted: bool| {
            std::panic::catch_unwind(|| {
                check_operation(
                    "planted",
                    z,
                    || z.unwrap(),
                    admitted,
                    Relative { half_u2: 4, u3: 0 },
                    |z| (add(z, &-value(x)), value(x)),
                )
            })
        };
        assert!(run(Some(x), true).is_ok());
        assert!(run(Some(DoubleWord::sum(1.0, 1.0e-19)), true).is_err());
        assert!(run(Some(x), false).is_err());
        assert!(run(None, true).is_err());
        assert!(!rounds_to(1.0_f64.next_up(), &exact(1.0)));
        assert!(rounds_to(-0.0, &exact(0.0)));
    }
}
