//! Error-free transforms: the rounded sum or product of two binary64 numbers,
//! together with its exact rounding error.
//!
//! The algorithms, their sources, and the domains on which each is exact are in
//! [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md).

/// Veltkamp's splitting constant `2^27 + 1`, for binary64's 53-bit significand
/// split into 26 and 27 bits (Dekker 1971, (5.7) and (6.2)).
const SPLITTER: f64 = 134_217_729.0;

/// `(s, t)` with `s = RN(a + b)` and `s + t = a + b` exactly, for any `a` and
/// `b` at most `2^1020` in magnitude, which excludes overflow
/// (`two_sum_ieee`, `formal/binary64/IEEE64Eft.v`).
///
/// Knuth and Møller's 2Sum, operation for operation as Joldes, Muller and
/// Popescu (2017) state it in Algorithm 2.
#[must_use]
#[inline]
pub const fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let a_prime = s - b;
    let b_prime = s - a_prime;
    let delta_a = a - a_prime;
    let delta_b = b - b_prime;
    (s, delta_a + delta_b)
}

/// `(s, t)` with `s = RN(a + b)` and `s + t = a + b` exactly, provided
/// `a = 0`, `|a| ≥ |b|`, or the exponent of `a` is at least that of `b`, and
/// `|a|, |b| ≤ 2^1021`, which excludes overflow (`fast_two_sum_ieee`,
/// `formal/binary64/IEEE64Eft.v`).
///
/// Dekker's Fast2Sum, as Joldes, Muller and Popescu (2017) state it in
/// Algorithm 1. Outside its precondition `t` need not be the exact error; use
/// [`two_sum`] there.
#[must_use]
#[inline]
pub const fn fast_two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let z = s - a;
    (s, b - z)
}

/// `x`'s head and tail: `x = head + tail` exactly, with `head` carrying at most
/// 26 significant bits and `tail` at most 26.
///
/// Veltkamp's splitting as Dekker (1971) gives it in (6.1), with `c = 2^27 + 1`
/// from (6.2) and the tail from (5.6). `x · c` can't overflow for
/// `|x| ≤ 2^994`.
#[inline]
const fn split(x: f64) -> (f64, f64) {
    let p = x * SPLITTER;
    let q = x - p;
    let head = q + p;
    (head, x - head)
}

/// `(p, e)` with `p = RN(a · b)` and `p + e = a · b` exactly.
///
/// Veltkamp's algorithm for the exact product, as Dekker (1971) gives it at
/// the end of §5, on Dekker's splitting. It needs no fused
/// multiply-add, so the result is the same on every target.
///
/// # Domain
///
/// Exact when `a · b = 0` or `|a · b| ≥ 2^-969`, and `|a| ≤ 2^e_a`,
/// `|b| ≤ 2^e_b` for some `e_a, e_b ≤ 994` with `e_a + e_b ≤ 1020`, which
/// excludes overflow.
///
/// - **Underflow:** the condition is that of Flocq's `Dekker` theorem,
///   instantiated for binary64 with ties-to-even in
///   `formal/two-prod/TwoProdBinary64.v`. It covers subnormal operands.
/// - **Overflow:** machine-checked in Flocq's IEEE 754 model (`two_prod_ieee`,
///   `formal/binary64/IEEE64Eft.v`).
///
/// These conditions are sufficient, not necessary: they are the proof's
/// hypotheses, not the boundary of exactness. Below `2^-969`, or beyond the
/// magnitude limits, `p + e = a · b` is neither claimed nor ruled out; the result
/// is whatever the arithmetic produces.
#[must_use]
#[inline]
pub const fn two_prod(a: f64, b: f64) -> (f64, f64) {
    let p = a * b;
    let (a_head, a_tail) = split(a);
    let (b_head, b_tail) = split(b);
    let e = (((a_head * b_head - p) + a_head * b_tail) + a_tail * b_head) + a_tail * b_tail;
    (p, e)
}
