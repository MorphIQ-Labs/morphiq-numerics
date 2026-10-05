//! Error-free transforms: the rounded sum or product of two binary64 numbers,
//! together with its exact rounding error.
//!
//! The algorithms, their sources, and the domains on which each is exact are in
//! [`docs/double-word.md`](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/double-word.md).

/// Veltkamp's splitting constant `2^27 + 1`, for binary64's 53-bit significand
/// split into 26 and 27 bits (Dekker 1971, (5.7) and (6.2)).
const SPLITTER: f64 = 134_217_729.0;

/// `(s, t)` with `s = RN(a + b)` and `s + t = a + b` exactly, for any finite
/// `a` and `b` whose sum doesn't overflow.
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
/// `a = 0`, `b = 0`, or the exponent of `a` is at least that of `b`; `|a| ≥ |b|`
/// suffices. The sum must not overflow.
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
/// from (6.2) and the tail from (5.6). Exact for normal `x` with `|x| ≤ 2^996`,
/// where `x · c` neither overflows nor rounds in the subnormal range.
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
/// Exact when `a` or `b` is zero, or when all of these hold, writing `e_x`
/// for the exponent of `x` (`2^e_x ≤ |x| < 2^(e_x+1)`):
/// - `a` and `b` are normal, with `|a|, |b| ≤ 2^996`, so the splitting
///   neither overflows nor rounds in the subnormal range;
/// - `e_a + e_b ≥ -970`: every intermediate is then a multiple of
///   `2^(e_a+e_b-104) ≥ 2^-1074`, so gradual underflow loses no bit;
/// - `e_a + e_b ≤ 1021`: `|a · b| < 2^1023`, so no intermediate overflows.
///
/// Outside that domain the result is finite or infinite as the arithmetic
/// produces it, but `p + e = a · b` isn't claimed.
#[must_use]
#[inline]
pub const fn two_prod(a: f64, b: f64) -> (f64, f64) {
    let p = a * b;
    let (a_head, a_tail) = split(a);
    let (b_head, b_tail) = split(b);
    let e = (((a_head * b_head - p) + a_head * b_tail) + a_tail * b_head) + a_tail * b_tail;
    (p, e)
}
