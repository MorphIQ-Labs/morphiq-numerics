//! Every operation of every backend this CPU has, lane by lane, against the
//! scalar `f64` operation it names (IEEE 754 binary64, which the language
//! specifies). Fused multiply-add is checked against an exact product.

use std::vec::Vec;

use crate::{Scalar, Simd, WithSimd};

/// Operands: special values, every class of encoding, and random words.
fn operands() -> Vec<f64> {
    let mut v = std::vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        -f64::from_bits(1),
        f64::MAX,
        -f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        -f64::NAN,
        f64::EPSILON,
        1.0 + f64::EPSILON,
        3.0,
        f64::from_bits(0x000f_ffff_ffff_ffff),
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    for _ in 0..2_000 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        v.push(f64::from_bits(state));
        // Near 1, where products and sums cancel.
        v.push(f64::from_bits(0x3ff0_0000_0000_0000 ^ (state >> 20)));
    }
    v
}

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

/// Lane `i` of each operation on `(a[i], b[i])` equals the scalar operation.
struct Check<'a>(&'a [f64], &'a [f64]);

impl WithSimd for Check<'_> {
    type Output = ();
    #[inline(always)]
    fn with<S: Simd>(self, s: S) {
        let n = S::LANES;
        let all = (1_u64 << n) - 1;
        let prefix: Vec<_> = (0..n).map(|i| self.0[i]).collect();
        for len in 0..=n {
            let loaded = s.store(s.load_partial(&prefix[..len]));
            for (i, &x) in loaded.as_ref().iter().enumerate() {
                let expected = if i < len { prefix[i].to_bits() } else { 0 };
                assert_eq!(x.to_bits(), expected, "{}: padded load", S::NAME);
            }
            let sentinel = f64::from_bits(0x7ff8_0000_0000_1234);
            let mut output = std::vec![sentinel; n + 2];
            s.store_partial(s.load_partial(&prefix), &mut output[1..=len]);
            for (i, &x) in output.iter().enumerate() {
                let expected = if (1..=len).contains(&i) {
                    prefix[i - 1].to_bits()
                } else {
                    sentinel.to_bits()
                };
                assert_eq!(x.to_bits(), expected, "{}: partial store boundary", S::NAME);
            }
        }
        let oversized = std::vec![0.0; n + 1];
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| s.load_partial(&oversized)))
                .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || s.store_partial(s.splat(0.0), &mut oversized.clone())
            ))
            .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || s.gather_wrapped(&[0_u64; 0], s.splat_bits(0))
            ))
            .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || s.gather_wrapped(&[0_u64; 3], s.splat_bits(u64::MAX))
            ))
            .is_err()
        );
        for invalid in [0, 1, 3] {
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match invalid {
                0 => {
                    s.gather_pair_wrapped(&[0_u64; 0], s.splat_bits(u64::MAX));
                }
                1 => {
                    s.gather_pair_wrapped(&[0_u64; 1], s.splat_bits(u64::MAX));
                }
                _ => {
                    s.gather_pair_wrapped(&[0_u64; 3], s.splat_bits(u64::MAX));
                }
            }));
            assert!(caught.is_err(), "{}: invalid pair table", S::NAME);
        }
        for bits in 0..=all {
            for input in [bits, bits | !all] {
                let mask = s.mask_from_bits(input);
                assert_eq!(s.mask_bits(mask), bits, "{}: mask bits", S::NAME);
                let values = s.store(s.select(mask, s.splat(-1.0), s.splat(1.0)));
                for (i, &value) in values.as_ref().iter().enumerate() {
                    assert_eq!(value, if bits >> i & 1 != 0 { -1.0 } else { 1.0 });
                }
            }
        }
        for (xs, ys) in self.0.chunks_exact(n).zip(self.1.chunks_exact(n)) {
            let (mut a, mut b) = (S::Array::default(), S::Array::default());
            a.as_mut().copy_from_slice(xs);
            b.as_mut().copy_from_slice(ys);
            let (va, vb) = (s.load(a), s.load(b));
            let lanes = |v: S::F| s.store(v);
            let words = |v: S::U| s.store(s.to_float(v));
            let mask = |m: S::M| s.mask_bits(m);
            let ua = s.to_bits(va);
            let ub = s.to_bits(vb);
            let results = [
                (lanes(s.add(va, vb)), 0),
                (lanes(s.sub(va, vb)), 1),
                (lanes(s.mul(va, vb)), 2),
                (lanes(s.div(va, vb)), 3),
                (lanes(s.abs(va)), 4),
                (lanes(s.neg(va)), 5),
                (lanes(s.select(s.lt(va, vb), va, vb)), 6),
                (words(s.and_u(ua, ub)), 7),
                (words(s.or_u(ua, ub)), 8),
                (words(s.sub_u(ua, ub)), 9),
                (words(s.shr_u(ua, 45)), 12),
                (words(s.shr_u(ua, 0)), 13),
                (words(s.shr_u(ua, 64)), 14),
                (words(s.add_u(ua, ub)), 15),
                (words(s.shl_u(ua, 43)), 16),
                (words(s.shl_u(ua, 0)), 17),
                (words(s.shl_u(ua, 63)), 18),
                (words(s.shl_u(ua, 64)), 19),
                (words(s.shl_u(ua, 128)), 20),
                (lanes(s.splat(xs[0])), 10),
                (words(s.splat_bits(xs[0].to_bits())), 11),
            ];
            let mut wa = S::Words::default();
            for (w, x) in wa.as_mut().iter_mut().zip(xs) {
                *w = x.to_bits();
            }
            assert_eq!(
                words(s.load_bits(wa))
                    .as_ref()
                    .iter()
                    .map(|x| x.to_bits())
                    .collect::<Vec<_>>(),
                xs.iter().map(|x| x.to_bits()).collect::<Vec<_>>(),
                "{}: load_bits",
                S::NAME
            );
            let table = [
                0,
                1,
                u64::MAX,
                0x8000_0000_0000_0000,
                0x7ff0_0000_0000_0000,
                0x7ff8_0000_0000_1234,
                0x0010_0000_0000_0000,
                0x3ff0_0000_0000_0000,
            ];
            let gathered = s.store(s.gather_wrapped(&table, ua));
            for (&input, &output) in xs.iter().zip(gathered.as_ref()) {
                let index = usize::try_from(input.to_bits() & 7).unwrap();
                assert_eq!(
                    output.to_bits(),
                    table[index],
                    "{}: wrapped gather",
                    S::NAME
                );
            }
            let (first, second) = s.gather_pair_wrapped(&table, ua);
            let (first, second) = (s.store(first), s.store(second));
            for (lane, &input) in xs.iter().enumerate() {
                let i = usize::try_from(input.to_bits() & 6).unwrap();
                assert_eq!(
                    first.as_ref()[lane].to_bits(),
                    table[i],
                    "{}: pair first",
                    S::NAME
                );
                assert_eq!(
                    second.as_ref()[lane].to_bits(),
                    table[i + 1],
                    "{}: pair second",
                    S::NAME
                );
            }
            let lt = mask(s.lt(va, vb));
            let le = mask(s.le(va, vb));
            let eq = mask(s.eq_u(ua, ub));
            let eq_self = mask(s.eq_u(ua, ua));
            let both = mask(s.and_m(s.lt(va, vb), s.le(vb, va)));
            let either = mask(s.or_m(s.lt(va, vb), s.lt(vb, va)));
            let not_lt = mask(s.not_m(s.lt(va, vb)));
            let all = (1u64 << n) - 1;
            assert_eq!(eq_self, all, "{}: eq_u reflexive", S::NAME);
            assert_eq!(not_lt, !lt & all, "{}: not_m", S::NAME);
            for i in 0..n {
                let (x, y) = (xs[i], ys[i]);
                let expected = [
                    x + y,
                    x - y,
                    x * y,
                    x / y,
                    x.abs(),
                    -x,
                    if x < y { x } else { y },
                    f64::from_bits(x.to_bits() & y.to_bits()),
                    f64::from_bits(x.to_bits() | y.to_bits()),
                    f64::from_bits(x.to_bits().wrapping_sub(y.to_bits())),
                    xs[0],
                    xs[0],
                    f64::from_bits(x.to_bits() >> 45),
                    x,
                    0.0,
                    f64::from_bits(x.to_bits().wrapping_add(y.to_bits())),
                    f64::from_bits(x.to_bits() << 43),
                    x,
                    f64::from_bits(x.to_bits() << 63),
                    0.0,
                    0.0,
                ];
                for (got, op) in &results {
                    let want = expected[*op];
                    // Bit operations are compared as words, NaN payloads included.
                    let exact = matches!(op, 4 | 5 | 7..=20);
                    let ok = if exact {
                        got.as_ref()[i].to_bits() == want.to_bits()
                    } else {
                        same(got.as_ref()[i], want)
                    };
                    assert!(ok, "{}: op {op} on ({x:e}, {y:e}) lane {i}", S::NAME);
                }
                let bit = |m: u64| m >> i & 1 == 1;
                assert_eq!(bit(lt), x < y, "{}: lt({x:e}, {y:e})", S::NAME);
                assert_eq!(bit(le), x <= y, "{}: le({x:e}, {y:e})", S::NAME);
                assert_eq!(bit(eq), x.to_bits() == y.to_bits(), "{}: eq_u", S::NAME);
                assert_eq!(bit(both), x < y && y <= x, "{}: and_m", S::NAME);
                assert_eq!(bit(either), x < y || y < x, "{}: or_m", S::NAME);
            }
            assert_eq!(lt >> n, 0, "{}: mask bits above the lanes", S::NAME);
        }
    }
}

fn check<S: Simd>(s: S) {
    let a = operands();
    let mut b = a.clone();
    b.rotate_left(7);
    // Every pairing of the special values too.
    let specials = &a[..18];
    let mut sa = Vec::new();
    let mut sb = Vec::new();
    for &x in specials {
        for &y in specials {
            sa.push(x);
            sb.push(y);
        }
    }
    let (a, b) = ([a, sa].concat(), [b, sb].concat());
    s.vectorize(Check(&a, &b));
}

#[test]
fn scalar_lanes_are_scalar_arithmetic() {
    check(Scalar::new());
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[test]
fn neon_lanes_are_scalar_arithmetic() {
    check(crate::Neon::new());
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[test]
fn x86_lanes_are_scalar_arithmetic() {
    check(crate::Sse2::new());
    match crate::Avx2::try_new() {
        Some(s) => check(s),
        None => std::eprintln!("AVX2 with FMA not present: not checked"),
    }
    match crate::Avx512::try_new() {
        Some(s) => check(s),
        None => std::eprintln!("AVX-512F not present: not checked"),
    }
}

/// `mul_add(a, b, −RN(a·b))` is the exact product's error wherever that error
/// is representable: checked against the product in exact integer arithmetic
/// on operands whose product is normal and far from overflow.
fn check_fma<S: Simd>(s: S) {
    assert!(S::FMA, "{} has no FMA", S::NAME);
    let mut state = 0x2545_f491_4f6c_dd1d_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..20_000 / S::LANES {
        let (mut a, mut b) = (S::Array::default(), S::Array::default());
        for (x, y) in a.as_mut().iter_mut().zip(b.as_mut()) {
            // Exponents in [−200, 200], random significands and signs.
            let w = next();
            *x = f64::from_bits((w & (1 << 63)) | ((823 + w % 401) << 52) | (next() >> 12));
            let w = next();
            *y = f64::from_bits((w & (1 << 63)) | ((823 + w % 401) << 52) | (next() >> 12));
        }
        let (va, vb) = (s.load(a), s.load(b));
        let p = s.mul(va, vb);
        let e = s.store(s.mul_add(va, vb, s.neg(p)).expect("FMA"));
        let p = s.store(p);
        for i in 0..S::LANES {
            let (x, y) = (a.as_ref()[i], b.as_ref()[i]);
            assert!(
                exact_product_is(x, y, p.as_ref()[i], e.as_ref()[i]),
                "{}: fma error of {x:e}·{y:e}",
                S::NAME
            );
        }
    }
}

/// `p + e = x·y` exactly, by integer arithmetic on the significands.
fn exact_product_is(x: f64, y: f64, p: f64, e: f64) -> bool {
    // Every value here is normal, so v = m·2^(E − 1075) with m < 2^53.
    let parts = |v: f64| -> (i128, i32) {
        let b = v.to_bits();
        let m = i128::from((b & ((1 << 52) - 1)) | (1 << 52));
        let ex = i32::try_from((b >> 52) & 0x7ff).unwrap() - 1075;
        (if v < 0.0 { -m } else { m }, ex)
    };
    let (mx, ex) = parts(x);
    let (my, ey) = parts(y);
    let (mp, ep) = parts(p);
    if e == 0.0 {
        return mx * my == mp << (ep - ex - ey);
    }
    let (me, ee) = parts(e);
    // x·y and p are multiples of 2^(ex + ey), so e is too: with its trailing
    // zeros removed its exponent is at least ex + ey, and everything fits in
    // 2^107 on that grid.
    let tz = me.trailing_zeros().cast_signed();
    let (me, ee) = (me >> tz, ee + tz);
    let base = ex + ey;
    if ee < base {
        return false;
    }
    let lhs = mx * my;
    let rhs = (mp << (ep - base)) + (me << (ee - base));
    lhs == rhs
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[test]
fn neon_mul_add_gives_the_exact_product_error() {
    check_fma(crate::Neon::new());
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
#[test]
fn x86_mul_add_gives_the_exact_product_error() {
    #[cfg(target_feature = "fma")]
    check_fma(crate::Sse2::new());
    if let Some(s) = crate::Avx2::try_new() {
        check_fma(s);
    }
    if let Some(s) = crate::Avx512::try_new() {
        check_fma(s);
    }
}

#[test]
fn backends_without_fma_return_none() {
    const { assert!(!Scalar::FMA) };
    assert!(Scalar::new().mul_add(1.0, 2.0, 3.0).is_none());
    // SSE2 has the fused multiply-add only in builds that target FMA.
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "sse2",
        not(target_feature = "fma")
    ))]
    {
        let s = crate::Sse2::new();
        const { assert!(!crate::Sse2::FMA) };
        assert!(
            s.mul_add(s.splat(1.0), s.splat(2.0), s.splat(3.0))
                .is_none()
        );
    }
}

#[test]
fn dispatch_runs_some_backend() {
    struct Name;
    impl WithSimd for Name {
        type Output = &'static str;
        fn with<S: Simd>(self, _: S) -> &'static str {
            S::NAME
        }
    }
    let name = crate::dispatch(Name);
    std::eprintln!("dispatch selects {name}");
    assert!(["scalar", "neon", "sse2", "avx2", "avx512"].contains(&name));
}
