//! `Q128` against its contract (`docs/exp.md` §6), decided exactly with
//! big-integer arithmetic that shares nothing with the type.

use super::Q128;
use crate::random::SplitMix64;
use crate::test_exact::Exact;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_traits::Signed;

/// `−q`, exactly.
fn negated(q: Q128) -> Q128 {
    Q128::new(!q.negative, q.m, q.e)
}

/// A normalized `Q128` with a random significand, sign and exponent in
/// `[-range, range]`; one in eight has a significand with a run of zeros or
/// ones, where carries and cancellations happen.
fn random(rng: &mut SplitMix64, range: i32) -> Q128 {
    let mut m = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    match rng.next_u64() % 8 {
        0 => m |= (1 << 127) - (1 << (rng.next_u64() % 127)),
        1 => m &= !((1 << 127) - (1 << (rng.next_u64() % 127))),
        _ => {}
    }
    let span = u64::try_from(2 * range + 1).unwrap();
    let e = i32::try_from(rng.next_u64() % span).unwrap() - range;
    Q128::new(rng.next_u64() & 1 == 1, m | 1, e)
}

#[test]
fn new_normalizes_exactly() {
    let mut rng = SplitMix64::new(0x5131_3238_6e65_7701);
    for _ in 0..10_000 {
        let m = u128::from(rng.next_u64()) >> (rng.next_u64() % 64);
        let e = i32::try_from(rng.next_u64() % 400).unwrap() - 200;
        let q = Q128::new(false, m, e);
        assert!(q.m == 0 || q.m >> 127 == 1, "{q:?} is not normalized");
        let expected = Exact {
            mantissa: BigInt::from(m),
            exponent: i64::from(e),
        };
        assert_eq!(Exact::of(q).cmp(&expected), Ordering::Equal);
    }
}

#[test]
fn from_f64_is_exact() {
    let mut rng = SplitMix64::new(0x5131_3238_6636_3401);
    let edges = [
        0.0,
        -0.0,
        1.0,
        -1.0,
        f64::MIN_POSITIVE,
        f64::MAX,
        f64::from_bits(1),
    ];
    let randoms = (0..10_000).map(|_| f64::from_bits(rng.next_u64() % 0x7ff0_0000_0000_0000));
    for x in edges.into_iter().chain(randoms) {
        let q = Q128::from_f64(x);
        assert_eq!(
            Exact::of(q).cmp(&Exact::of_f64(x)),
            Ordering::Equal,
            "{x:e}"
        );
        assert!(q.m == 0 || q.m >> 127 == 1);
        assert_eq!(
            q.to_f64().to_bits(),
            if x == 0.0 { 0 } else { x.to_bits() },
            "{x:e}"
        );
    }
}

#[test]
fn mul_truncates_toward_zero() {
    let mut rng = SplitMix64::new(0x5131_3238_6d75_6c01);
    for _ in 0..100_000 {
        let (a, b) = (random(&mut rng, 300), random(&mut rng, 300));
        let p = a.mul(b);
        assert!(p.m >> 127 == 1, "{p:?} is not normalized");
        let exact = Exact::of(a).mul(&Exact::of(b));
        // Relative error in [-2^-127, 0]: same sign, |p| <= |exact|, and
        // |exact| - |p| <= 2^-127 |exact|.
        assert_eq!(p.negative, exact.mantissa.is_negative());
        let gap = exact.abs().sub(&Exact::of(p).abs());
        assert!(
            !gap.mantissa.is_negative(),
            "{a:?} * {b:?} rounded away from zero"
        );
        let bound = exact.abs().mul(&Exact::pow2(-127));
        assert_ne!(gap.cmp(&bound), Ordering::Greater, "{a:?} * {b:?}");
    }
    assert_eq!(Q128::ZERO.mul(Q128::ONE), Q128::ZERO);
    assert_eq!(Q128::ONE.mul(Q128::ONE), Q128::ONE);
}

#[test]
fn add_is_within_its_bound() {
    let mut rng = SplitMix64::new(0x5131_3238_6164_6401);
    for i in 0..100_000 {
        let a = random(&mut rng, 40);
        // Close exponents, opposite signs and equal magnitudes all occur.
        let b = match i % 4 {
            0 => negated(a),
            1 => Q128::new(!a.negative, a.m ^ (1 << (rng.next_u64() % 128)), a.e),
            _ => random(&mut rng, 40),
        };
        let s = a.add(b);
        assert!(s.m == 0 || s.m >> 127 == 1, "{s:?} is not normalized");
        let (ea, eb) = (Exact::of(a), Exact::of(b));
        let error = Exact::of(s).sub(&ea.add(&eb)).abs();
        let larger = if ea.abs().cmp(&eb.abs()) == Ordering::Less {
            eb.abs()
        } else {
            ea.abs()
        };
        let bound = larger.mul(&Exact::pow2(-126));
        assert_ne!(error.cmp(&bound), Ordering::Greater, "{a:?} + {b:?}");
    }
    assert_eq!(Q128::ONE.add(negated(Q128::ONE)), Q128::ZERO);
    assert_eq!(Q128::ONE.add(Q128::ZERO), Q128::ONE);
}

/// The binary64 neighbours of a finite `r`, by encoding; the larger
/// neighbour of the largest finite magnitude is treated as `2^1024`.
fn neighbours(r: f64) -> (Exact, Exact) {
    let up = |x: f64| {
        if x.to_bits() == 0x7fef_ffff_ffff_ffff {
            Exact::pow2(1024)
        } else if x == 0.0 {
            Exact::of_f64(f64::from_bits(1))
        } else if x > 0.0 {
            Exact::of_f64(f64::from_bits(x.to_bits() + 1))
        } else {
            Exact::of_f64(f64::from_bits(x.to_bits() - 1))
        }
    };
    let down = |x: f64| up(-x).neg();
    (down(r), up(r))
}

/// `r` is the binary64 nearest to `v`, ties to even; a magnitude at or beyond
/// `2^1024 − 2^970` (half an ulp above the largest finite) rounds to infinity.
fn check_rounding(v: &Exact, r: f64) {
    let overflow = Exact::pow2(1024).sub(&Exact::pow2(970));
    if v.abs().cmp(&overflow) != Ordering::Less {
        assert!(
            r.is_infinite() && (r < 0.0) == v.mantissa.is_negative(),
            "{v:?} -> {r:e}"
        );
        return;
    }
    assert!(r.is_finite(), "{v:?} -> {r:e}");
    let er = Exact::of_f64(r);
    let d = v.sub(&er).abs();
    let (lo, hi) = neighbours(r);
    for n in [lo, hi] {
        match d.cmp(&v.sub(&n).abs()) {
            Ordering::Less => {}
            Ordering::Equal => assert_eq!(r.to_bits() & 1, 0, "{v:?} -> {r:e}: tie not to even"),
            Ordering::Greater => panic!("{v:?} -> {r:e}: a neighbour is nearer"),
        }
    }
}

#[test]
fn to_f64_rounds_to_nearest_even() {
    let mut rng = SplitMix64::new(0x5131_3238_726e_6401);
    for _ in 0..100_000 {
        // Exponents across the whole binary64 range and past both ends.
        let q = random(&mut rng, 1250).mul_pow2(-127);
        check_rounding(&Exact::of(q), q.to_f64());
    }
    // Exact ties and near-ties at every scale, normal and subnormal.
    for _ in 0..20_000 {
        // top = t + 127 spans overflow, the normal range and deep subnormals.
        let t = i32::try_from(rng.next_u64() % 2330).unwrap() - 1330;
        let kept = u128::from(rng.next_u64() & ((1 << 52) - 1));
        // Half an ulp exactly, for a normal result (bit 74 is the half bit).
        let tie = (1u128 << 127) | (kept << 75) | (1 << 74);
        for m in [tie, tie - 1, tie + 1, tie & !(1 << 75)] {
            let q = Q128::new(rng.next_u64() & 1 == 1, m, t);
            check_rounding(&Exact::of(q), q.to_f64());
        }
    }
    assert_eq!(Q128::ZERO.to_f64().to_bits(), 0);
    assert_eq!(negated(Q128::ZERO).to_f64().to_bits(), 0);
}

#[test]
fn cmp_abs_is_exact() {
    let mut rng = SplitMix64::new(0x5131_3238_636d_7001);
    for _ in 0..20_000 {
        let (a, b) = (random(&mut rng, 3), random(&mut rng, 3));
        assert_eq!(a.cmp_abs(b), Exact::of(a).abs().cmp(&Exact::of(b).abs()));
        assert_eq!(a.cmp_abs(negated(a)), Ordering::Equal);
    }
    assert_eq!(Q128::ZERO.cmp_abs(Q128::ONE), Ordering::Less);
    assert!(negated(Q128::ONE).is_negative() && !negated(Q128::ZERO).is_negative());
}
