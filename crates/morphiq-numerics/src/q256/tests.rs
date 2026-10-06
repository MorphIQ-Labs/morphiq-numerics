//! `Q256` against its contract, decided exactly with big-integer arithmetic
//! that shares nothing with the type.

use super::Q256;
use crate::random::SplitMix64;
use crate::test_exact::Exact;
use core::cmp::Ordering;

fn negated(q: Q256) -> Q256 {
    Q256::new(!q.negative, q.m, q.e)
}

/// A random normalized significand; one in eight carries a run of zeros or
/// ones, where carries and cancellations happen.
fn limbs(rng: &mut SplitMix64) -> [u64; 4] {
    let mut m = [rng.next_u64(), rng.next_u64(), rng.next_u64(), rng.next_u64()];
    match rng.next_u64() % 8 {
        0 => m[1] = 0,
        1 => {
            m[1] = u64::MAX;
            m[2] = u64::MAX;
        }
        2 => m[0] = 0,
        _ => {}
    }
    m[3] |= 1 << 63;
    m
}

fn random(rng: &mut SplitMix64, range: i32) -> Q256 {
    let m = limbs(rng);
    let span = u64::try_from(2 * range + 1).unwrap();
    let e = i32::try_from(rng.next_u64() % span).unwrap() - range;
    Q256::new(rng.next_u64() & 1 == 1, m, e)
}

#[test]
fn new_and_from_f64_are_exact() {
    let mut rng = SplitMix64::new(0x5132_3536_6e65_7701);
    for _ in 0..5_000 {
        let m = [rng.next_u64() >> (rng.next_u64() % 64), rng.next_u64() % 3, 0, 0];
        let q = Q256::new(false, m, -100);
        assert!(q.m == [0; 4] || q.m[3] >> 63 == 1);
        let expected = Exact::of_q256(Q256 {
            negative: false,
            m,
            e: -100,
        });
        assert_eq!(Exact::of_q256(q).cmp(&expected), Ordering::Equal);
        let x = f64::from_bits(rng.next_u64() % 0x7ff0_0000_0000_0000);
        assert_eq!(
            Exact::of_q256(Q256::from_f64(x)).cmp(&Exact::of_f64(x)),
            Ordering::Equal
        );
        assert_eq!(Q256::from_f64(x).to_f64().to_bits(), x.to_bits());
    }
}

#[test]
fn mul_truncates_toward_zero() {
    let mut rng = SplitMix64::new(0x5132_3536_6d75_6c01);
    for _ in 0..50_000 {
        let (a, b) = (random(&mut rng, 300), random(&mut rng, 300));
        let p = a.mul(b);
        assert!(p.m[3] >> 63 == 1);
        let exact = Exact::of_q256(a).mul(&Exact::of_q256(b));
        assert_eq!(p.negative, exact.mantissa.is_negative());
        let gap = exact.abs().sub(&Exact::of_q256(p).abs());
        assert!(!gap.mantissa.is_negative(), "rounded away from zero");
        assert_ne!(
            gap.cmp(&exact.abs().mul(&Exact::pow2(-255))),
            Ordering::Greater
        );
    }
    assert_eq!(Q256::ONE.mul(Q256::ONE), Q256::ONE);
}

#[test]
fn add_is_within_its_bound() {
    let mut rng = SplitMix64::new(0x5132_3536_6164_6401);
    for i in 0..50_000 {
        let a = random(&mut rng, 70);
        let b = match i % 4 {
            0 => negated(a),
            1 => {
                let mut m = a.m;
                m[usize::try_from(rng.next_u64() % 4).unwrap()] ^= 1 << (rng.next_u64() % 64);
                Q256::new(!a.negative, m, a.e)
            }
            _ => random(&mut rng, 70),
        };
        let s = a.add(b);
        assert!(s.m == [0; 4] || s.m[3] >> 63 == 1);
        let (ea, eb) = (Exact::of_q256(a), Exact::of_q256(b));
        let error = Exact::of_q256(s).sub(&ea.add(&eb)).abs();
        let larger = if ea.abs().cmp(&eb.abs()) == Ordering::Less {
            eb.abs()
        } else {
            ea.abs()
        };
        assert_ne!(
            error.cmp(&larger.mul(&Exact::pow2(-254))),
            Ordering::Greater,
            "{a:?} + {b:?}"
        );
    }
    assert_eq!(Q256::ONE.add(negated(Q256::ONE)), Q256::ZERO);
}

/// The binary64 neighbours of `r` toward and away from zero, with `2^1024`
/// beyond the largest finite.
fn neighbours(r: f64) -> [Exact; 2] {
    let away = |x: f64| {
        let b = x.to_bits() & !(1 << 63);
        let v = if b == 0x7fef_ffff_ffff_ffff {
            Exact::pow2(1024)
        } else {
            Exact::of_f64(f64::from_bits(b + 1))
        };
        if x.is_sign_negative() { v.neg() } else { v }
    };
    let toward = |x: f64| {
        let b = x.to_bits() & !(1 << 63);
        if b == 0 {
            return Exact::of_f64(-f64::from_bits(1)).mul(&Exact::of_f64(x.signum()));
        }
        let v = Exact::of_f64(f64::from_bits(b - 1));
        if x.is_sign_negative() { v.neg() } else { v }
    };
    [toward(r), away(r)]
}

/// `r` is the binary64 nearest `v`, ties to even, or `±∞` past the overflow
/// threshold.
fn check_rounding(v: &Exact, r: f64) {
    let overflow = Exact::pow2(1024).sub(&Exact::pow2(970));
    if v.abs().cmp(&overflow) != Ordering::Less {
        assert!(r.is_infinite(), "{v:?} -> {r:e}");
        return;
    }
    let d = v.sub(&Exact::of_f64(r)).abs();
    for n in neighbours(r) {
        match d.cmp(&v.sub(&n).abs()) {
            Ordering::Less => {}
            Ordering::Equal => assert_eq!(r.to_bits() & 1, 0, "{v:?} -> {r:e}: tie not to even"),
            Ordering::Greater => panic!("{v:?} -> {r:e}: a neighbour is nearer"),
        }
    }
}

#[test]
fn to_f64_rounds_to_nearest_even() {
    let mut rng = SplitMix64::new(0x5132_3536_726e_6401);
    for _ in 0..50_000 {
        // Exponents across the whole binary64 range and past both ends.
        let span = 2 * 1250 + 1;
        let e = i32::try_from(rng.next_u64() % span).unwrap() - 1250 - 255;
        let q = Q256::new(rng.next_u64() & 1 == 1, limbs(&mut rng), e);
        check_rounding(&Exact::of_q256(q), q.to_f64());
    }
    for _ in 0..10_000 {
        // Exact ties for a normal result (bit 202 is the half bit), and their
        // neighbours, at scales that also reach the subnormals.
        let t = i32::try_from(rng.next_u64() % 2400).unwrap() - 1420 - 255;
        let kept = rng.next_u64() & ((1 << 52) - 1);
        let top = (1 << 63) | (kept << 11);
        for m in [
            [0, 0, 0, top | (1 << 10)],
            [u64::MAX, u64::MAX, u64::MAX, top | ((1 << 10) - 1)],
            [1, 0, 0, top | (1 << 10)],
        ] {
            let q = Q256::new(rng.next_u64() & 1 == 1, m, t);
            check_rounding(&Exact::of_q256(q), q.to_f64());
        }
    }
    assert_eq!(Q256::ZERO.to_f64().to_bits(), 0);
}

#[test]
fn cmp_abs_is_exact() {
    let mut rng = SplitMix64::new(0x5132_3536_636d_7001);
    for _ in 0..10_000 {
        let (a, b) = (random(&mut rng, 2), random(&mut rng, 2));
        assert_eq!(
            a.cmp_abs(b),
            Exact::of_q256(a).abs().cmp(&Exact::of_q256(b).abs())
        );
    }
}
