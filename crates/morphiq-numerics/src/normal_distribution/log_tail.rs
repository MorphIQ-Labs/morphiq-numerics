//! Negative log-CDF tails with accepted-rounding proofs in
//! NormalLogFirst.v, NormalLogTailModerate.v and NormalLogTailHuge.v.
use super::{Dw, dw, tables};

const FIRST_LIMIT: f64 = 64.0;
const FIRST_GUARD: f64 = f64::from_bits(0x3ce0_0000_0000_0000); // 2^-49

const HUGE: f64 = f64::from_bits(0x42c0_0000_0000_0000); // 2^45
const DOWN: f64 = f64::from_bits(0x21f0_0000_0000_0000); // 2^-480
const UP: f64 = f64::from_bits(0x5df0_0000_0000_0000); // 2^480
const MODERATE_GUARD: f64 = f64::from_bits(0x3bb0_0000_0000_0000); // 2^-68
const GUARD: f64 = f64::from_bits(0x3bd0_0000_0000_0000); // 2^-66

/// Binary64 reconstruction on 37 <= a <= 64 (NormalLogFirst.v).
#[inline]
pub(crate) fn first_candidate(a: f64) -> (f64, f64) {
    let r = 1.0 / a;
    let u = r * r;
    let mut p = tables::LOG_TAIL[7];
    for i in (0..7).rev() {
        p = tables::LOG_TAIL[i] + u * p;
    }
    let (h, l, _, _) = crate::ln::stage::parts(0, a);
    let c = (h + tables::LN_SQRT_2PI.0) + (l + (tables::LN_SQRT_2PI.1 + u * p));
    let sq = Dw::product(a, -0.5 * a);
    let (high, low) = crate::eft::fast_two_sum(sq.hi(), -c);
    (high, low + sq.lo())
}

#[inline]
pub(crate) fn first_decide(a: f64) -> Option<f64> {
    let (h, l) = first_candidate(a);
    crate::ln::stages::decide(h, l, FIRST_GUARD)
}

/// For 37 < a < LOG_OVERFLOW. Returns a normalized candidate and the
/// power-of-two factor applied twice after a successful rounding test.
#[inline]
pub(crate) fn candidate(a: f64) -> (Dw, f64) {
    if a >= HUGE {
        // Scaling the argument first keeps both the square and Dekker's
        // residual normal. The omitted logarithmic correction is bounded
        // by 1028 (NormalLogOverflow.normal_log_tail_square_bounds).
        let r = a * DOWN;
        return (Dw::product(r, -0.5 * r), UP);
    }
    let reciprocal = 1.0 / a;
    let u = reciprocal * reciprocal;
    let mut p = tables::LOG_TAIL[7];
    for i in (0..7).rev() {
        p = tables::LOG_TAIL[i] + u * p;
    }
    let (h, l, _, _) = crate::ln::stage::parts(0, a);
    let correction = Dw::sum(h, l).add(dw(tables::LN_SQRT_2PI)).add_f64(u * p);
    (Dw::product(a, -0.5 * a).sub(correction), 1.0)
}

#[inline]
pub(super) fn decide(a: f64) -> Option<f64> {
    if !(37.0..tables::LOG_OVERFLOW).contains(&a) {
        return None;
    }
    if a <= FIRST_LIMIT
        && let Some(v) = first_decide(a)
    {
        return Some(v);
    }
    let (y, scale) = candidate(a);
    crate::erfcx::decide(
        y.hi(),
        y.lo(),
        if a >= HUGE { GUARD } else { MODERATE_GUARD },
    )
    .map(|v| if a >= HUGE { (v * scale) * scale } else { v })
}

#[test]
fn accepted_tail_candidates_match_independent_oracle() {
    use crate::test_exact::{entries, word};
    let mut accepted = 0;
    for case in entries(
        include_str!("../../../reference/fixtures/normal.json"),
        &["cases"],
    ) {
        let x = word(case, "x");
        if x < -37.0
            && x > -tables::LOG_OVERFLOW
            && let Some(actual) = decide(-x)
        {
            assert_eq!(actual.to_bits(), word(case, "log_cdf").to_bits(), "x={x:e}");
            accepted += 1;
        }
    }
    assert!(accepted > 100);
}

#[test]
#[ignore = "local tail measurement against Q256; no performance assertion"]
fn log_tail_local_measurement() {
    use core::hint::black_box;
    use std::time::{Duration, Instant};
    fn measure(xs: &[f64], f: impl Fn(f64) -> f64) -> f64 {
        let start = Instant::now();
        let mut rounds = 0_u32;
        while start.elapsed() < Duration::from_millis(150) {
            for &x in black_box(xs) {
                black_box(f(x));
            }
            rounds += 1;
        }
        #[allow(clippy::cast_precision_loss)] // bounded timing sample count
        {
            start.elapsed().as_secs_f64() * 1e9 / (f64::from(rounds) * xs.len() as f64)
        }
    }
    for kind in ["37_to_38", "38_to_100", "large", "huge"] {
        let xs: std::vec::Vec<_> = (0..4096)
            .map(|i| {
                let u = (f64::from(i) + 0.5) / 4096.0;
                match kind {
                    "37_to_38" => 37.0 + u,
                    "38_to_100" => 38.0 + 62.0 * u,
                    "large" => 100.0 + (HUGE - 100.0) * u,
                    _ => f64::from_bits(
                        (u64::try_from(45 + i % 468 + 1023).unwrap() << 52)
                            | ((u.to_bits() & ((1 << 52) - 1)) ^ 0x0005_a5a5_1234_5678),
                    ),
                }
            })
            .filter(|&a| a < tables::LOG_OVERFLOW)
            .collect();
        let fallback = xs.iter().filter(|&&a| decide(a).is_none()).count();
        let baseline = measure(&xs, |a| {
            super::accurate::evaluate(super::Operation::LogCdf, -a)
        });
        let scalar = measure(&xs, |a| super::evaluate(super::Operation::LogCdf, -a));
        std::println!(
            "{kind},q256_ns={baseline:.3},scalar_ns={scalar:.3},fallback={fallback}/{}",
            xs.len()
        );
    }
}

#[cfg(feature = "simd")]
pub(super) mod lanes {
    use super::*;
    use crate::lanes::{
        Dw as LaneDw, add_dw, add_f64, fast_two_sum, lanes_mask, two_prod, two_sum,
    };
    use morphiq_numerics_arch::Simd;
    #[cfg(test)]
    use morphiq_numerics_arch::WithSimd;

    #[inline(always)]
    fn first_candidate<K: Simd>(k: K, a: K::F) -> LaneDw<K> {
        let r = k.div(k.splat(1.0), a);
        let u = k.mul(r, r);
        let mut p = k.splat(tables::LOG_TAIL[7]);
        for i in (0..7).rev() {
            p = k.add(k.splat(tables::LOG_TAIL[i]), k.mul(u, p));
        }
        let (h, l, _) = crate::ln::lanes::direct_parts(k, a);
        let c = k.add(
            k.add(h, k.splat(tables::LN_SQRT_2PI.0)),
            k.add(l, k.add(k.splat(tables::LN_SQRT_2PI.1), k.mul(u, p))),
        );
        let sq = two_prod(k, a, k.mul(k.splat(-0.5), a));
        let (high, low) = fast_two_sum(k, sq.0, k.neg(c));
        (high, k.add(low, sq.1))
    }

    #[inline(always)]
    fn candidate<K: Simd>(k: K, a: K::F) -> (LaneDw<K>, K::F) {
        let huge = k.le(k.splat(HUGE), a);
        let bits = k.mask_bits(huge);
        let mut y = (k.splat(0.0), k.splat(0.0));
        if bits != 0 {
            let r = k.mul(k.select(huge, a, k.splat(HUGE)), k.splat(DOWN));
            y = two_prod(k, r, k.mul(k.splat(-0.5), r));
        }
        if bits != lanes_mask::<K>() {
            let a = k.select(huge, k.splat(38.0), a);
            let reciprocal = k.div(k.splat(1.0), a);
            let u = k.mul(reciprocal, reciprocal);
            let mut p = k.splat(tables::LOG_TAIL[7]);
            for i in (0..7).rev() {
                p = k.add(k.splat(tables::LOG_TAIL[i]), k.mul(u, p));
            }
            let c = two_sum(
                k,
                k.splat(tables::LN_SQRT_2PI.0),
                k.splat(tables::LN_SQRT_2PI.1),
            );
            let (lh, ll, _) = crate::ln::lanes::direct_parts(k, a);
            let logarithm = two_sum(k, lh, ll);
            let correction = add_f64(k, add_dw(k, logarithm, c), k.mul(u, p));
            let square = two_prod(k, a, k.mul(k.splat(-0.5), a));
            let regular = add_dw(k, square, (k.neg(correction.0), k.neg(correction.1)));
            y = (
                k.select(huge, y.0, regular.0),
                k.select(huge, y.1, regular.1),
            );
        }
        (y, k.select(huge, k.splat(UP), k.splat(1.0)))
    }

    /// All inputs are finite magnitudes in [37, LOG_OVERFLOW).
    #[inline(always)]
    pub(crate) fn decide<K: Simd>(k: K, a: K::F) -> (K::F, u64) {
        let eligible = k.le(a, k.splat(FIRST_LIMIT));
        if k.mask_bits(eligible) != 0 {
            let y = first_candidate(k, k.select(eligible, a, k.splat(38.0)));
            let low = k.add(y.0, k.sub(y.1, k.splat(FIRST_GUARD)));
            let high = k.add(y.0, k.add(y.1, k.splat(FIRST_GUARD)));
            let decided = k.and_m(eligible, k.and_m(k.le(low, high), k.le(high, low)));
            let accepted = k.mask_bits(decided);
            if accepted == lanes_mask::<K>() {
                return (low, accepted);
            }
            let (second, second_accepted) = second_decide(k, k.select(decided, k.splat(38.0), a));
            return (k.select(decided, low, second), accepted | second_accepted);
        }
        second_decide(k, a)
    }

    #[inline(always)]
    fn second_decide<K: Simd>(k: K, a: K::F) -> (K::F, u64) {
        let (y, scale) = candidate(k, a);
        let eps = k.select(
            k.le(k.splat(HUGE), a),
            k.splat(GUARD),
            k.splat(MODERATE_GUARD),
        );
        let accepted = crate::lanes::decide_relative_vector(k, y, eps);
        (k.mul(k.mul(y.0, scale), scale), accepted)
    }

    #[cfg(test)]
    struct Compare<'a>(&'a [f64]);
    #[cfg(test)]
    impl WithSimd for Compare<'_> {
        type Output = ();

        #[inline(always)]
        fn with<K: Simd>(self, k: K) {
            for chunk in self.0.chunks(K::LANES) {
                let mut input = K::Array::default();
                input.as_mut().fill(38.0);
                input.as_mut()[..chunk.len()].copy_from_slice(chunk);
                let first_input = k.select(
                    k.le(k.load(input), k.splat(FIRST_LIMIT)),
                    k.load(input),
                    k.splat(38.0),
                );
                let first = first_candidate(k, first_input);
                let first_hi = k.store(first.0);
                let first_lo = k.store(first.1);
                let (values, accepted) = decide(k, k.load(input));
                let values = k.store(values);
                let (y, scale) = candidate(k, k.load(input));
                let (hi, lo, scale) = (k.store(y.0), k.store(y.1), k.store(scale));
                for (i, &a) in chunk.iter().enumerate() {
                    let fa = if a <= FIRST_LIMIT { a } else { 38.0 };
                    let (fh, fl) = super::first_candidate(fa);
                    assert_eq!(
                        (
                            first_hi.as_ref()[i].to_bits(),
                            first_lo.as_ref()[i].to_bits()
                        ),
                        (fh.to_bits(), fl.to_bits()),
                        "first stage a={fa:e} {}",
                        K::NAME
                    );
                    let decision = super::decide(a);
                    assert_eq!(
                        accepted >> i & 1 != 0,
                        decision.is_some(),
                        "decision a={a:e} {}",
                        K::NAME
                    );
                    if let Some(v) = decision {
                        assert_eq!(
                            values.as_ref()[i].to_bits(),
                            v.to_bits(),
                            "result a={a:e} {}",
                            K::NAME
                        );
                    }
                    let (scalar, expected_scale) = super::candidate(a);
                    assert_eq!(
                        (
                            hi.as_ref()[i].to_bits(),
                            lo.as_ref()[i].to_bits(),
                            scale.as_ref()[i].to_bits()
                        ),
                        (
                            scalar.hi().to_bits(),
                            scalar.lo().to_bits(),
                            expected_scale.to_bits()
                        ),
                        "a={a:e} backend={}",
                        K::NAME
                    );
                }
            }
        }
    }

    #[test]
    fn tail_lanes_match_scalar_intermediates() {
        use crate::test_exact::{entries, word};
        let xs: std::vec::Vec<_> = entries(
            include_str!("../../../reference/fixtures/normal.json"),
            &["cases"],
        )
        .iter()
        .map(|case| -word(case, "x"))
        .filter(|&a| a > 37.0 && a < tables::LOG_OVERFLOW)
        .collect();
        for backend in crate::lanes::tests::backends() {
            backend.vectorize(Compare(&xs));
        }
    }
}
