//! Final-grid candidates for the narrow finite bands beyond |x|=37.
//! Accepted-rounding compositions: NormalFiniteDensity.v and NormalFiniteTail.v.
use super::{Operation, dw, gaussian, pow2, scaled_erfcx, tables};

const DOWN: f64 = f64::from_bits(0x1a70_0000_0000_0000); // 2^-600
const UP: f64 = f64::from_bits(0x6570_0000_0000_0000); // 2^600
const HALF: f64 = f64::from_bits(0x2240_0000_0000_0000); // 2^-475
const NORMAL: f64 = f64::from_bits(0x2598_0000_0000_0000); // 1.5 * 2^-422
const GUARD: f64 = f64::from_bits(0x3be0_0000_0000_0000); // 2^-65
const ABS_GUARD: f64 = f64::from_bits(0x1f70_0000_0000_0000); // 2^-520

fn final_grid((h, l): (f64, f64)) -> Option<f64> {
    if h >= NORMAL {
        return crate::erfcx::decide(h, l, GUARD).map(|v| v * DOWN);
    }
    let mut c = (h * DOWN).abs();
    let residual = (h - c * UP) + l;
    if residual > HALF {
        c = f64::from_bits(c.to_bits() + 1);
    } else if residual < -HALF && c != 0.0 {
        c = f64::from_bits(c.to_bits() - 1);
    }
    let distance = ((h - c * UP) + l).abs();
    (distance + (h * GUARD + ABS_GUARD) < HALF).then_some(c)
}

pub(crate) fn candidate(op: Operation, a: f64) -> (f64, f64) {
    let (g, exponent) = gaussian(a);
    let (y, exponent) = if matches!(op, Operation::Pdf) {
        (g.mul(dw(tables::DENSITY)), exponent)
    } else {
        (g.mul(scaled_erfcx(a)), exponent - 1)
    };
    // Retain both words in a normal binade until the final underflow-grid test.
    let scale = pow2(exponent + 600);
    (y.hi() * scale, y.lo() * scale)
}

pub(crate) fn decide(op: Operation, a: f64) -> Option<f64> {
    final_grid(candidate(op, a)).map(|v| {
        if matches!(op, Operation::LogCdf) {
            -v
        } else {
            v
        }
    })
}

#[test]
fn finite_tail_candidates_match_independent_oracle() {
    use crate::test_exact::{entries, word};
    let mut accepted = [0; 3];
    let mut rejected = [0; 3];
    for case in entries(
        include_str!("../../../reference/fixtures/normal.json"),
        &["cases"],
    ) {
        let x = word(case, "x");
        if x <= 37.0 || x >= 39.0 {
            continue;
        }
        for (i, (op, name)) in [
            (Operation::Pdf, "pdf"),
            (Operation::Cdf, "ccdf"),
            (Operation::LogCdf, "log_cdf"),
        ]
        .into_iter()
        .enumerate()
        {
            if let Some(actual) = decide(op, x) {
                assert_eq!(
                    actual.to_bits(),
                    word(case, name).to_bits(),
                    "x={x:e} {op:?}"
                );
                accepted[i] += 1;
            } else {
                rejected[i] += 1;
            }
        }
    }
    std::println!("accepted={accepted:?} rejected={rejected:?}");
    assert!(accepted.into_iter().all(|n| n > 100));
}

#[cfg(feature = "simd")]
pub(super) mod lanes {
    use super::*;
    use crate::lanes::{decide_relative, lanes_mask, two_sum};
    use morphiq_numerics_arch::Simd;
    #[cfg(test)]
    use morphiq_numerics_arch::WithSimd;

    #[inline(always)]
    fn candidate<K: Simd>(k: K, op: Operation, a: K::F) -> (K::F, K::F) {
        let (g, mut scale) = super::super::lanes::gaussian_scaled::<K, 600>(k, a);
        let factor = if matches!(op, Operation::Pdf) {
            two_sum(k, k.splat(tables::DENSITY.0), k.splat(tables::DENSITY.1))
        } else {
            scale = k.mul(scale, k.splat(0.5));
            super::super::lanes::scaled_erfcx(k, a)
        };
        let y = super::super::lanes::mul(k, g, factor);
        let h = k.mul(y.0, scale);
        let l = k.mul(y.1, scale);
        (h, l)
    }

    #[inline(always)]
    pub(crate) fn decide<K: Simd>(k: K, op: Operation, a: K::F) -> (K::F, u64) {
        let (h, l) = candidate(k, op, a);
        let normal = k.le(k.splat(NORMAL), h);
        let normal_bits = k.mask_bits(normal);
        let ordinary = decide_relative(k, (h, l), GUARD);
        let initial = k.abs(k.mul(h, k.splat(DOWN)));
        if normal_bits == lanes_mask::<K>() {
            return (
                if matches!(op, Operation::LogCdf) {
                    k.neg(initial)
                } else {
                    initial
                },
                ordinary,
            );
        }
        let residual = k.add(k.sub(h, k.mul(initial, k.splat(UP))), l);
        let up = k.to_float(k.sub_u(k.to_bits(initial), k.splat_bits(u64::MAX)));
        let down = k.to_float(k.sub_u(k.to_bits(initial), k.splat_bits(1)));
        let go_down = k.and_m(k.lt(residual, k.splat(-HALF)), k.lt(k.splat(0.0), initial));
        let c = k.select(
            k.lt(k.splat(HALF), residual),
            up,
            k.select(go_down, down, initial),
        );
        let distance = k.abs(k.add(k.sub(h, k.mul(c, k.splat(UP))), l));
        let error = k.add(k.mul(h, k.splat(GUARD)), k.splat(ABS_GUARD));
        let accepted = k.mask_bits(k.lt(k.add(distance, error), k.splat(HALF)));
        let result = k.select(normal, initial, c);
        (
            if matches!(op, Operation::LogCdf) {
                k.neg(result)
            } else {
                result
            },
            (ordinary & normal_bits) | (accepted & !normal_bits),
        )
    }

    #[cfg(test)]
    struct Compare<'a> {
        xs: &'a [f64],
        expected: &'a [f64],
        op: Operation,
    }
    #[cfg(test)]
    impl WithSimd for Compare<'_> {
        type Output = ();
        #[inline(always)]
        fn with<K: Simd>(self, k: K) {
            for (chunk, expected) in self.xs.chunks(K::LANES).zip(self.expected.chunks(K::LANES)) {
                let mut input = K::Array::default();
                input.as_mut().fill(38.0);
                input.as_mut()[..chunk.len()].copy_from_slice(chunk);
                let (h, l) = candidate(k, self.op, k.load(input));
                let h = k.store(h);
                let l = k.store(l);
                let (values, accepted) = decide(k, self.op, k.load(input));
                let values = k.store(values);
                for (i, (&x, &expected)) in chunk.iter().zip(expected).enumerate() {
                    let (sh, sl) = super::candidate(self.op, x);
                    assert_eq!(
                        h.as_ref()[i].to_bits(),
                        sh.to_bits(),
                        "high {x:e} {}",
                        K::NAME
                    );
                    assert_eq!(
                        l.as_ref()[i].to_bits(),
                        sl.to_bits(),
                        "low {x:e} {}",
                        K::NAME
                    );
                    let scalar = super::decide(self.op, x);
                    assert_eq!(
                        accepted >> i & 1 != 0,
                        scalar.is_some(),
                        "{x:e} {}",
                        K::NAME
                    );
                    if let Some(scalar) = scalar {
                        assert_eq!(
                            values.as_ref()[i].to_bits(),
                            scalar.to_bits(),
                            "{x:e} {}",
                            K::NAME
                        );
                        assert_eq!(scalar.to_bits(), expected.to_bits(), "{x:e} {:?}", self.op);
                    }
                }
            }
        }
    }

    #[test]
    fn finite_tail_lanes_match_scalar_and_oracle() {
        use crate::test_exact::{entries, word};
        let cases = entries(
            include_str!("../../../reference/fixtures/normal.json"),
            &["cases"],
        );
        for (op, name) in [
            (Operation::Pdf, "pdf"),
            (Operation::Cdf, "ccdf"),
            (Operation::LogCdf, "log_cdf"),
        ] {
            let pairs: std::vec::Vec<_> = cases
                .iter()
                .filter_map(|case| {
                    let x = word(case, "x");
                    (x > 37.0 && x < 39.0).then(|| (x, word(case, name)))
                })
                .collect();
            let (xs, expected): (std::vec::Vec<_>, std::vec::Vec<_>) = pairs.into_iter().unzip();
            for backend in crate::lanes::tests::backends() {
                backend.vectorize(Compare {
                    xs: &xs,
                    expected: &expected,
                    op,
                });
            }
        }
    }
}
