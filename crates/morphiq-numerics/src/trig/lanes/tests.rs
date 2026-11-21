//! Raw words and decisions are checked before scalar fallback can mask them.
use super::*;
use crate::lanes::tests::backends;
use crate::test_exact::{entries, word};

fn corpus() -> std::vec::Vec<f64> {
    let mut xs = std::vec![
        f64::NAN,
        0.5,
        -0.0,
        f64::INFINITY,
        -1.0,
        1.0e-10,
        f64::MAX,
        -f64::MAX
    ];
    for e in 0..2047_u64 {
        for m in [0, 1, (1_u64 << 52) - 1] {
            let bits = (e << 52) | m;
            xs.extend([f64::from_bits(bits), f64::from_bits(bits | (1 << 63))]);
        }
    }
    for center in [
        SIN_IS_X.to_bits(),
        TAN_IS_X.to_bits(),
        COS_SMALL.to_bits(),
        super::super::QUARTER_PI.to_bits(),
    ] {
        for bits in center - 2..=center + 2 {
            xs.extend([f64::from_bits(bits), -f64::from_bits(bits)]);
        }
    }
    for fixture in [
        include_str!("../../../../reference/fixtures/sin_cos.json"),
        include_str!("../../../../reference/fixtures/tan.json"),
    ] {
        for section in ["precise", "cases"] {
            for case in entries(fixture, &[section]) {
                xs.push(word(case, "x"));
            }
        }
    }
    while xs.len() % 8 != 0 {
        xs.push(0.5);
    }
    xs
}

struct Values<'a, const KIND: u8>(&'a [f64]);
impl<const KIND: u8> WithSimd for Values<'_, KIND> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let (mut accepted, mut rejected, mut screened) = (0, 0, 0);
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut input = K::Array::default();
            input.as_mut().copy_from_slice(chunk);
            let r = prepare::<K, KIND>(input);
            let (s, c) = fast_pair(k, &r);
            let raw = [k.store(s.0), k.store(s.1), k.store(c.0), k.store(c.1)];
            let (value, active) = if KIND == TAN {
                tangent(k, s, c, &r)
            } else {
                (select(k, s, c, &r, KIND == COS), r.active)
            };
            let (hi, lo) = (k.store(value.0), k.store(value.1));
            let decisions = decision(k, value, if KIND == TAN { EPS_TAN } else { EPS }) & active;
            let out = Trig::<KIND>::lanes(k, input);
            let (pair_s, pair_c) = pair(k, input);
            for (lane, &x) in chunk.iter().enumerate() {
                let context = (K::NAME, KIND, x.to_bits());
                assert_eq!(
                    out.as_ref()[lane].to_bits(),
                    Trig::<KIND>::scalar(x).to_bits(),
                    "{context:?}"
                );
                let pair = super::super::sincos(x);
                assert_eq!(
                    (
                        pair_s.as_ref()[lane].to_bits(),
                        pair_c.as_ref()[lane].to_bits()
                    ),
                    (pair.0.to_bits(), pair.1.to_bits()),
                    "{context:?}"
                );
                if r.active >> lane & 1 == 0 {
                    screened += 1;
                    continue;
                }
                let reduced = Reduced::of(x);
                let (s, c) = super::super::fast(&reduced.r);
                for (vector, scalar) in raw.iter().zip([s.hi(), s.lo(), c.hi(), c.lo()]) {
                    assert_eq!(
                        vector.as_ref()[lane].to_bits(),
                        scalar.to_bits(),
                        "{context:?}"
                    );
                }
                let scalar = if KIND == TAN {
                    super::super::tan_fast(&reduced)
                } else {
                    let (swap, negative) = reduced.select(if KIND == COS {
                        Function::Cos
                    } else {
                        Function::Sin
                    });
                    let value = if swap { c } else { s };
                    Some(if negative { value.neg() } else { value })
                };
                assert_eq!(active >> lane & 1 != 0, scalar.is_some(), "{context:?}");
                if let Some(scalar) = scalar {
                    assert_eq!(
                        (hi.as_ref()[lane].to_bits(), lo.as_ref()[lane].to_bits()),
                        (scalar.hi().to_bits(), scalar.lo().to_bits()),
                        "{context:?}"
                    );
                    let d = crate::ln::decide_with(scalar, if KIND == TAN { EPS_TAN } else { EPS });
                    assert_eq!(decisions >> lane & 1 != 0, d.is_some(), "{context:?}");
                    if d.is_some() {
                        accepted += 1;
                    } else {
                        rejected += 1;
                    }
                }
            }
        }
        assert!(accepted > 0 && rejected > 0 && screened > 0);
        std::eprintln!(
            "{} kind={KIND}: {accepted} accepted, {rejected} rejected, {screened} screened",
            K::NAME
        );
    }
}

#[test]
fn trig_lanes_match_scalar_words_and_decisions() {
    let xs = corpus();
    for backend in backends() {
        backend.vectorize(Values::<SIN>(&xs));
        backend.vectorize(Values::<COS>(&xs));
        backend.vectorize(Values::<TAN>(&xs));
    }
}

#[test]
fn trig_slices_preserve_bits_for_short_slices_and_remainders() {
    let xs = corpus();
    for offset in 0..8 {
        for len in 0..35 {
            let x = &xs[offset..offset + len];
            for (batch, scalar) in [
                (
                    crate::elementary::sin_slice as fn(&[f64], &mut [f64]),
                    super::super::sin as fn(f64) -> f64,
                ),
                (crate::elementary::cos_slice, super::super::cos),
                (crate::elementary::tan_slice, super::super::tan),
            ] {
                let mut out = std::vec![0.0; len];
                batch(x, &mut out);
                for (&x, out) in x.iter().zip(out) {
                    assert_eq!(out.to_bits(), scalar(x).to_bits());
                }
            }
            let (mut s, mut c) = (std::vec![0.0; len], std::vec![0.0; len]);
            crate::elementary::sincos_slice(x, &mut s, &mut c);
            for ((&x, s), c) in x.iter().zip(s).zip(c) {
                let expected = super::super::sincos(x);
                assert_eq!(
                    (s.to_bits(), c.to_bits()),
                    (expected.0.to_bits(), expected.1.to_bits())
                );
            }
        }
    }
}

struct Quotients;
impl WithSimd for Quotients {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let cases = [
            [1.0, 0.0, 1.0, 0.0],
            [-1.0, 0.0, 3.0, 0.0],
            [0.0, -0.0, 1.0, 0.0],
            [-0.0, 0.0, -1.0, 0.0],
            [1.0, 0.0, 0.0, 0.0],
            [1.0, 1.0, 1.0, 0.0],
            [f64::NAN, 0.0, 1.0, 0.0],
            [1.0, 0.0, f64::INFINITY, 0.0],
            [f64::from_bits(1), 0.0, 1.0, 0.0],
            [f64::from_bits((1023 + 457) << 52), 0.0, 1.0, 0.0],
            [f64::from_bits((1023 + 458) << 52), 0.0, 1.0, 0.0],
            [f64::from_bits((1023 - 457) << 52), 0.0, 1.0, 0.0],
            [f64::from_bits((1023 - 458) << 52), 0.0, 1.0, 0.0],
        ];
        let mut accepts = 0;
        let mut rejects = 0;
        for start in 0..cases.len() {
            let mut words = [K::Array::default(); 4];
            for lane in 0..K::LANES {
                for (out, value) in words.iter_mut().zip(cases[(start + lane) % cases.len()]) {
                    out.as_mut()[lane] = value;
                }
            }
            let r = Reduction::<K> {
                hi: K::Array::default(),
                lo: K::Array::default(),
                odd: 0,
                sin_negative: 0,
                cos_negative: 0,
                tan_negative: 0,
                active: crate::lanes::lanes_mask::<K>(),
            };
            let (q, admitted) = tangent(
                k,
                (k.load(words[0]), k.load(words[1])),
                (k.load(words[2]), k.load(words[3])),
                &r,
            );
            let (hi, lo) = (k.store(q.0), k.store(q.1));
            for lane in 0..K::LANES {
                let [xh, xl, yh, yl] = cases[(start + lane) % cases.len()];
                let expected = DoubleWord::from_parts(xh, xl)
                    .zip(DoubleWord::from_parts(yh, yl))
                    .and_then(|(x, y)| x.checked_div(y).ok());
                assert_eq!(
                    admitted >> lane & 1 != 0,
                    expected.is_some(),
                    "{} {start} {lane}",
                    K::NAME
                );
                if let Some(expected) = expected {
                    accepts += 1;
                    assert_eq!(
                        (hi.as_ref()[lane].to_bits(), lo.as_ref()[lane].to_bits()),
                        (expected.hi().to_bits(), expected.lo().to_bits()),
                        "{} {start} {lane}",
                        K::NAME
                    );
                } else {
                    rejects += 1;
                }
            }
        }
        assert!(accepts > 0 && rejects > 0);
    }
}

#[test]
fn tangent_division_preserves_admission_boundaries_and_zero_words() {
    for backend in backends() {
        backend.vectorize(Quotients);
    }
}
