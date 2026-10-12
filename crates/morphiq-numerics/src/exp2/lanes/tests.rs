//! The lane stage values are `exp2`'s, word for word: every lane `exp2`'s
//! screen admits gets `Stages::of(x).a_value()`'s and `b_value()`'s bits, so
//! the lane kernel transcribes the scalar operation sequence rather than
//! merely agreeing after rounding (docs/lanes.md §6).

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{reduce, stage_a, stage_b};
use crate::exp2::stages::Stages;
use crate::lanes::tests::{backends, exp2_corpus};

struct StageValues<'a>(&'a [f64]);

impl WithSimd for StageValues<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        let mut rejected_a = 0;
        let mut rejected_b = 0;
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let reduced = reduce(k, &x);
            let (a, b) = (stage_a(k, &reduced), stage_b(k, &reduced));
            let (result_a, ok_a) = super::decide(k, a, super::E_A);
            let (result_b, ok_b) = super::decide(k, b, super::E_B);
            let result_a = k.store(k.mul(result_a, reduced.table.scale));
            let result_b = k.store(k.mul(result_b, reduced.table.scale));
            let words = |v: K::F| k.store(v);
            let (a_hi, a_lo, b_hi, b_lo) = (words(a.0), words(a.1), words(b.0), words(b.1));
            for (i, &xi) in chunk.iter().enumerate() {
                if reduced.screened >> i & 1 == 1 {
                    continue;
                }
                let stages = Stages::of(xi);
                let (ya, la) = stages.a_value();
                let (yb, lb) = stages.b_value();
                assert_eq!(
                    (a_hi.as_ref()[i].to_bits(), a_lo.as_ref()[i].to_bits()),
                    (ya.to_bits(), la.to_bits()),
                    "exp2's stage A value at {xi:e} on {}",
                    K::NAME
                );
                assert_eq!(
                    (b_hi.as_ref()[i].to_bits(), b_lo.as_ref()[i].to_bits()),
                    (yb.to_bits(), lb.to_bits()),
                    "exp2's stage B value at {xi:e} on {}",
                    K::NAME
                );
                for (result, accepted, value, error) in [
                    (
                        result_a.as_ref()[i],
                        ok_a >> i & 1 != 0,
                        (ya, la),
                        super::E_A,
                    ),
                    (
                        result_b.as_ref()[i],
                        ok_b >> i & 1 != 0,
                        (yb, lb),
                        super::E_B,
                    ),
                ] {
                    let expected = crate::exp::decide(value.0, value.1, error, stages.k);
                    assert_eq!(accepted, expected.is_some());
                    if let Some(expected) = expected {
                        assert_eq!(result.to_bits(), expected.to_bits());
                    }
                }
                rejected_a += usize::from(ok_a >> i & 1 == 0);
                rejected_b += usize::from(ok_b >> i & 1 == 0);
                compared += 1;
            }
        }
        assert!(rejected_a > 0);
        std::eprintln!(
            "{}: exp2 {compared}, A rejected {rejected_a}, B rejected {rejected_b}",
            K::NAME
        );
        assert!(compared > self.0.len() / 3, "{compared} lanes compared");
    }
}

#[test]
fn exp2_lanes_compute_scalar_stage_values_word_for_word() {
    let xs = exp2_corpus();
    for backend in backends() {
        backend.vectorize(StageValues(&xs));
    }
}
