//! The lane stage values are `exp`'s, word for word: every lane `exp`'s
//! screen admits gets `Stages::of(x).a_value()`'s and `b_value()`'s bits, so
//! the lane kernel transcribes the scalar operation sequence rather than
//! merely agreeing after rounding (docs/lanes.md §6).

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{reduce, stage_a, stage_b};
use crate::exp::Stages;
use crate::lanes::tests::{backends, exp_corpus};

struct StageValues<'a>(&'a [f64]);

impl WithSimd for StageValues<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let reduced = reduce(k, &x);
            let (a, b) = (stage_a(k, &reduced), stage_b(k, &reduced));
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
                    "exp's stage A value at {xi:e} on {}",
                    K::NAME
                );
                assert_eq!(
                    (b_hi.as_ref()[i].to_bits(), b_lo.as_ref()[i].to_bits()),
                    (yb.to_bits(), lb.to_bits()),
                    "exp's stage B value at {xi:e} on {}",
                    K::NAME
                );
                compared += 1;
            }
        }
        assert!(compared > self.0.len() / 2, "{compared} lanes compared");
    }
}

#[test]
fn exp_lanes_compute_exps_stage_values_word_for_word() {
    let xs = exp_corpus();
    for backend in backends() {
        backend.vectorize(StageValues(&xs));
    }
}
