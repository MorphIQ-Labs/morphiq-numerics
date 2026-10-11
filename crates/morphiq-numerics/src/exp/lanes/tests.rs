//! The lane fast value is `exp`'s, word for word: every lane `exp` would try
//! its fast path on gets `Reduced::of(x).fast_value()`'s bits, so the lane
//! kernel transcribes the scalar operation sequence rather than merely
//! agreeing after rounding (docs/lanes.md §6).

use morphiq_numerics_arch::{Simd, WithSimd};

use super::fast;
use crate::exp::Reduced;
use crate::lanes::tests::{backends, exp_corpus};

struct FastValues<'a>(&'a [f64]);

impl WithSimd for FastValues<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let (y, _, scalar_lanes) = fast(k, &x);
            let (hi, lo) = (k.store(y.0), k.store(y.1));
            for (i, &xi) in chunk.iter().enumerate() {
                if scalar_lanes >> i & 1 == 1 {
                    continue;
                }
                let want = Reduced::of(xi).fast_value();
                assert_eq!(
                    (hi.as_ref()[i].to_bits(), lo.as_ref()[i].to_bits()),
                    (want.hi().to_bits(), want.lo().to_bits()),
                    "exp's fast value at {xi:e} on {}",
                    K::NAME
                );
                compared += 1;
            }
        }
        assert!(compared > self.0.len() / 2, "{} lanes compared", compared);
    }
}

#[test]
fn exp_lanes_compute_exps_fast_value_word_for_word() {
    let xs = exp_corpus();
    for backend in backends() {
        backend.vectorize(FastValues(&xs));
    }
}
