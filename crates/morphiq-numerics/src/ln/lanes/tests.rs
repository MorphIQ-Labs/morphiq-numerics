//! The lane fast values are `ln`'s and `ln_1p`'s, word for word: every lane
//! the scalar function would try its fast path on gets that fast value's bits,
//! so the lane kernels transcribe the scalar operation sequences rather than
//! merely agreeing after rounding (docs/lanes.md §6).

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{fast_ln, fast_ln_1p};
use crate::double_word::DoubleWord;
use crate::lanes::tests::{backends, ln_1p_corpus, ln_corpus};
use crate::ln::{Reduced, ln_1p_double_word, split};

struct FastValues<'a> {
    xs: &'a [f64],
    ln_1p: bool,
}

impl WithSimd for FastValues<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        for chunk in self.xs.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let (y, scalar_lanes, case_a) = if self.ln_1p {
                fast_ln_1p(k, &x)
            } else {
                let (y, scalar_lanes) = fast_ln(k, &x);
                (y, scalar_lanes, 0)
            };
            let (hi, lo) = (k.store(y.0), k.store(y.1));
            for (i, &xi) in chunk.iter().enumerate() {
                if scalar_lanes >> i & 1 == 1 {
                    continue;
                }
                let want = if !self.ln_1p {
                    Reduced::of(xi).fast_value()
                } else if case_a >> i & 1 == 1 {
                    ln_1p_double_word(DoubleWord::from_f64(xi))
                } else {
                    let (h, l) = split(xi);
                    Reduced::of(h).fast_value().add_f64(l / h)
                };
                assert_eq!(
                    (hi.as_ref()[i].to_bits(), lo.as_ref()[i].to_bits()),
                    (want.hi().to_bits(), want.lo().to_bits()),
                    "{}'s fast value at {xi:e} on {}",
                    if self.ln_1p { "ln_1p" } else { "ln" },
                    K::NAME
                );
                compared += 1;
            }
        }
        assert!(compared > self.xs.len() / 3, "{} lanes compared", compared);
    }
}

#[test]
fn ln_lanes_compute_lns_fast_value_word_for_word() {
    let xs = ln_corpus();
    for backend in backends() {
        backend.vectorize(FastValues {
            xs: &xs,
            ln_1p: false,
        });
    }
}

#[test]
fn ln_1p_lanes_compute_ln_1ps_fast_value_word_for_word() {
    let xs = ln_1p_corpus();
    for backend in backends() {
        backend.vectorize(FastValues {
            xs: &xs,
            ln_1p: true,
        });
    }
}
