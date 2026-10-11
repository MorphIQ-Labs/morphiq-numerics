//! The lane fast values are `ln`'s and `ln_1p`'s, word for word: every lane
//! the scalar function would try its fast path (`ln`) or stage H (`ln_1p`) on
//! gets that value's bits, so the lane kernels transcribe the scalar operation
//! sequences rather than merely agreeing after rounding (docs/lanes.md §6).

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{fast_ln, stage_h};
use crate::lanes::tests::{backends, ln_1p_corpus, ln_corpus};
use crate::ln::Reduced;
use crate::ln::stages::stage_h_parts;

struct FastValues<'a> {
    xs: &'a [f64],
}

impl WithSimd for FastValues<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        for chunk in self.xs.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let (y, scalar_lanes) = fast_ln(k, &x);
            let (hi, lo) = (k.store(y.0), k.store(y.1));
            for (i, &xi) in chunk.iter().enumerate() {
                if scalar_lanes >> i & 1 == 1 {
                    continue;
                }
                let want = Reduced::of(xi).fast_value();
                assert_eq!(
                    (hi.as_ref()[i].to_bits(), lo.as_ref()[i].to_bits()),
                    (want.hi().to_bits(), want.lo().to_bits()),
                    "ln's fast value at {xi:e} on {}",
                    K::NAME
                );
                compared += 1;
            }
        }
        assert!(compared > self.xs.len() / 3, "{} lanes compared", compared);
    }
}

struct StageH<'a> {
    xs: &'a [f64],
}

impl WithSimd for StageH<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut compared = 0_usize;
        for chunk in self.xs.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let ((s, lo, eps), scalar_lanes) = stage_h(k, &x);
            let (s, lo, eps) = (k.store(s), k.store(lo), k.store(eps));
            for (i, &xi) in chunk.iter().enumerate() {
                if scalar_lanes >> i & 1 == 1 {
                    continue;
                }
                let (ws, wlo, weps, _) = stage_h_parts(xi);
                assert_eq!(
                    (
                        s.as_ref()[i].to_bits(),
                        lo.as_ref()[i].to_bits(),
                        eps.as_ref()[i].to_bits()
                    ),
                    (ws.to_bits(), wlo.to_bits(), weps.to_bits()),
                    "ln_1p's stage H at {xi:e} on {}",
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
        backend.vectorize(FastValues { xs: &xs });
    }
}

#[test]
fn ln_1p_lanes_compute_stage_h_word_for_word() {
    let xs = ln_1p_corpus();
    for backend in backends() {
        backend.vectorize(StageH { xs: &xs });
    }
}
