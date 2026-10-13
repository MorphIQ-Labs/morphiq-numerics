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
            let (hi, lo, eps) = (k.store(y.0), k.store(y.1), k.store(y.2));
            for (i, &xi) in chunk.iter().enumerate() {
                if scalar_lanes >> i & 1 == 1 {
                    continue;
                }
                let reduced = Reduced::of(xi);
                let want = crate::ln::stage::parts(reduced.e, reduced.y);
                assert_eq!(
                    (
                        hi.as_ref()[i].to_bits(),
                        lo.as_ref()[i].to_bits(),
                        eps.as_ref()[i].to_bits()
                    ),
                    (want.0.to_bits(), want.1.to_bits(), want.2.to_bits()),
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

/// Force both fallback branches even when an earlier stage would decide.
struct FallbackValues<'a> {
    xs: &'a [f64],
    log1p: bool,
}

impl WithSimd for FallbackValues<'_> {
    type Output = ();
    fn with<K: Simd>(self, k: K) {
        let mut accepted = 0;
        let mut rejected = 0;
        for chunk in self.xs.chunks_exact(K::LANES) {
            let mut x = K::Array::default();
            x.as_mut().copy_from_slice(chunk);
            let y = if self.log1p {
                super::fallback::ln_1p(k, k.load(x))
            } else {
                super::fallback::ln(k, k.load(x))
            };
            let (hi, lo) = (k.store(y.0), k.store(y.1));
            let decisions = crate::lanes::decide_relative(k, y, crate::ln::EPS);
            for (i, &xi) in chunk.iter().enumerate() {
                let want = if !self.log1p {
                    Reduced::of(xi).fast_value()
                } else if xi.abs() < crate::ln::TWO_M7 {
                    crate::ln::ln_1p_double_word(crate::double_word::DoubleWord::from_f64(xi))
                } else {
                    let (h, l) = crate::ln::split(xi);
                    Reduced::of(h).fast_value().add_f64(l / h)
                };
                assert_eq!(
                    (hi.as_ref()[i].to_bits(), lo.as_ref()[i].to_bits()),
                    (want.hi().to_bits(), want.lo().to_bits()),
                    "fallback log1p={} at {xi:e} on {}",
                    self.log1p,
                    K::NAME
                );
                let decided = crate::ln::decide(want).is_some();
                assert_eq!(
                    decisions >> i & 1 != 0,
                    decided,
                    "rounding at {xi:e} on {}",
                    K::NAME
                );
                if decided {
                    accepted += 1;
                } else {
                    rejected += 1;
                }
            }
        }
        assert!(accepted > 100);
        assert!(rejected > 0, "rounding boundary coverage on {}", K::NAME);
    }
}

#[test]
fn ln_fallback_lanes_match_scalar_words_and_rounding_decisions() {
    let xs: std::vec::Vec<_> = ln_corpus()
        .into_iter()
        .filter(|&x| x > 0.0 && x < f64::INFINITY && x != 1.0)
        .collect();
    for backend in backends() {
        backend.vectorize(FallbackValues {
            xs: &xs,
            log1p: false,
        });
    }
}

#[test]
fn ln_1p_fallback_lanes_match_scalar_words_and_rounding_decisions() {
    let xs: std::vec::Vec<_> = ln_1p_corpus()
        .into_iter()
        .filter(|&x| x > -1.0 && x < f64::INFINITY && x.abs() >= crate::ln::TWO_M54)
        .collect();
    for backend in backends() {
        backend.vectorize(FallbackValues {
            xs: &xs,
            log1p: true,
        });
    }
}

struct PendingLanes<'a> {
    xs: &'a [f64],
    log1p: bool,
}

impl WithSimd for PendingLanes<'_> {
    type Output = ();
    fn with<K: Simd>(self, k: K) {
        use crate::lanes::Kernel;
        for &xi in self.xs {
            // Repeat an undecided argument to require vector completion, then
            // mix it with decided and screened lanes to exercise every mask.
            for period in [0, 2, 3, 4] {
                let mut x = K::Array::default();
                for (i, value) in x.as_mut().iter_mut().enumerate() {
                    *value = if period == 0 || i % period == 0 {
                        xi
                    } else if i % period == 1 {
                        0.0
                    } else {
                        f64::INFINITY
                    };
                }
                let out = if self.log1p {
                    super::Ln1p::lanes(k, x)
                } else {
                    super::Ln::lanes(k, x)
                };
                for (&input, &result) in x.as_ref().iter().zip(out.as_ref()) {
                    let want = if self.log1p {
                        crate::ln::ln_1p(input)
                    } else {
                        crate::ln::ln(input)
                    };
                    assert_eq!(
                        result.to_bits(),
                        want.to_bits(),
                        "pending log1p={} at {input:e} on {}",
                        self.log1p,
                        K::NAME
                    );
                }
            }
        }
    }
}

#[test]
fn undecided_logarithm_lanes_complete_alone_together_and_with_specials() {
    let ln: std::vec::Vec<_> = ln_corpus()
        .into_iter()
        .filter(|&x| {
            if !(x > 0.0 && x < f64::INFINITY) || x == 1.0 {
                return false;
            }
            let r = Reduced::of(x);
            crate::ln::stage::parts(r.e, r.y).3.is_none()
        })
        .collect();
    let ln1p: std::vec::Vec<_> = ln_1p_corpus()
        .into_iter()
        .filter(|&x| {
            x > -1.0
                && x < f64::INFINITY
                && x.abs() >= crate::ln::TWO_M54
                && !(crate::ln::stages::stage_h_screen(x)
                    && crate::ln::stages::stage_h(x).is_some())
                && !(crate::ln::stages::stage_b_screen(x)
                    && crate::ln::stages::stage_b(x).is_some())
        })
        .collect();
    assert!(!ln.is_empty() && !ln1p.is_empty());
    for backend in backends() {
        backend.vectorize(PendingLanes {
            xs: &ln,
            log1p: false,
        });
        backend.vectorize(PendingLanes {
            xs: &ln1p,
            log1p: true,
        });
    }
}
