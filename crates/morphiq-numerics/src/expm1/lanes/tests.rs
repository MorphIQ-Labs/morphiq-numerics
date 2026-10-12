//! Both subtraction stages and the small polynomial retain every scalar word.
use super::*;
use crate::lanes::tests::{backends, expm1_corpus};
use morphiq_numerics_arch::{Simd, WithSimd};

struct Values<'a>(&'a [f64]);
impl WithSimd for Values<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut small_count = 0;
        let mut general_count = 0;
        let mut small_rejected = 0;
        let mut stage_a_rejected = 0;
        for chunk in self.0.chunks_exact(K::LANES) {
            let mut small = K::Array::default();
            let mut general = K::Array::default();
            for (i, &x) in chunk.iter().enumerate() {
                small.as_mut()[i] = if x.abs() >= TINY && x.abs() < SMALL {
                    x
                } else {
                    1.0 / 64.0
                };
                general.as_mut()[i] = if x.abs() >= SMALL && x.abs() < 704.0 && x > -37.0 {
                    x
                } else {
                    1.0
                };
            }
            let sv = small_fast(k, k.load(small));
            let (sh, sl) = (k.store(sv.0), k.store(sv.1));
            let accepted = small_decide(k, sv);
            let r = reduce(k, &general);
            for (base, value) in [(E_A, stage_a(k, &r)), (E_B, stage_b(k, &r))] {
                let (s, lo, eps) = parts(k, value, inverse_scale(k, r.table.scale), base);
                let (s, lo, eps) = (k.store(s), k.store(lo), k.store(eps));
                let (result, decided) = subtract(k, value, inverse_scale(k, r.table.scale), base);
                let result = k.store(k.mul(result, r.table.scale));
                for (i, &x) in general.as_ref().iter().enumerate() {
                    let scalar = crate::exp::Stages::of(x);
                    let (h, l) = if base == E_A {
                        scalar.a_value()
                    } else {
                        scalar.b_value()
                    };
                    let exponent = i32::try_from(scalar.exponent()).unwrap();
                    let want = super::super::stages::parts(h, l, exponent, base);
                    assert_eq!(
                        [
                            s.as_ref()[i].to_bits(),
                            lo.as_ref()[i].to_bits(),
                            eps.as_ref()[i].to_bits()
                        ],
                        [want.0.to_bits(), want.1.to_bits(), want.2.to_bits()],
                        "{} subtraction at {x:e}",
                        K::NAME
                    );
                    let want = super::super::stages::subtract(h, l, exponent, base);
                    assert_eq!(decided >> i & 1 != 0, want.is_some());
                    if let Some(want) = want {
                        assert_eq!(result.as_ref()[i].to_bits(), want.to_bits());
                    }
                    if x == chunk[i] {
                        general_count += 1;
                        stage_a_rejected += usize::from(base == E_A && want.is_none());
                    }
                }
            }
            for (i, &x) in small.as_ref().iter().enumerate() {
                let want = super::super::small_fast(x);
                assert_eq!(
                    [sh.as_ref()[i].to_bits(), sl.as_ref()[i].to_bits()],
                    [want.hi().to_bits(), want.lo().to_bits()],
                    "{} small at {x:e}",
                    K::NAME
                );
                let decided = crate::ln::decide_with(want, EPS).is_some();
                assert_eq!(accepted >> i & 1 != 0, decided);
                if x == chunk[i] {
                    small_count += 1;
                    small_rejected += usize::from(!decided);
                }
            }
        }
        assert!(small_count > 100 && general_count > 100);
        assert!(small_rejected > 0 && stage_a_rejected > 0);
        std::eprintln!(
            "{}: small {small_count} ({small_rejected} rejected), general {general_count} ({stage_a_rejected} A rejected)",
            K::NAME
        );
    }
}
#[test]
fn expm1_lanes_compute_scalar_words_and_decisions() {
    let xs = expm1_corpus();
    for backend in backends() {
        backend.vectorize(Values(&xs));
    }
}
