use super::*;
use crate::lanes::tests::backends;
use crate::random::SplitMix64;
use crate::test_exact::{entries, word};
use morphiq_numerics_arch::WithSimd;
use std::vec;
use std::vec::Vec;

struct Compare<'a>(&'a [f64]);

impl WithSimd for Compare<'_> {
    type Output = ();

    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let mut outputs = vec![0.0; self.0.len()];
        check::<Normal<0>, K>(k, self.0, &mut outputs);
        check::<Normal<1>, K>(k, self.0, &mut outputs);
        check::<Normal<2>, K>(k, self.0, &mut outputs);
        check::<Normal<3>, K>(k, self.0, &mut outputs);
        check::<Normal<4>, K>(k, self.0, &mut outputs);
        // Compare before the rounding decision, so a scalar fallback cannot
        // hide a wrong lane operation. Tiny/special inputs enter scalar paths.
        let regular: Vec<_> = self
            .0
            .iter()
            .copied()
            .filter(|x| x.is_finite() && (TINY..=37.0).contains(&x.abs()))
            .collect();
        for chunk in regular.chunks_exact(K::LANES) {
            let mut input = K::Array::default();
            input.as_mut().copy_from_slice(chunk);
            for op in [
                Operation::Pdf,
                Operation::Cdf,
                Operation::Centered,
                Operation::LogCdf,
            ] {
                let y = candidate(k, op, k.load(input));
                let (hi, lo) = (k.store(y.0), k.store(y.1));
                for (i, &x) in chunk.iter().enumerate() {
                    let scalar = super::super::fast(op, x).unwrap().0;
                    assert_eq!(
                        (hi.as_ref()[i].to_bits(), lo.as_ref()[i].to_bits()),
                        (scalar.hi().to_bits(), scalar.lo().to_bits()),
                        "{op:?} at {x:e}, backend {}",
                        K::NAME
                    );
                }
            }
        }
    }
}

#[inline]
fn check<G: Kernel, K: Simd>(k: K, xs: &[f64], out: &mut [f64]) {
    crate::lanes::run::<G, K>(k, xs, out);
    for (&x, &y) in xs.iter().zip(out.iter()) {
        assert_eq!(
            y.to_bits(),
            G::scalar(x).to_bits(),
            "{} x={:016x} backend {}",
            core::any::type_name::<G>(),
            x.to_bits(),
            K::NAME
        );
    }
}

#[test]
fn normal_lanes_preserve_scalar_intermediates_and_results() {
    let mut xs: Vec<_> = entries(
        include_str!("../../../../reference/fixtures/normal.json"),
        &["cases"],
    )
    .into_iter()
    .map(|case| word(case, "x"))
    .collect();
    let mut rng = SplitMix64::new(0x6e6f_726d_616c_0001);
    for _ in 0..8192 {
        #[allow(clippy::cast_precision_loss)] // 53-bit integer
        let u = (rng.next_u64() >> 11) as f64 * f64::from_bits(0x3ca0_0000_0000_0000);
        xs.extend([74.0 * u - 37.0, u - 0.5, f64::from_bits(rng.next_u64())]);
    }
    for backend in backends() {
        backend.vectorize(Compare(&xs));
        for x in [
            SMALL.next_down(),
            -SMALL.next_down(),
            -0.0,
            f64::from_bits(1),
        ] {
            backend.vectorize(Compare(&[x; 17]));
        }
        // Exercise homogeneous saturation as well as the mixed fixture stream,
        // including both finite neighbors of the log-CDF overflow boundary.
        for case in entries(
            include_str!("../../../../reference/fixtures/normal.json"),
            &["cases"],
        ) {
            let x = word(case, "x");
            if x < -1.0e154 {
                backend.vectorize(Compare(&[x; 17]));
            }
        }
    }
}

#[test]
fn normal_lanes_handle_short_slices_and_remainders() {
    let xs = [
        0.0,
        -0.0,
        f64::from_bits(1),
        -f64::from_bits(1),
        -0.5,
        0.5,
        1.0,
        -8.0,
        8.0,
        37.0,
        -37.0,
        39.0,
        -39.0,
        -40.0,
        -f64::from_bits(0x42c0_0000_0000_0000),
        -1.0e100,
        -super::super::tables::LOG_OVERFLOW.next_down(),
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits(0x7ff8_1234_5678_9abc),
        f64::from_bits(0xfff8_9876_5432_1abc),
    ];
    for backend in backends() {
        for start in 0..=xs.len() {
            for end in start..=xs.len() {
                backend.vectorize(Compare(&xs[start..end]));
            }
        }
    }
}
