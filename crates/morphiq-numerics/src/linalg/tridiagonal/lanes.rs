// The Thomas recurrence is adapted from FerroRisk at
// 100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c, under its MIT license.
// Copyright (c) 2026 MorphIQ Labs. See THIRD_PARTY_NOTICES.md in this crate.
//! Independent RHS columns, with the scalar recurrence in every lane.
use super::{Error, Factors};
use morphiq_numerics_arch::{Simd, WithSimd};

pub(super) fn solve(
    factors: &Factors<'_, '_>,
    count: usize,
    rhs: &[f64],
    out: &mut [f64],
) -> Result<(), Error> {
    let mut batch = Batch {
        factors,
        count,
        rhs,
        out,
        start: 0,
    };
    // Cascade widths so short batches and vector-sized remainders still use
    // SIMD. No dummy lanes: a padded value could overflow at a tiny pivot.
    #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
    {
        use morphiq_numerics_arch::{Avx2, Avx512, Sse2};
        if count >= Avx512::LANES
            && let Some(k) = Avx512::try_new()
        {
            batch.start = k.vectorize(&mut batch)?;
        }
        if count - batch.start >= Avx2::LANES
            && let Some(k) = Avx2::try_new()
        {
            batch.start = k.vectorize(&mut batch)?;
        }
        if count - batch.start >= Sse2::LANES {
            batch.start = Sse2::new().vectorize(&mut batch)?;
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        batch.start = morphiq_numerics_arch::Neon::new().vectorize(&mut batch)?;
    }
    // Also type-check and exercise the generic kernel on non-vector targets.
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    )))]
    {
        batch.start = morphiq_numerics_arch::Scalar::new().vectorize(&mut batch)?;
    }
    factors.solve_columns(count, rhs, batch.out, batch.start)
}

pub(super) struct Batch<'s, 'a, 'w> {
    pub(super) factors: &'s Factors<'a, 'w>,
    pub(super) count: usize,
    pub(super) rhs: &'s [f64],
    pub(super) out: &'s mut [f64],
    pub(super) start: usize,
}

#[inline(always)]
fn load<K: Simd>(k: K, values: &[f64], at: usize) -> K::F {
    let mut array = K::Array::default();
    array.as_mut().copy_from_slice(&values[at..at + K::LANES]);
    k.load(array)
}

#[inline(always)]
fn store<K: Simd>(k: K, value: K::F, out: &mut [f64], at: usize) -> Result<(), Error> {
    if k.mask_bits(k.le(k.abs(value), k.splat(f64::MAX))) != (1 << K::LANES) - 1 {
        return Err(Error::Range);
    }
    out[at..at + K::LANES].copy_from_slice(k.store(value).as_ref());
    Ok(())
}

impl WithSimd for &mut Batch<'_, '_, '_> {
    type Output = Result<usize, Error>;
    #[inline(always)]
    fn with<K: Simd>(self, k: K) -> Self::Output {
        let n = self.factors.matrix.len();
        let end = self.start + (self.count - self.start) / K::LANES * K::LANES;
        for column in (self.start..end).step_by(K::LANES) {
            let mut previous = k.splat(0.0);
            for row in 0..n {
                let at = row * self.count + column;
                let rhs = load(k, self.rhs, at);
                let numerator = if row == 0 {
                    rhs
                } else {
                    k.sub(
                        rhs,
                        k.mul(k.splat(self.factors.matrix.lower[row - 1]), previous),
                    )
                };
                previous = k.div(numerator, k.splat(self.factors.pivots[row]));
                store(k, previous, self.out, at)?;
            }
            // `previous` is the last forward value, then the next solved row.
            for row in (0..n.saturating_sub(1)).rev() {
                let at = row * self.count + column;
                previous = k.sub(
                    load(k, self.out, at),
                    k.mul(k.splat(self.factors.normalized_upper[row]), previous),
                );
                store(k, previous, self.out, at)?;
            }
        }
        Ok(end)
    }
}
