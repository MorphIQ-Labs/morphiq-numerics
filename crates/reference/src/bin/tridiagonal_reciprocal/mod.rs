// The Thomas recurrence is adapted from FerroRisk at
// 100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c, under its MIT license.
// Copyright (c) 2026 MorphIQ Labs. See the library THIRD_PARTY_NOTICES.md.
//! Unpublished experiment. No claimed a priori forward-error bound.
//! A finite result must be certified against the original matrix and RHS.
use morphiq_numerics::linalg::tridiagonal::Error;
#[cfg(feature = "simd")]
mod lanes;

// The benchmark supplies factors from DominantTridiagonal::factor_into.
// All slices stay immutably borrowed while this private handle exists.
pub(super) struct Factors<'a> {
    pub(super) lower: &'a [f64],
    pub(super) pivots: &'a [f64],
    pub(super) normalized_upper: &'a [f64],
    pub(super) reciprocal: &'a [f64],
}

/// One extra division per pivot at setup. Zero marks an unavailable finite
/// reciprocal, never a singularity tolerance. Retain the original pivot.
pub(super) fn prepare(pivots: &[f64], reciprocal: &mut [f64]) {
    assert_eq!(pivots.len(), reciprocal.len());
    for (&p, r) in pivots.iter().zip(reciprocal) {
        assert!(p.is_finite() && p != 0.0);
        let inverse = 1.0 / p;
        *r = if inverse.is_finite() && inverse != 0.0 {
            inverse
        } else {
            0.0
        };
    }
}

impl Factors<'_> {
    pub(super) fn solve_many_into(
        &self,
        count: usize,
        rhs: &[f64],
        out: &mut [f64],
    ) -> Result<(), Error> {
        let size = self.pivots.len().checked_mul(count).ok_or(Error::Shape)?;
        if rhs.len() != size || out.len() != size {
            return Err(Error::Shape);
        }
        if rhs.iter().any(|x| !x.is_finite()) {
            return Err(Error::NonFinite);
        }
        if size == 0 {
            return Ok(());
        }
        #[cfg(feature = "simd")]
        {
            lanes::solve(self, count, rhs, out)
        }
        #[cfg(not(feature = "simd"))]
        {
            self.solve_columns(count, rhs, out, 0)
        }
    }

    fn solve_columns(
        &self,
        count: usize,
        rhs: &[f64],
        out: &mut [f64],
        start: usize,
    ) -> Result<(), Error> {
        let n = self.pivots.len();
        for column in start..count {
            for row in 0..n {
                let at = row * count + column;
                let numerator = if row == 0 {
                    rhs[at]
                } else {
                    rhs[at] - self.lower[row - 1] * out[at - count]
                };
                out[at] = if self.reciprocal[row] == 0.0 {
                    numerator / self.pivots[row]
                } else {
                    numerator * self.reciprocal[row]
                };
                if !out[at].is_finite() {
                    return Err(Error::Range);
                }
            }
            for row in (0..n.saturating_sub(1)).rev() {
                let at = row * count + column;
                out[at] -= self.normalized_upper[row] * out[at + count];
                if !out[at].is_finite() {
                    return Err(Error::Range);
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
