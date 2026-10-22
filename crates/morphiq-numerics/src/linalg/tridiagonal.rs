// The Thomas recurrence is adapted from FerroRisk at
// 100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c, under its MIT license.
// Copyright (c) 2026 MorphIQ Labs. See THIRD_PARTY_NOTICES.md in this crate.
//! Reusable Thomas factors for strictly row-diagonally-dominant matrices.
//!
//! The solve has a fixed binary64 operation order and returns a finite
//! approximation. [`ThomasFactors::certify`] separately encloses its residual
//! and absolute solution error, including underflow. A successful solve alone
//! does not promise a small forward error. See `docs/tridiagonal.md`.
//!
//! ```
//! use morphiq_numerics::linalg::tridiagonal::DominantTridiagonal;
//! let matrix = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
//! let mut pivots = [0.0; 2];
//! let mut normalized_upper = [0.0];
//! let factors = matrix.factor_into(&mut pivots, &mut normalized_upper).unwrap();
//! let mut solution = [0.0; 2];
//! factors.solve_into(&[3.0, 3.0], &mut solution).unwrap();
//! assert_eq!(solution, [1.0, 1.0]);
//! let certificate = factors.certify(&[3.0, 3.0], &solution).unwrap();
//! // Compare certificate.max_solution_error() to the caller's error budget.
//! factors.solve_into(&[0.0, 3.0], &mut solution).unwrap();
//! assert_eq!(solution, [-1.0, 2.0]);
//! ```

use crate::interval::FiniteInterval;

#[cfg(feature = "simd")]
mod lanes;

/// Failure of matrix admission, factorization, solution or certification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A coefficient, workspace, RHS or output has the wrong length.
    Shape,
    /// A matrix or vector entry is not finite.
    NonFinite,
    /// Strict row diagonal dominance could not be established at this row.
    NotDominant(usize),
    /// Elimination produced a zero pivot at this row (not a singularity proof).
    ZeroPivot(usize),
    /// Arithmetic or a required finite enclosure is unrepresentable.
    Range,
}

/// An immutable, conservatively validated strictly dominant tridiagonal matrix.
///
/// The diagonal has length `n`; lower and upper diagonals have length
/// `n.saturating_sub(1)`. All entries are finite. Admission establishes
/// `|diagonal[i]| > |lower[i-1]| + |upper[i]|`, omitting absent neighbours.
/// Near equality, conservative rounding can refuse an exactly dominant row.
#[derive(Clone, Copy, Debug)]
pub struct DominantTridiagonal<'a> {
    lower: &'a [f64],
    diagonal: &'a [f64],
    upper: &'a [f64],
    margin: f64,
}

fn point(x: f64) -> Result<FiniteInterval, Error> {
    FiniteInterval::point(x).map_err(|_| Error::NonFinite)
}

// Certificate operands have already been checked finite. Singleton products
// need one rounding and its neighbours, not four equal interval corners.
fn point_product(x: f64, y: f64) -> Result<FiniteInterval, Error> {
    let product = x * y;
    FiniteInterval::new(product.next_down(), product.next_up()).map_err(|_| Error::Range)
}

impl<'a> DominantTridiagonal<'a> {
    /// Validate dimensions, finite entries and a positive dominance margin.
    ///
    /// # Errors
    /// [`Error::Shape`], [`Error::NonFinite`] or [`Error::NotDominant`].
    /// Inputs are never modified. The empty matrix is admitted.
    pub fn new(lower: &'a [f64], diagonal: &'a [f64], upper: &'a [f64]) -> Result<Self, Error> {
        let n = diagonal.len();
        if lower.len() != n.saturating_sub(1) || upper.len() != n.saturating_sub(1) {
            return Err(Error::Shape);
        }
        if lower
            .iter()
            .chain(diagonal)
            .chain(upper)
            .any(|x| !x.is_finite())
        {
            return Err(Error::NonFinite);
        }
        let mut margin = f64::MAX;
        for (i, d) in diagonal.iter().enumerate() {
            let mut row = d.abs();
            // Skip exact zero terms so even a one-row subnormal diagonal has
            // its exact positive margin, without an unnecessary outward step.
            for a in [lower.get(i.wrapping_sub(1)), upper.get(i)]
                .into_iter()
                .flatten()
            {
                if *a != 0.0 {
                    // Only a lower bound is needed. A nonnegative row and
                    // finite |a| make the subtraction finite. Its predecessor
                    // encloses the exact difference, including underflow.
                    row = (row - a.abs()).next_down();
                    if row <= 0.0 {
                        return Err(Error::NotDominant(i));
                    }
                }
            }
            if row <= 0.0 {
                return Err(Error::NotDominant(i));
            }
            margin = margin.min(row);
        }
        Ok(Self {
            lower,
            diagonal,
            upper,
            margin: if n == 0 { 0.0 } else { margin },
        })
    }

    /// Matrix order.
    #[must_use]
    pub fn len(&self) -> usize {
        self.diagonal.len()
    }

    /// Whether the matrix has order zero.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.diagonal.is_empty()
    }

    /// A lower bound on the exact minimum row dominance margin; zero if empty.
    #[must_use]
    pub fn dominance_margin(&self) -> f64 {
        self.margin
    }

    /// Factor once into caller-owned pivots (`n`) and normalized upper (`n-1`).
    ///
    /// The returned object immutably borrows the matrix and factor storage.
    /// No matrix or factors can be changed while they are used for solving.
    ///
    /// ```compile_fail
    /// use morphiq_numerics::linalg::tridiagonal::DominantTridiagonal;
    /// let mut diagonal = [2.0];
    /// let matrix = DominantTridiagonal::new(&[], &diagonal, &[]).unwrap();
    /// let mut pivots = [0.0];
    /// let mut upper = [];
    /// let factors = matrix.factor_into(&mut pivots, &mut upper).unwrap();
    /// diagonal[0] = 3.0;
    /// factors.solve_into(&[1.0], &mut [0.0]).unwrap();
    /// ```
    ///
    /// ```compile_fail
    /// use morphiq_numerics::linalg::tridiagonal::DominantTridiagonal;
    /// let matrix = DominantTridiagonal::new(&[], &[2.0], &[]).unwrap();
    /// let mut pivots = [0.0];
    /// let factors = matrix.factor_into(&mut pivots, &mut []).unwrap();
    /// pivots[0] = 3.0;
    /// factors.solve_into(&[1.0], &mut [0.0]).unwrap();
    /// ```
    ///
    /// # Errors
    /// [`Error::Shape`] leaves storage unchanged. On [`Error::ZeroPivot`] or
    /// [`Error::Range`], storage may be partially written; no factors escape.
    pub fn factor_into<'w>(
        self,
        pivots: &'w mut [f64],
        normalized_upper: &'w mut [f64],
    ) -> Result<ThomasFactors<'a, 'w>, Error> {
        let n = self.len();
        if pivots.len() != n || normalized_upper.len() != n.saturating_sub(1) {
            return Err(Error::Shape);
        }
        for i in 0..n {
            let pivot = if i == 0 {
                self.diagonal[0]
            } else {
                self.diagonal[i] - self.lower[i - 1] * normalized_upper[i - 1]
            };
            if !pivot.is_finite() {
                return Err(Error::Range);
            }
            if pivot == 0.0 {
                return Err(Error::ZeroPivot(i));
            }
            pivots[i] = pivot;
            if i + 1 < n {
                normalized_upper[i] = self.upper[i] / pivot;
                if !normalized_upper[i].is_finite() {
                    return Err(Error::Range);
                }
            }
        }
        Ok(ThomasFactors {
            matrix: self,
            pivots,
            normalized_upper,
        })
    }
}

/// Factors tied to one immutable matrix and private, immutable factor storage.
#[derive(Debug)]
pub struct ThomasFactors<'a, 'w> {
    matrix: DominantTridiagonal<'a>,
    pivots: &'w [f64],
    normalized_upper: &'w [f64],
}

impl ThomasFactors<'_, '_> {
    /// Solve a new RHS in O(n) work without allocation or refactorization.
    ///
    /// Each multiplication, subtraction and division is separately rounded.
    /// Every output is finite on success. Use [`Self::certify`] to obtain a
    /// quantitative bound, not an assumed accuracy tolerance.
    ///
    /// # Errors
    /// [`Error::Shape`] or [`Error::NonFinite`] leaves output unchanged.
    /// [`Error::Range`] may leave a partial output, which must not be used.
    pub fn solve_into(&self, rhs: &[f64], out: &mut [f64]) -> Result<(), Error> {
        let n = self.matrix.len();
        if rhs.len() != n || out.len() != n {
            return Err(Error::Shape);
        }
        if rhs.iter().any(|x| !x.is_finite()) {
            return Err(Error::NonFinite);
        }
        for i in 0..n {
            out[i] = if i == 0 {
                rhs[i] / self.pivots[i]
            } else {
                (rhs[i] - self.matrix.lower[i - 1] * out[i - 1]) / self.pivots[i]
            };
            if !out[i].is_finite() {
                return Err(Error::Range);
            }
        }
        for i in (0..n.saturating_sub(1)).rev() {
            out[i] -= self.normalized_upper[i] * out[i + 1];
            if !out[i].is_finite() {
                return Err(Error::Range);
            }
        }
        Ok(())
    }

    /// Solve `rhs_count` right-hand sides sharing these factors.
    ///
    /// Both slices have exactly `matrix.len() * rhs_count` entries, interleaved
    /// by row: entry `(row, column)` is at `row * rhs_count + column`.
    /// Every column returns the bits of [`Self::solve_into`] on that RHS.
    /// With `simd`, independent columns run on SSE2/AVX2/AVX-512 or NEON;
    /// `std` enables runtime detection. Other builds use the scalar recurrence.
    /// No packing, allocation, refactorization or reciprocal substitution occurs.
    /// Work is O(n * rhs_count), with O(1) auxiliary storage. Zero rows or zero
    /// RHSs succeed with empty slices.
    ///
    /// ```
    /// use morphiq_numerics::linalg::tridiagonal::DominantTridiagonal;
    /// let matrix = DominantTridiagonal::new(&[1.0], &[2.0, 2.0], &[1.0]).unwrap();
    /// let mut pivots = [0.0; 2];
    /// let mut upper = [0.0];
    /// let factors = matrix.factor_into(&mut pivots, &mut upper).unwrap();
    /// let mut out = [0.0; 4];
    /// factors.solve_many_into(2, &[3.0, 0.0, 3.0, 3.0], &mut out).unwrap();
    /// assert_eq!(out, [1.0, -1.0, 1.0, 2.0]);
    /// ```
    ///
    /// # Errors
    /// [`Error::Shape`] (including dimension-product overflow) and
    /// [`Error::NonFinite`] leave the entire output unchanged. On
    /// [`Error::Range`] discard the entire output; the partially written
    /// contents and processing order are backend-dependent.
    pub fn solve_many_into(
        &self,
        rhs_count: usize,
        rhs: &[f64],
        out: &mut [f64],
    ) -> Result<(), Error> {
        let size = self
            .matrix
            .len()
            .checked_mul(rhs_count)
            .ok_or(Error::Shape)?;
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
            lanes::solve(self, rhs_count, rhs, out)
        }
        #[cfg(not(feature = "simd"))]
        {
            self.solve_columns(rhs_count, rhs, out, 0)
        }
    }

    // Same recurrence as solve_into, with interleaved RHS/output addressing.
    fn solve_columns(
        &self,
        count: usize,
        rhs: &[f64],
        out: &mut [f64],
        start: usize,
    ) -> Result<(), Error> {
        let n = self.matrix.len();
        for column in start..count {
            for row in 0..n {
                let at = row * count + column;
                out[at] = if row == 0 {
                    rhs[at] / self.pivots[0]
                } else {
                    (rhs[at] - self.matrix.lower[row - 1] * out[at - count]) / self.pivots[row]
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

    /// Enclose the residual and solution error of any finite candidate vector.
    ///
    /// If `rho` encloses `max |A*x-rhs|` and `m` is the positive dominance
    /// margin, `max |x-x_exact| <= rho/m`. This also bounds an absolute RHS
    /// perturbation making the candidate exact. It is not a condition estimate
    /// or a small relative-error promise. The O(n) check allocates nothing.
    ///
    /// # Errors
    /// [`Error::Shape`], [`Error::NonFinite`] or [`Error::Range`] if a finite
    /// outward enclosure is unavailable, even when the solution itself is finite.
    pub fn certify(&self, rhs: &[f64], candidate: &[f64]) -> Result<Certificate, Error> {
        let a = self.matrix;
        if rhs.len() != a.len() || candidate.len() != a.len() {
            return Err(Error::Shape);
        }
        if rhs.iter().chain(candidate).any(|x| !x.is_finite()) {
            return Err(Error::NonFinite);
        }
        if a.is_empty() {
            return Ok(Certificate {
                residual: 0.0,
                error: 0.0,
            });
        }
        let mut residual: f64 = 0.0;
        for i in 0..a.len() {
            let mut row = point_product(a.diagonal[i], candidate[i])?;
            if i > 0 {
                let term = point_product(a.lower[i - 1], candidate[i - 1])?;
                row = row.checked_add(term).map_err(|_| Error::Range)?;
            }
            if i + 1 < a.len() {
                let term = point_product(a.upper[i], candidate[i + 1])?;
                row = row.checked_add(term).map_err(|_| Error::Range)?;
            }
            row = row.checked_sub(point(rhs[i])?).map_err(|_| Error::Range)?;
            residual = residual.max(row.abs().upper());
        }
        // Direct positive division avoids an overflowing reciprocal for tiny
        // margins. The successor encloses rounding, including underflow.
        let error = (residual / a.margin).next_up();
        if !error.is_finite() {
            return Err(Error::Range);
        }
        Ok(Certificate { residual, error })
    }
}

/// Conservative absolute bounds for one matrix/RHS/candidate combination.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Certificate {
    residual: f64,
    error: f64,
}

impl Certificate {
    /// Upper bound on `max |A*x-rhs|`, also an absolute RHS backward-error bound.
    #[must_use]
    pub fn max_residual(&self) -> f64 {
        self.residual
    }
    /// Upper bound on `max |x-x_exact|` for the exact binary64 input system.
    #[must_use]
    pub fn max_solution_error(&self) -> f64 {
        self.error
    }
}

#[cfg(test)]
mod tests;
