// The Thomas recurrence is adapted from FerroRisk at
// 100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c, under its MIT license.
// Copyright (c) 2026 MorphIQ Labs. See THIRD_PARTY_NOTICES.md in this crate.
//! Reusable Thomas factors with explicit dominant, sign and unpivoted contracts.
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
    /// The sign domain requires a strictly positive diagonal at this row.
    NonPositiveDiagonal(usize),
    /// Both nonzero entries of this adjacent lower/upper link have the same sign.
    SameSignLink(usize),
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
        let matrix = Coefficients {
            lower: self.lower,
            diagonal: self.diagonal,
            upper: self.upper,
        };
        Ok(ThomasFactors {
            factors: matrix.factor_into(pivots, normalized_upper)?,
            margin: self.margin,
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct Coefficients<'a> {
    lower: &'a [f64],
    diagonal: &'a [f64],
    upper: &'a [f64],
}

impl<'a> Coefficients<'a> {
    fn len(self) -> usize {
        self.diagonal.len()
    }

    fn factor_into<'w>(
        self,
        pivots: &'w mut [f64],
        normalized_upper: &'w mut [f64],
    ) -> Result<Factors<'a, 'w>, Error> {
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
        Ok(Factors {
            matrix: self,
            pivots,
            normalized_upper,
        })
    }
}

/// Positive diagonal and nonpositive exact products of matching off-diagonals.
///
/// All coefficients are finite; `diagonal[i] > 0` and
/// `lower[i] * upper[i] <= 0` over exact reals. Admission checks signs without
/// multiplying, so overflow/underflow cannot hide a positive product. Either
/// signed zero is allowed in a link. This domain need not be row dominant.
/// Exact Thomas pivots are positive, but finite-range arithmetic can refuse.
/// No forward-error or conditioning bound is implied.
#[derive(Clone, Copy, Debug)]
pub struct SignTridiagonal<'a> {
    matrix: Coefficients<'a>,
}

impl<'a> SignTridiagonal<'a> {
    /// Check n/n-1 dimensions, finiteness, positive diagonal and link signs.
    /// The empty matrix is admitted. Inputs are never modified.
    ///
    /// # Errors
    /// [`Error::Shape`], [`Error::NonFinite`], [`Error::NonPositiveDiagonal`]
    /// (row index) or [`Error::SameSignLink`] (off-diagonal index).
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
        for (i, &d) in diagonal.iter().enumerate() {
            if d <= 0.0 {
                return Err(Error::NonPositiveDiagonal(i));
            }
        }
        for (i, (&l, &u)) in lower.iter().zip(upper).enumerate() {
            if l != 0.0 && u != 0.0 && l.is_sign_negative() == u.is_sign_negative() {
                return Err(Error::SameSignLink(i));
            }
        }
        Ok(Self {
            matrix: Coefficients {
                lower,
                diagonal,
                upper,
            },
        })
    }

    /// Matrix order.
    #[must_use]
    pub fn len(&self) -> usize {
        self.matrix.len()
    }

    /// Whether the matrix has order zero.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Factor into immutable borrowed pivots (n) and normalized upper (n-1).
    /// Uses exactly the same division/multiplication/subtraction recurrence as
    /// [`DominantTridiagonal::factor_into`]. No automatic algorithm fallback.
    ///
    /// # Errors
    /// [`Error::Shape`] leaves storage unchanged. [`Error::Range`] may leave
    /// partial storage; no factors escape. Positive pivots cannot round to
    /// zero in this domain under the prescribed gradual-underflow arithmetic.
    pub fn factor_into<'w>(
        self,
        pivots: &'w mut [f64],
        normalized_upper: &'w mut [f64],
    ) -> Result<SignThomasFactors<'a, 'w>, Error> {
        Ok(SignThomasFactors {
            factors: self.matrix.factor_into(pivots, normalized_upper)?,
        })
    }
}

/// Finite tridiagonal coefficients for checked, unpivoted Thomas elimination.
///
/// Admission checks only n/n-1 shapes and finite entries, not nonsingularity,
/// conditioning or stability. Factorization can refuse a nonsingular matrix
/// (for example one with a zero leading pivot). Rounded factorization success
/// does not establish exact nonsingularity. Use a pivoted solver when required.
/// Negative pivots are allowed. No automatic fallback or forward-error bound.
#[derive(Clone, Copy, Debug)]
pub struct UnpivotedTridiagonal<'a> {
    matrix: Coefficients<'a>,
}

impl<'a> UnpivotedTridiagonal<'a> {
    /// Validate compact dimensions and finite coefficients; allow empty matrices.
    /// Zero diagonals are admitted here and checked during elimination.
    ///
    /// # Errors
    /// [`Error::Shape`] or [`Error::NonFinite`]. Inputs remain unchanged.
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
        Ok(Self {
            matrix: Coefficients {
                lower,
                diagonal,
                upper,
            },
        })
    }

    /// Matrix order.
    #[must_use]
    pub fn len(&self) -> usize {
        self.matrix.len()
    }

    /// Whether the matrix has order zero.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Factor using the shared fixed-order recurrence, in O(n) without allocation.
    /// Pivots have length n and normalized upper length n-1 (zero when empty).
    /// Successful factors contain only finite entries and nonzero pivots.
    /// This is a finite-computation check, not a stability certificate.
    ///
    /// # Errors
    /// [`Error::Shape`] leaves storage unchanged. [`Error::ZeroPivot`] or
    /// [`Error::Range`] may leave partial storage; no factors escape on failure.
    pub fn factor_into<'w>(
        self,
        pivots: &'w mut [f64],
        normalized_upper: &'w mut [f64],
    ) -> Result<UnpivotedThomasFactors<'a, 'w>, Error> {
        Ok(UnpivotedThomasFactors {
            factors: self.matrix.factor_into(pivots, normalized_upper)?,
        })
    }
}

/// Immutable checked factors with residual-only certification.
///
/// A solve returns a finite approximation; useful accuracy is not guaranteed.
/// Matrix and factor borrows prevent stale/mismatched storage without copying.
///
/// ```
/// use morphiq_numerics::linalg::tridiagonal::UnpivotedTridiagonal;
/// let matrix = UnpivotedTridiagonal::new(&[1.0], &[1.0, 0.0], &[1.0]).unwrap();
/// let mut p = [0.0; 2];
/// let mut u = [0.0];
/// let f = matrix.factor_into(&mut p, &mut u).unwrap();
/// let mut x = [0.0; 2];
/// f.solve_into(&[1.0, 2.0], &mut x).unwrap();
/// assert_eq!(x, [2.0, -1.0]);
/// assert_eq!(f.min_abs_pivot(), Some(1.0));
/// assert!(f.certify_residual(&[1.0, 2.0], &x).unwrap().max_residual().is_finite());
/// ```
///
/// ```compile_fail
/// use morphiq_numerics::linalg::tridiagonal::UnpivotedTridiagonal;
/// let mut p = [0.0];
/// let f = UnpivotedTridiagonal::new(&[], &[1.0], &[]).unwrap()
///     .factor_into(&mut p, &mut []).unwrap();
/// f.certify(&[1.0], &[1.0]); // no dominance evidence
/// ```
///
/// ```compile_fail
/// use morphiq_numerics::linalg::tridiagonal::UnpivotedTridiagonal;
/// let mut p = [0.0];
/// let f = UnpivotedTridiagonal::new(&[], &[1.0], &[]).unwrap()
///     .factor_into(&mut p, &mut []).unwrap();
/// p[0] = 2.0;
/// f.solve_into(&[1.0], &mut [0.0]).unwrap();
/// ```
#[derive(Debug)]
pub struct UnpivotedThomasFactors<'a, 'w> {
    factors: Factors<'a, 'w>,
}

impl UnpivotedThomasFactors<'_, '_> {
    /// Smallest absolute computed pivot, or None for an empty matrix.
    /// O(n), allocation-free, with no rounding beyond exact absolute value.
    /// This is not a condition estimate, exact-pivot bound or singularity test.
    #[must_use]
    pub fn min_abs_pivot(&self) -> Option<f64> {
        self.factors.pivots.iter().map(|p| p.abs()).reduce(f64::min)
    }

    /// Shared O(n), allocation-free fixed-order solve; finite output on success.
    /// See [`ThomasFactors::solve_into`] for the arithmetic order.
    ///
    /// # Errors
    /// [`Error::Shape`] and [`Error::NonFinite`] leave output unchanged;
    /// [`Error::Range`] invalidates the entire partially written output.
    pub fn solve_into(&self, rhs: &[f64], out: &mut [f64]) -> Result<(), Error> {
        self.factors.solve_into(rhs, out)
    }

    /// Shared scalar/SIMD row-interleaved solve, bit-identical per RHS.
    /// Layout and complexity follow [`ThomasFactors::solve_many_into`].
    ///
    /// # Errors
    /// [`Error::Shape`] (including size overflow) and [`Error::NonFinite`] leave
    /// output unchanged. [`Error::Range`] invalidates the entire output; partial
    /// contents depend on backend traversal. Empty batches succeed.
    pub fn solve_many_into(
        &self,
        rhs_count: usize,
        rhs: &[f64],
        out: &mut [f64],
    ) -> Result<(), Error> {
        self.factors.solve_many_into(rhs_count, rhs, out)
    }

    /// Enclose max |A*x-rhs| for any finite candidate in O(n), without allocation.
    /// An absolute RHS backward-error enclosure, not a solution-error bound.
    ///
    /// # Errors
    /// [`Error::Shape`], [`Error::NonFinite`] or [`Error::Range`] if no finite
    /// outward enclosure is representable, even after a successful solve.
    pub fn certify_residual(
        &self,
        rhs: &[f64],
        candidate: &[f64],
    ) -> Result<ResidualCertificate, Error> {
        self.factors.certify_residual(rhs, candidate)
    }
}

/// Factors tied to one immutable matrix and private, immutable factor storage.
#[derive(Debug)]
struct Factors<'a, 'w> {
    matrix: Coefficients<'a>,
    pivots: &'w [f64],
    normalized_upper: &'w [f64],
}

impl Factors<'_, '_> {
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

    fn certify_residual(
        &self,
        rhs: &[f64],
        candidate: &[f64],
    ) -> Result<ResidualCertificate, Error> {
        let a = self.matrix;
        if rhs.len() != a.len() || candidate.len() != a.len() {
            return Err(Error::Shape);
        }
        if rhs.iter().chain(candidate).any(|x| !x.is_finite()) {
            return Err(Error::NonFinite);
        }
        if a.len() == 0 {
            return Ok(ResidualCertificate { residual: 0.0 });
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
        Ok(ResidualCertificate { residual })
    }
}

/// Factors carrying a strict dominance margin and a solution-error certificate.
#[derive(Debug)]
pub struct ThomasFactors<'a, 'w> {
    factors: Factors<'a, 'w>,
    margin: f64,
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
        self.factors.solve_into(rhs, out)
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
        self.factors.solve_many_into(rhs_count, rhs, out)
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
        let residual = self.factors.certify_residual(rhs, candidate)?.residual;
        if self.factors.matrix.len() == 0 {
            return Ok(Certificate {
                residual,
                error: 0.0,
            });
        }
        // Direct positive division avoids an overflowing reciprocal for tiny
        // margins. The successor encloses rounding, including underflow.
        let error = (residual / self.margin).next_up();
        if !error.is_finite() {
            return Err(Error::Range);
        }
        Ok(Certificate { residual, error })
    }
}

/// Factors for the sign domain, with residual-only certification.
///
/// The private matrix/factor borrows prevent stale or mismatched factors.
/// The dominance-only solution-error certificate is deliberately unavailable.
///
/// ```
/// use morphiq_numerics::linalg::tridiagonal::SignTridiagonal;
/// let matrix = SignTridiagonal::new(&[-3.0; 2], &[2.0; 3], &[3.0; 2]).unwrap();
/// let mut pivots = [0.0; 3];
/// let mut upper = [0.0; 2];
/// let factors = matrix.factor_into(&mut pivots, &mut upper).unwrap();
/// let mut out = [0.0; 3];
/// factors.solve_into(&[-4.0, 2.0, 12.0], &mut out).unwrap();
/// let residual = factors.certify_residual(&[-4.0, 2.0, 12.0], &out).unwrap();
/// assert!(residual.max_residual().is_finite());
/// ```
///
/// ```compile_fail
/// use morphiq_numerics::linalg::tridiagonal::SignTridiagonal;
/// let mut p = [0.0];
/// let f = SignTridiagonal::new(&[], &[1.0], &[]).unwrap()
///     .factor_into(&mut p, &mut []).unwrap();
/// f.certify(&[1.0], &[1.0]); // no dominance evidence
/// ```
///
/// ```compile_fail
/// use morphiq_numerics::linalg::tridiagonal::SignTridiagonal;
/// let mut diagonal = [1.0];
/// let mut p = [0.0];
/// let f = SignTridiagonal::new(&[], &diagonal, &[]).unwrap()
///     .factor_into(&mut p, &mut []).unwrap();
/// diagonal[0] = 2.0;
/// f.solve_into(&[1.0], &mut [0.0]).unwrap();
/// ```
#[derive(Debug)]
pub struct SignThomasFactors<'a, 'w> {
    factors: Factors<'a, 'w>,
}

impl SignThomasFactors<'_, '_> {
    /// Finite fixed-order approximation using the shared Thomas recurrence.
    /// Same operation order and O(n) allocation-free work as
    /// [`ThomasFactors::solve_into`]; no forward-error guarantee.
    ///
    /// # Errors
    /// [`Error::Shape`] and [`Error::NonFinite`] leave output unchanged;
    /// [`Error::Range`] invalidates the entire partially written output.
    pub fn solve_into(&self, rhs: &[f64], out: &mut [f64]) -> Result<(), Error> {
        self.factors.solve_into(rhs, out)
    }

    /// Solve row-interleaved RHS columns using the shared scalar/SIMD kernel.
    /// Layout, complexity and bit equality follow [`ThomasFactors::solve_many_into`].
    ///
    /// # Errors
    /// [`Error::Shape`] (including size overflow) and [`Error::NonFinite`] leave
    /// output unchanged. [`Error::Range`] invalidates the entire output, whose
    /// partial contents depend on backend traversal. Empty batches succeed.
    pub fn solve_many_into(
        &self,
        rhs_count: usize,
        rhs: &[f64],
        out: &mut [f64],
    ) -> Result<(), Error> {
        self.factors.solve_many_into(rhs_count, rhs, out)
    }

    /// Enclose `max |A*x-rhs|` for any finite candidate in O(n), without allocation.
    /// This bounds an absolute RHS perturbation making the candidate exact;
    /// it does not bound solution error. The original matrix is used.
    ///
    /// # Errors
    /// [`Error::Shape`], [`Error::NonFinite`] or [`Error::Range`] if a finite
    /// outward residual enclosure is unavailable, even after a successful solve.
    pub fn certify_residual(
        &self,
        rhs: &[f64],
        candidate: &[f64],
    ) -> Result<ResidualCertificate, Error> {
        self.factors.certify_residual(rhs, candidate)
    }
}

/// Absolute RHS backward-error enclosure, without a solution-error bound.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ResidualCertificate {
    residual: f64,
}

impl ResidualCertificate {
    /// Upper bound on the exact `max |A*x-rhs|` for the supplied candidate.
    #[must_use]
    pub fn max_residual(&self) -> f64 {
        self.residual
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
