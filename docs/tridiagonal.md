# Strictly dominant tridiagonal systems

`linalg::tridiagonal` separates checked matrix admission, Thomas factorization,
repeated RHS solves, and a posteriori certification. All four operations are
O(n), allocation-free, safe Rust and `no_std`. They use binary64 operations in
a fixed order, without fused multiply-add or reciprocal substitution. Features
do not change their bits. The solution is **not** claimed correctly rounded.

## Domain and ownership

`DominantTridiagonal::new(lower, diagonal, upper)` takes an n-element diagonal
and two n−1-element off-diagonals (both empty for n=0). `lower[i]` is A[i+1,i];
`upper[i]` is A[i,i+1]. There are no ignored sentinel coefficients. All entries
must be finite. Each row must satisfy strict **row** diagonal dominance:

    |d[i]| − |l[i−1]| − |u[i]| > 0

Absent neighbours contribute zero. Starting with `abs(d[i])`, subtract each
nonzero neighbour magnitude and take `next_down` after each subtraction. This
establishes a lower bound on the exact row margin using only its needed lower
endpoint. Reject a nonpositive intermediate bound; otherwise m is the minimum
row bound. Exact zero neighbours are skipped. Near the boundary, a strictly dominant matrix can be refused if
its positive margin cannot be enclosed above zero. Signs need not be positive
or form an M-matrix. An empty matrix is admitted with margin zero. A one-row
matrix admits every finite nonzero diagonal, including the least subnormal.

Strict dominance implies nonsingularity over the reals. It does not guarantee
well conditioning, representable factors, or an accurate floating-point solve.
Nonsingular matrices outside this domain, including ones that require a row
interchange, return `NotDominant(row)`. This API is not a general pivoted solver.

`factor_into` takes exactly n pivots and n−1 normalized upper coefficients.
The resulting opaque `ThomasFactors` immutably borrows both the complete matrix
and factor storage. Safe Rust prevents modification of either while the factors
are in use. `solve_into` accepts only a new RHS and output, both exactly n long;
it cannot be passed an unrelated matrix. Mutable output cannot overlap the RHS,
matrix or factors. New coefficients require admission and factorization again.
No pointer identity or matrix hash substitutes for equality. There is no hidden
cache, allocation, one-shot duplicate algorithm or automatic pivoted fallback.

## Fixed-order recurrence

Each displayed multiplication, subtraction and division rounds separately to
nearest binary64, ties to even:

    p[0] = d[0]
    c[0] = u[0] / p[0]                     (if n > 1)
    p[i] = d[i] − l[i−1] * c[i−1]
    c[i] = u[i] / p[i]                     (if i < n−1)

    y[0] = rhs[0] / p[0]
    y[i] = (rhs[i] − l[i−1] * y[i−1]) / p[i]
    y[i] = y[i] − c[i] * y[i+1]           (i = n−2 down to 0)

Factorization uses n−1 multiplies, subtracts and divides. A solve uses n divides,
2(n−1) multiplies and 2(n−1) subtracts. There is no factorization in the solve
path. Input finiteness checks are additional linear passes. Factor storage is
8(2n−1) bytes for n>0; output is 8n bytes. The matrix and RHS remain caller-owned.
The handles have only slice descriptors and a margin; auxiliary stack is O(1).

Underflow, including a rounded zero coefficient or solution component, follows
IEEE binary64 gradual underflow. Signed zero follows the stated operation order.
There is no absolute pivot tolerance. A zero eliminated pivot returns
`ZeroPivot(row)`; a nonfinite factor/intermediate/output returns `Range`. These
are failures of this floating-point algorithm, not proofs that A is singular.
Overflow before cancellation is rejected even if the exact result is finite.
Flushing subnormals or changing the rounding mode is outside the contract.

`Shape` and `NonFinite` failures are detected before writes. Factorization or
solve arithmetic failures can leave partially written buffers; discard those
contents. No factors escape a failed factorization. No operation changes matrix
or RHS entries. Empty operations succeed without indexing a buffer.

## SIMD across right-hand sides

`ThomasFactors::solve_many_into(rhs_count, rhs, out)` solves multiple RHSs
against the same factors. Slices have exactly `n * rhs_count` entries, interleaved
by row: `(row, column)` lives at `row * rhs_count + column`. This layout permits
contiguous lane loads/stores without allocation or packing inside the API.
Factorization is still performed once, using the scalar API. Certification is
still per vector; callers can gather a column into their own storage to certify it.
Different matrices require separate factor objects and calls.

With `simd`, the existing safe lane layer executes independent RHS columns on
SSE2 (2 lanes), AVX2 (4), AVX-512F (8), or ARM NEON (2). With `std`, availability
is detected at runtime; otherwise target features determine availability.
Dispatch cascades from wider to narrower available backends, then uses scalar
code for the final column. Without SIMD, every column uses the scalar recurrence.
No rows are parallelized, and no reciprocal or FMA replaces a scalar operation.
There are no padded lanes whose artificial values might cause a range failure.

The per-lane equivalence argument is induction on the forward row, followed by
reverse induction on the backward row: a lane starts with the same RHS/pivot,
then applies the same separately rounded multiply, subtract and divide to the
same previous lane value and shared coefficients. The row-interleaved address
maps only that RHS into its lane. Thus every successful column has exactly the
`solve_into` bits, including signed zero and gradual underflow. Existing lane
primitive contracts supply the arithmetic premise. This is a source-level
argument supported by forced-backend tests and the cross-target digest, not an
extracted/compiler-verified SIMD proof. The scalar certificate theorem applies
to each finite column independently, without a new accuracy claim.

Dimensions use checked multiplication. Shape and nonfinite-input errors leave
the entire output untouched. Any nonfinite intermediate lane returns `Range`;
all output must then be discarded, because partial writes and traversal order
can differ by backend. Zero RHSs or zero rows succeed with empty slices. Total
work is O(n * rhs_count), output is 8*n*rhs_count bytes, and auxiliary storage
is bounded by the backend width. Shared factor storage does not grow with the
batch size. The API does not allocate or change any scalar entry point's bits.

Exact manufactured systems test distinct columns and row boundaries. Independent
rational fixtures check batched solutions against their exact bounds. Forced
backend tests compare scalar bits at short, full-width and remainder sizes,
including mixed signs, subnormals and range failures. The benchmark's `--batches`
mode compares the batched API with independent scalar calls on the same RHSs;
both interleaved and column-contiguous layouts are prepared before timing, so
packing costs are excluded and must be measured separately by consumers that
need conversion. SIMD implementation is not a native speedup claim.

## Numerical certificate

`solve_into` returns a finite fixed-order approximation on success. It does not
by itself promise a useful error bound. `ThomasFactors::certify(rhs, candidate)`
separately supplies an absolute bound for **any** finite candidate x, whether
produced by this solver or elsewhere. Using the exact binary64 input values as
real numbers, it encloses each point product with the predecessor and successor
of its rounded value, then combines these finite intervals with `FiniteInterval`
sums and subtraction. A point product needs one multiply, rather than four
identical interval corners; it has the same enclosure. Let ρ be the largest
absolute residual endpoint. Then:

    max_i |(A*x − rhs)[i]| ≤ ρ
    max_i |x[i] − x_exact[i]| ≤ ρ / m

The returned solution bound is `next_up(round_nearest(ρ/m))`. Direct division
avoids an unnecessary reciprocal overflow for a tiny m. Outward neighbours
account for underflow and cancellation; the result is conservative, not tight.
The empty certificate is exactly (0,0). Any unrepresentable finite interval
endpoint or final bound returns `Range`, even if x itself is finite.

The first inequality is also an **absolute RHS backward-error bound**: x solves
`A*x = rhs + r` with `max |r| ≤ ρ`. It is not a componentwise relative backward
error or a condition-number estimate. A small residual need not imply a small
solution error when m is small. Consumers must compare the returned bound to
their own absolute error budgets; they must not interpret success as acceptance.
Certifying every solve costs another O(n) pass and is measured separately.

To derive the second inequality, set e=x−x_exact and choose a row k attaining
`E=max |e[i]|`. Triangle inequalities give

    |(A*e)[k]| ≥ (|d[k]| − |l[k−1]| − |u[k]|) E ≥ m E.

Thus E≤ρ/m. The same argument with zero residual proves a zero nullspace;
finite-dimensional square-matrix injectivity gives existence and uniqueness.
This argument requires no relative-error model or normal-only arithmetic and
does not depend on the accuracy of the Thomas recurrence.

`formal/binary64/Tridiagonal.v` proves conservative subtraction of neighbour magnitudes, the maximum-row argument, existence of a
maximum over the finite error vector, the global error inequality, zero kernel,
and outward rounding of the final quotient. `FiniteInterval.v` supplies real
enclosure lemmas including binary64 neighbour rounding. The proof does not
extract the Rust solver, prove finite-dimensional surjectivity, or promise
that every admitted system factors/solves/certifies successfully. The
source-binding manifest and independent tests connect the documented primitive
sequence to these real-arithmetic theorems; they are not a compiler proof.

## Independent evidence and alternatives

`generators/tridiagonal_reference.py` uses exact Python `Fraction` arithmetic
and dense Gauss–Jordan elimination with row pivoting, independently of Thomas.
It generates exact rational solutions for generic systems and exact manufactured
solutions for the long case. The reference tests compare returned certificates
to exact integer arithmetic, without a rounded test tolerance. Tests cover
empty/single/short/long cases, mixed signs, subnormal and power-of-two scaling,
near-dominance, unequal row scales, repeated RHSs, unsupported/singular inputs,
NaN/infinity, signed zero, and range failures. Compile-fail examples enforce
matrix/factor immutability. The determinism corpus records solutions,
certificates and admission/solve errors across targets and feature configurations.

The established general alternative is LAPACK's pivoted
[DGTTRF/DGTTRS](https://netlib.org/lapack/lug/node38.html), with row pivots and a
second superdiagonal. It supports matrices outside the domain here; it does not
return this certificate or promise the same bits. LAPACK 3.12.1 is a diagnostic
performance comparator, not an accuracy-equivalent parity gate. The normalized
Thomas baseline has matching arithmetic but fewer checks and no certificate.
Dense LU from faer is a different complexity/cost comparison, and is not added
as a runtime dependency. Parallel cyclic reduction changes operation order;
reciprocal pivots change rounding. Neither is part of this API.

The recurrence is adapted from the original MIT FerroRisk kernel at
`100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c`, with factor/solve separation,
compact off-diagonals, explicit domain/range checks and a separate certificate.
The crate's `THIRD_PARTY_NOTICES.md` records the exact source, hash and license.
No later private consumer implementation or data is included. The error-bound
derivation above is self-contained; see also R. S. Varga,
[*Matrix Iterative Analysis*, 2nd ed., Springer (2000)](https://link.springer.com/book/10.1007/978-3-642-05156-2)
for background on matrix properties and iterative methods.

Native performance protocols, raw samples and qualification belong to #152
under performance epic #149. Implementation and release tracking belong to #219
and its pull request. Consumer adoption requires separate
qualification of matrix coverage and composed numerical error.
