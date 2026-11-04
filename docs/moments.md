# Mergeable compensated moments

`reduce::Moments2` accumulates exact binary64 observations using constant
storage and no allocation. `push` adds an observation; `merge` combines two
accumulators. `count` is exact through `2^53`. Readouts return a
`MomentEstimate` with finite `value()` and nonnegative finite
`absolute_error()`:

| Readout | Exact statistic enclosed by `value ± absolute_error` |
| --- | --- |
| `mean` | `μ = Σxᵢ / n` |
| `variance` | `v = Σ(xᵢ − μ)² / (n − 1)` |
| `standard_error` | `sqrt(v / n)` |

The bound describes arithmetic error, not sampling uncertainty. The standard
error's statistical interpretation depends on the caller's sampling model.
For antithetic Monte Carlo, observations are pair means, not individual paths.
An existing price sum need not use this accumulator's mean: consumers preserving
old price bits keep their existing summation path and use this type for dispersion.

## Numerical contract and failures

The returned error bound is computed for the actual operation sequence. There
is no uniform relative-error or correctly-rounded-output claim. A caller with
an accuracy budget must check the returned bound against that budget; success
does not mean that every possible consumer accuracy requirement is met.

All zero readouts are positive zero. A mean of an empty sample returns `Empty`;
variance and standard error with fewer than two samples return
`InsufficientSamples`. `push` refuses NaNs and infinities with
`NonFiniteSample`. A count above `2^53` returns `CountOverflow`; integer counts
and their conversions to binary64 are therefore exact on every target.

Every nontrivial double-word operation uses its existing checked form.
`Arithmetic(CheckError)` means its operands did not satisfy that operation's
[proved domain](double-word.md#checked-operations). This can occur for finite
observations, including overflowing differences, very small squared deviations,
or quotient exponent spans outside the existing theorem. Exact-zero identities
are evaluated directly, so constant samples remain supported even at extreme
finite magnitudes. A finite error radius or square-root enclosure that cannot
be represented returns `Range`. There is no fallback or silent underflow-to-zero
rule. Admission, as well as rounding, can depend on batch boundaries and order.

Failed updates and merges preserve the entire receiver. The right operand of
a merge is always unchanged. Empty accumulators are merge identities.
Readouts never mutate state. Counts, anchors, words, and radii are private;
callers cannot construct an invalid state or an invalid returned certificate.

**Determinism:** the input sequence within each batch, batch boundaries, and
ordered sequence of merges are part of the contract. The same operations give
the same values, error bounds, and refusals on every target. Workers may compute
fixed batches in any schedule, then merge them in the specified order. Changing
the partition or merge order need not preserve bits. No SIMD or parallel
scheduler is introduced by this type.

## Representation and identities

Retain the first admitted sample `a` as an anchor and accumulate

```
S = Σ(xᵢ − a)
Q = Σ(xᵢ − a)²
μ = a + S/n
M₂ = Q − S²/n
```

`S` and `Q` each have a double-word centre and an absolute error radius.
Subtracting the sample anchor with checked TwoSum recovers the difference
exactly. In particular, a large mean does not erase a small spread before the
compensated arithmetic begins. Each update performs one exact difference, two
double-word additions, and one double-word product, plus the radius operations.
There is no division per observation.

To merge B into A, retain A's anchor and let `d = a_B − a_A`:

```
S_B' = S_B + n_B*d
Q_B' = Q_B + 2*d*S_B + n_B*d²
S_new = S_A + S_B'
Q_new = Q_A + Q_B'
```

These are exact real-arithmetic identities. They imply the Chan combination
`M₂_new = M₂_A + M₂_B + (μ_B−μ_A)²*n_A*n_B/(n_A+n_B)`.
The implementation evaluates the anchored-sum identities in the stated order,
not the floating-point Welford recurrence. Welford/Chan was considered as a
candidate; the anchored sums avoid a division in every streaming update while
retaining a separately propagated bound through cancellation and anchor changes.
The formulas follow from expanding a square; no external implementation was used.

Sources for the statistical context and competing recurrences:

- B. P. Welford, “Note on a Method for Calculating Corrected Sums of Squares
  and Products,” *Technometrics* 4(3), 1962,
  [doi:10.1080/00401706.1962.10490022](https://doi.org/10.1080/00401706.1962.10490022).
- T. F. Chan, G. H. Golub, R. J. LeVeque, “Algorithms for Computing the Sample
  Variance: Analysis and Recommendations,” *The American Statistician* 37(3),
  1983, [doi:10.1080/00031305.1983.10483115](https://doi.org/10.1080/00031305.1983.10483115).

## Error propagation

A private bounded value `(c,e)` represents an exact quantity `x` with
`|c−x| <= e`, where `c = hi+lo`. Let `A` and `B` be upper bounds on the absolute
values of two stored centres, and `e_a,e_b` their radii. Before local arithmetic
rounding, valid propagated radii are:

| Operation on centres | Propagated radius |
| --- | --- |
| addition or subtraction | `e_a + e_b` |
| multiplication | `A*e_b + B*e_a + e_a*e_b` |
| division by exact positive count `n` | `e_a/n` |

For the local operation, let `r` be its returned double-word centre. If
`|r−z| <= ε|z|` with `0 <= ε <= 1/2`, then `|r−z| <= 2ε|r|`.
The existing checked double-word theorems give, for `u=2^-53`,
`ε < 4u²` for addition/subtraction, `ε <= 5u²` for multiplication, and
`ε <= 3u²` for division by binary64. Consequently the local radii are bounded by
`8u²|r|`, `10u²|r|`, and `6u²|r|`, respectively. The code expresses these exact
constants as `2`, `2.5`, or `1.5` times `f64::EPSILON²`, since `EPSILON=2u`.
They are theorem-derived powers of two and exact binary fractions, not fitted
coefficients or generated approximation tables.

All radius sums, products, and quotients round outward with `next_up` after
nearest-even rounding. Exact-zero identities retain zero. This includes
underflow: a positive exact error rounded to zero is widened to `2^-1074`.
Overflowing outward neighbours are refused. The magnitude bound is an outward
sum of `abs(hi)` and `abs(lo)`. Adding the propagated and local radii preserves
the enclosure inductively. Rounding a stored centre to its leading word adds
`abs(lo)` to the final radius.

Variance and squared standard error are nonnegative exact statistics. Projecting
a negative estimate to zero cannot increase its distance from that statistic;
the radius is retained. For standard error, the nonnegative interval formed
from the squared estimate and its radius is passed through the existing
`FiniteInterval::checked_sqrt`. The returned centre uses the correctly rounded
scalar square root, and the radius covers both outward interval endpoints.

## Proof boundary and checks

`formal/binary64/Moments.v` proves the exact anchored sums, concatenation and
anchor-translation identities, their mean and centred-second-moment readouts,
nonnegativity, the Chan identity, and the real error-propagation rules above.
Primitive double-word guarantees come from the existing checked arithmetic
proofs. Outward rounding and square-root propagation use the existing
[finite-interval](interval.md) contract. This is a real-arithmetic composition
proof, not a machine-checked translation of Rust control flow or an addition to
the OCaml extraction corpus. Rust-to-proof correspondence remains a reviewed
source binding with independent numerical and cross-target checks.

`crates/reference/tests/moments.rs` independently evaluates sums and squares
in exact integer arithmetic, clearing denominators before testing the returned
mean and variance bounds. It squares standard-error interval endpoints before
comparison, so no approximate square-root oracle is used there. Tests cover
large means with small spreads, signs, constant data, multiple partitions,
ordered merging across native worker counts and portable completion orders,
invalid inputs, count limits, zero signs,
and transactional refusals. Different partitions are checked against the exact
statistic, not required to match each other's bits.

`fuzz/src/moments.rs` also compares all three readouts with independently
directed MPFR intervals at 8,192-bit precision, including oracle negative
controls. The determinism digest records update and merge refusals, counts,
and every readout value and error bound across the supported target matrix.

## Accuracy and cost decision

The selected public contract is a finite, explicit absolute error enclosure
using compensated arithmetic. It separates arithmetic error from the consumer's
sampling error budget. Storage is constant: a count, an anchor, two double words,
and two radii; there are no retained observations or heap allocations.
Updates and merges have bounded constant work and no refinement or fallback.

The comparable design candidate is checked shifted Welford/Chan with the same
error-propagation rules. Ordinary Welford and compensated two-pass reductions
are diagnostic references with different certificate/storage contracts.
The reproducible [native comparison protocol](../scripts/bench_moments/README.md)
records dependent latency, independent throughput, merge/readout costs, and exact
error observations for the timed populations. Host-specific results and
qualification belong to
[#285](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/285).
No engine end-to-end performance or adoption claim is made here.
