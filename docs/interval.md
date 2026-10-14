# Finite binary64 intervals

`interval::FiniteInterval` encloses real values between two ordered, finite
binary64 endpoints. It provides conservative interval arithmetic, not the
narrowest directed-rounded result. Endpoint fields are private. `new` rejects
nonfinite or reversed bounds, and `point` represents an exact finite input.
Inputs are the exact reals represented by their binary64 encodings; this does
not account for uncertainty in how a caller obtained those inputs.

## Contract

For every real input inside each supplied interval, a successful operation
contains its exact mathematical result. The implementation uses round to
nearest, ties to even, followed by one representable neighbour outward at
each inexact endpoint. Exact arithmetic results are widened too. This
avoids changes to the process rounding mode, uses no allocation, and works
under `no_std` with the same operation sequence on every target.

| Operation | Endpoint construction before outward widening | Domain |
| --- | --- | --- |
| `checked_add` | `[l+a, u+b]` | all finite intervals |
| `checked_sub` | `[l-b, u-a]` | all finite intervals |
| `checked_mul` | hull of the four corner products | all finite intervals |
| `checked_div` | widen `[1/b, 1/a]`, then checked multiplication | denominator excludes zero |
| `checked_square` | square the endpoints of the absolute-value range | all finite intervals |
| `checked_ln` | `[ln(l), ln(u)]` | `l > 0` |
| `checked_exp` | `[exp(l), exp(u)]` | all finite intervals |
| `checked_sqrt` | `[sqrt(l), sqrt(u)]` | `l >= 0` |

Here the input intervals are `[l,u]` and `[a,b]`. Square, exponential and
square root intersect the widened enclosure with the nonnegative reals.
`negated`, `abs` and pointwise `max` compute their exact interval ranges
without rounding. `contains` includes both endpoints and excludes NaNs and
infinities. Both zero signs represent the same real. Negation flips their
signs; absolute value and the maximum of two zeros use positive zero, so
these transforms do not rely on the unspecified zero tie of `f64::max`.

`IntervalError::InvalidBounds` denotes invalid constructor inputs.
`Domain` denotes an interval that includes a forbidden argument, even if
some points in it are valid. `Range` means an intermediate result or its
outward neighbour is nonfinite. No infinite endpoint or finite sentinel is
returned. This deliberately includes an operation whose nearest result is
`f64::MAX`: its upper neighbour is infinite. Division can also fail when its
intermediate reciprocal overflows, even if the exact quotient would fit.

Underflow is not an exact-zero convention. For example, `exp([-1000,-1000])`
returns `[0, 2^-1074]`. Multiplying `2^-1074` by `0.5` returns
`[-2^-1074, 2^-1074]`, enclosing the positive midpoint lost by rounding.
A denominator interval containing zero therefore cannot be divided into;
callers must retain that inability to resolve a result.

## Derivation and proof boundary

Let `RN(x)` be binary64 nearest-even rounding and `pred`, `succ` its
representable neighbours. For finite neighbours,

```
pred(RN(x)) <= x <= succ(RN(x)).
```

This includes subnormal results and halfway cases. The theorem
`neighbour_enclosure` in `formal/binary64/FiniteInterval.v` instantiates
Flocq 3.4.3's `pred_round_le_id` and `succ_round_ge_id` with precision 53
and minimum exponent -1074. Flocq's format has no upper exponent limit;
the finite-neighbour guard is the correspondence condition for the bounded
IEEE binary64 format used in Rust.

Monotonicity proves sum, difference and elementary-function propagation.
A bilinear function on a rectangle has its extrema at corners: the
`product_corners` proof bounds each coordinate in turn, accounting for its
sign. Reciprocal reverses order on each of the positive and negative
half-lines. Combining its endpoint enclosure with the product theorem
proves staged division. Squaring the nonnegative absolute range is
monotone. Clamping a lower bound to zero preserves any nonnegative image.
The file also proves the three absolute-value branches, negation and
pointwise maximum. These are standard real interval-extension rules;
no fitted-model assumptions enter them.

The proof assumes each primitive's published contract: IEEE nearest-even
`+`, `-`, `*`, `/`, Rust `next_down`/`next_up` representable neighbours, and
this crate's correctly rounded [ln](ln.md), [exp](exp.md) and
[sqrt](sqrt.md). It is a real-arithmetic propagation proof, **not a
machine-checked translation of Rust control flow**. Existing elementary
kernel proofs establish those kernels' separate contracts. The new theorem
source, Rust implementation, fixtures, generator and derivation are hashed
in `formal/binding.sha256`; the formal lane recompiles the proof and audits
its axioms. The interval orchestration is not part of the existing OCaml
extraction corpus. Rust-to-proof correspondence is reviewed, tested against
independent endpoints, and checked across targets by the determinism digest.

The mathematical sources are IEEE 754-2019 sections 3–5 (binary formats,
rounding and arithmetic), and the named Flocq 3.4.3 predecessor/successor
rounding theorems. Only theorem interfaces were consulted; no external
implementation source was used.

## Independent checks and cost

`generators/interval_reference.py` generates 4,072 cases. Addition,
subtraction, multiplication and reciprocal images are evaluated with exact
rational arithmetic. Their declared widened endpoints must match bit for
bit; the generator also checks containment of the exact corner images,
including direct rational quotients independently of staged division.
Elementary cases use the shared mpmath 1.4.1 interval oracle, starting at
128 bits and requiring agreement at two consecutive precisions before
rounding an endpoint. This is numerical oracle evidence, not a substitute
for the proof above; the oracle's limitations are recorded in
`generators/oracle/__init__.py`.

The cases cover signs, zero crossings, cancellation, subnormals, binade
boundaries, overflow, invalid domains and deterministic random binary64
inputs. Separate tests check constructor invariants, exact transforms,
membership and zero signs. The `finite_interval` section of the
[determinism digest](determinism.md) covers every public operation and each
error variant. Adding that section changes the digest without changing any
existing scalar or batched function output.

All operations have constant storage and operation count. Addition and
subtraction evaluate two endpoint operations; multiplication evaluates
four corners; division evaluates two reciprocal endpoints and one
multiplication. Each elementary operation calls the corresponding scalar
kernel twice. There is no vector path, dynamic precision, allocation or
claim about an engine's end-to-end performance. Repeated use can widen
bounds through dependency overestimation; a successful enclosure need not
be narrow enough for a caller's decision.
