# Checked normalization of log weights

`morphiq_numerics::log_space::normalize_log_weights(x, output)` computes
`p_i = x_i − log(sum_j exp(x_j))` in a caller-provided slice. It also returns
the log total mass and one outward-rounded absolute error bound covering every
finite normalized component. It allocates nothing and uses O(n) work and O(1)
auxiliary storage (fixed-size lane scratch with SIMD).

This is a bounded-error API, not a correctly rounded one. It does not change
`log_sum_exp_and_normalize`, whose pair operation sequence remains separately
specified in [log_space.md](log_space.md). A new consumer chooses this contract
explicitly; existing consumers retain their current results.

## Sources and reuse

The mathematical starting point is the shifted formulation in Blanchard,
Higham and Higham, *Accurately Computing the Log-Sum-Exp and Softmax Functions*,
MIMS EPrint 2019.16, author version dated 15 May 2020, latest deposit 17 May
2020, equations (1.3)–(1.4) and Algorithm 4.1. The exact PDF URL, SHA-256 and
publication citation are recorded under [BHH] in [log_space.md](log_space.md).
Taking the logarithm of the normalized weight gives the formula below.
The compensated Sum2 reduction and elementary functions are reused from this
repository, with their existing contracts and source audit. No third-party
implementation source was consulted or copied for this function.

The only new numerical operations are the normalized-output subtractions and
the returned error-radius construction. Their bounds are composed below and
checked in exact rational arithmetic by `generators/log_space_bounds.py`.
That generator also writes `normalize_constants.rs`, binding the runtime
constants to these inequalities. This checks the arithmetic of the derivation;
it does not constitute a machine-checked proof that Rust follows it. Independent
interval fixtures check the implementation separately.

## Domain and failures

Inputs are finite binary64 log weights or negative infinity (exact zero mass).
Positive finite log weights are valid. At least one entry must be finite, and
the number of finite entries must be at most `2^20 + 1`, the established domain
of the inherited reduction bound. This limit is a proof domain, not a chosen
model state-count limit. Additional negative-infinity entries do not count.

Every successful output is nonpositive. An input structural zero produces
negative infinity exactly. Every finite input produces a finite output, even
when its ordinary-space probability would underflow. A singleton support gives
positive zero exactly and a zero radius; the log total preserves the original
finite value's bits, including signed zero.

Errors are typed:

| Condition | Error |
| --- | --- |
| Different input/output lengths | `LengthMismatch` |
| Empty input or all structural zeros | `ZeroMass` |
| NaN or positive infinity | `InvalidWeight(index)` |
| More than the qualified number of finite entries | `TooManyFiniteTerms` |
| Rounded shifted/normalized finite component overflows | `Unrepresentable(index)` |

The entire output slice is unchanged on error. Shape is checked first, then
input classification in index order, then output representability in index
order. A model can therefore distinguish impossible mass, invalid inputs and
insufficient numerical representation. The function never replaces an
unrepresentable finite log probability by a structural zero.

## Algorithm and arithmetic order

Let `m` be the first maximum, and let `j` be its index. The existing reduction
computes `t_hat ≈ sum_{i != j} exp(x_i − m)` in input order. It retains the
`two_sum` low word and uses the existing compensated accumulation and scalar-
equivalent lane implementation. Set `L_hat = ln_1p(t_hat)`. For finite entries:

```text
d_hat_i = RN(x_i − m)
p_hat_i = RN(d_hat_i − L_hat)
```

Return the log total as `m` when `t_hat == 0`, otherwise `RN(m + L_hat)`.
It is bit-identical to `log_sum_exp(x)` on the admitted domain. Probability
output never uses `x_i − RN(m + L_hat)`: at a large common offset that rounded
log total can lose the entire `L_hat` correction. For example, three equal
weights near `2^1000` have normalized logs `−log(3)`, not zero.

There are four passes: classify/find maximum, compensated reduction, validate
all normalized outputs/collect their largest magnitude, then write outputs.
The validation pass is what makes failure atomic without O(n) temporary
storage. For each finite entry the last two passes repeat only two subtractions.
The existing reduction uses transcendental work once per contributing term,
with one final `ln_1p`. No model topology or hidden-state recursion belongs here.

## Error bound

Write `u = 2^-53`, `tau = 2^-1074`, `n` for the finite count and `k = n−1`.
Let `d_i = x_i − m ≤ 0`, `L = log(1 + sum_{i != j} exp(d_i)) ≥ 0`, and
`p_i = d_i − L`. Thus `|p_i| = |d_i| + L`: the final subtraction has no
cancellation. The inherited reduction proof supplies the conservative bound

```text
|L_hat − L| ≤ beta u L + eta
beta = 3 + 2^-8
eta = (2k + 1) tau
```

This uses the published log-sum bound as an upper bound on its internal
logarithmic correction; the final addition to `m` is not needed here. A
subnormal result of subtracting two binary64 numbers is exact. For normal
results, each subtraction has relative error at most `u`. Therefore:

```text
|p_hat_i − p_i|
  ≤ u |p_i| + (1+u) (u |d_i| + beta u L + eta)
  ≤ [1 + (1+u) beta] u |p_i| + (1+u) eta
  ≤ C u |p_i| + 2n tau,             C = 4 + 2^-7.
```

The last inequalities include higher-order terms and hold through the maximum
qualified count. The rational generator checks them against the inherited
composition. Its error expressions increase with k on this domain, so the
endpoint check covers intermediate counts. Exact structural zeros are outside
the finite-component inequality and have no error.

For a radius computable from the returned values, rearrange:

```text
|p_i| ≤ (|p_hat_i| + 2n tau)/(1 − C u)
|p_hat_i − p_i| ≤ [C/(1−Cu)] u |p_hat_i| + [2/(1−Cu)] n tau.
```

The least power-of-two factors dominating these coefficients are 8 and 4.
The generator derives those factors rather than taking them as tolerances.
With `a = max_i |p_hat_i|`, the function returns
`up(up(8u a) + 4n tau)`, where `up(v)` advances the rounded value by one
binary64 step toward positive infinity. Each step bounds its preceding
round-to-nearest operation from above, including underflow. `4n tau` is
represented exactly by a subnormal bit pattern. The bound is finite even when
`a` is the largest finite value. A singleton support bypasses this construction
and returns the exact zero radius.

The radius bounds normalized log probabilities only. The returned log total
retains its separate [log-sum bound](log_space.md#4-log_sum_exp-error-bound).
Neither result asserts that a supplied model or observation is statistically
appropriate, or that a callback represents a normalized emission measure.

## Independent evidence

`generators/log_normalize_reference.py` uses mpmath 1.4.1 interval exponentials
and logarithms on exact binary64 inputs. Precision doubles from 256 bits until
the enclosure is at least 40 bits narrower than the permitted error. Accepted
binary64 endpoints are rounded inward around the derived bound, so no test
tolerance widens it. Uniform cases additionally use the closed form `−log(n)`.
The largest qualified count has a compact closed-form fixture.

The corpus covers irregular sums, lane boundaries/remainders, ties, exact
zeros, ordinary-space underflow, subnormal shifts/tails, huge common offsets
and the largest representable log spans. Separate tests check failure atomicity,
invalid inputs, finite-count boundaries and singleton exactness. Negative
controls require the oracle to reject unshifted subtraction and zeroing a
finite tail. Scalar/SIMD consistency is checked separately from accuracy.

The determinism corpus includes successful values, metadata, refusal codes and
untouched output storage. It extends the digest deliberately; existing APIs'
inputs and arithmetic are unchanged.

## Native cost measurements

The committed [host record](evidence/log-normalize-x86-host.json),
[scalar samples](evidence/log-normalize-x86-scalar.csv) and
[SIMD samples](evidence/log-normalize-x86-simd.csv) were collected with
`cargo run --release -p morphiq-numerics-reference --bin bench-log-normalize`
and the same command with `--features simd,std`, with execution pinned to CPU14.
The benchmark warms each case, allocates buffers before timing, alternates
method order over nine paired rounds and consumes outputs through `black_box`.
It covers K=1,2,3,8,32,128,1024,65536; ordinary dyadic weights, exact zeros with
underflowing tails, and huge equal offsets. All arithmetic results and metadata
are checked outside timing against a shifted-scratch composition.

The scratch comparator composes the existing public log-sum API on exact-shift
inputs and includes validation, output representability checks and the same
radius calculation. It uses one additional caller-owned K-entry buffer. Its
exact-shift restriction is explicit; it is not a qualified general normalizer.
The existing fused pair API is also timed at K=2. Its different validation,
output, failure and error contracts are retained; it is a diagnostic comparator.

| Ordinary inputs | K=2 | K=32 | K=1024 | K=65536 |
| --- | ---: | ---: | ---: | ---: |
| Checked scalar median ns/call | 89.5 | 1,079.4 | 33,110.8 | 2,073,623.9 |
| Scalar checked / shifted-scratch median | 1.00 | 0.94 | 0.91 | 0.90 |
| Checked SIMD median ns/call | 91.3 | 932.1 | 26,544.2 | 1,722,644.8 |
| SIMD checked / shifted-scratch median | 1.02 | 0.89 | 0.89 | 0.89 |

Across the tested K≥3 cases, checked/scratch median ratios were 0.82–0.99
(scalar) and 0.89–0.99 (SIMD). At K=2, checked/fused-pair ratios were
0.95–1.01 (scalar) and 0.92–1.17 (SIMD). These measurements do not establish
that the new function is at least as fast as every available alternative.
Other numerical workloads were active on the host; no exclusive machine or
frequency control was available. The samples report this run, not isolated
latency, sustained capacity, ARM performance or a universal performance bound.
The algorithm allocates zero bytes; caller-provided input/output storage and
the alternative's preallocated scratch are excluded from timed setup.
