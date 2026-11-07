# Bounded Box–Muller normal pairs

## Contract and consumer purpose

`fast::random::normal_pair(w1, w2)` uses the same exact word-to-uniform
mapping and octant fold as [the strong pair](random.md). For every pair of
`u64` words, each output differs from `random::normal_pair(w1, w2)` by at
most `2^-38` in absolute value. Outputs are finite. Angular zeros retain
their signed-zero bits. This is an explicit approximate API; no existing
stream method or normal pair changes its selected contract.

`normal_pair_slice(w1, w2, out)` writes the same pair bits as scalar calls.
It checks all three lengths before writing anything and panics on mismatch.
The implementation is a scalar loop on every backend; a slice interface
does not by itself claim SIMD acceleration.

The consumer purpose is local-volatility Monte Carlo using Xoshiro256++
streams, cached pairs and antithetic paths (#282). Uniform consumption and
the sampling grid are preserved. The primitive's absolute budget follows
from its mathematical composition, including logarithms near one; it is
not justified by Monte Carlo noise. Consumer pricing error, derivatives
and runtime remain separate qualifications.

| Region / output | Selected budget | Semantics | Cost budget |
| --- | --- | --- | --- |
| All word pairs, each output | `2^-38` absolute against the strong stepwise pair | Finite results, signed angular zeros, scalar/slice identity on all targets | No greater cost than a same-host libm Box–Muller with Xoshiro256++ on the declared native workloads |

## Derivation and bounded work

Write `u = unit_open(w1)`, `L = -ln(u)`. The existing grid gives
`2^-53 <= L < 37`. The private radius logarithm uses the existing generated
reciprocal/log tables and exact residual `z = y R[i] - 1`, with
`|z| <= 2^-9`. It selects two domains:

- For `511/512 <= u < 1`, the reciprocal-one cells retain the complete
  compensated logarithm sequence, including its degree-six correction.
  Its bound remains `|L_fast - L| <= 2^-53 L + 2^-65`.
- For `2^-53 <= u < 511/512`, use the degree-four correction below and
  the bound `|L_fast - L| <= 2^-48 L + 2^-45`. Here `L >= 2^-9`.

```text
ln1 = RN(RN(e L1) + T_hi[i])
ln0 = RN(RN(e L0) + T_lo[i])
z2  = RN(z z)
q4  = RN(z2 RN(RN(RN(z H[0]) - 1/2) + RN(z2 H[1])))
log = RN(RN(ln1 + z) + RN(ln0 + q4))
```

The coefficients are the existing generated `H[0]` and `H[1]`; no new
fit or table is introduced. The Gappa certificate compares this exact
binary64 sequence with the existing compensated sequence, including
its higher terms. For `|ln1| <= 38`, `|ln0| <= 2^-38`, and `|z| <= 2^-9`,
the difference is at most `2^-45`. The reduction proves these premises
on the uniform grid. Combining that difference with the existing
logarithm bound establishes the stated mixed bound away from one.
Public `fast::elementary::ln` retains its complete original sequence.

This removes four polynomial operations and three compensation operations
outside the reciprocal-one cells. Multiplication and addition stay separate;
only the existing proved-exact residual may use FMA, with its bit-identical
split fallback. There is no new FMA sequence or platform math call.

The correctly rounded reference logarithm's error is at most `2^-53 L`.
Both magnitudes are positive. Use

```text
|sqrt(2a) - sqrt(2b)| = 2 |a-b| / (sqrt(2a) + sqrt(2b))
```

to propagate their difference, then include both correctly rounded square
roots. Outside the reciprocal-one cells, the resulting radius differs
from the strong stepwise radius by at most `2^-40`. Near one, the original
composition bound is retained; it includes the absolute logarithm term.
The radii are below nine. The angle is the identical rounded
`phi = RN(RN(2 pi) m 2^-53)`, with `0 <= phi <= RN(pi/4)`; no general
argument reduction or transcendental fallback is needed.

`generators/fast_random_constants.py` generates six coefficients each for
`sin(sqrt(z))/sqrt(z)` and `cos(sqrt(z))` on
`[0, RN(pi/4)^2]`, using Chebyshev interpolation at 200 bits and rounding
each coefficient to binary64. Horner evaluation uses separate multiply
and add with `z = RN(phi*phi)`. Multiplying the sine polynomial by `phi`
preserves zero exactly. After multiplication by the radius, the octant
swaps and negates the two outputs using the strong pair's shared exact
helper; sign changes commute with these finite rounded products. The angular absolute budget
is `2^-44`, including coefficient, approximation and evaluation error.
The strong rounded sine/cosine adds at most `2^-53` to this comparison.
The final binary64 products are included in the output budget.

There is one logarithm, one correctly rounded square root, two degree-five
polynomials and no adaptive refinement. Every supported word pair takes
this path. No unproved result is accepted through a work cap or fallback.
The scalar and slice paths call the same function by construction. Empty
slices return after validation; one-element slices call the scalar path;
longer slices use the separate bulk loop, keeping its register setup off
tiny calls.

## Paired evidence and selection

The retained harness and its decision rule are in
[`scripts/bench_fast/normal_pair/README.md`](../scripts/bench_fast/normal_pair/README.md).
Six coefficients were selected over seven: both satisfied the screening
budget, with no established ordinary-input cost benefit from the larger
polynomial. Extra angular precision does not tighten the selected output
budget without a tighter logarithm composition proof. Coefficients come
from the mathematical functions; no external implementation is copied.

The independent interval-oracle Box–Muller fixture supplies the strong
stepwise results. Boundary witnesses cover the uniform extremes, all
octant boundaries and adjacent words, and seeded streams. Sampled errors
are distinct from the whole-domain certificates and composition proof.

## Assurance artifacts

`formal/fast/FastRandomWords.v` proves the exact uniform and integer-fold
domains. `FastRandomAngular.v` transcribes the binary64 Horner sequence,
connects its Gappa evaluation certificates to IEEE operations, and proves
the polynomial approximation against real sine and cosine with CoqInterval.
`FastRandomLog.v` connects the private logarithm to the existing full
logarithm proof, checks the branch domain, and applies the Gappa comparison
to finite IEEE operations. `FastRandomBound.v` proves the two-region
radius/output error composition, and
`FastRandom.bm_pair_ok` applies it to the finite binary64 kernel and strong
stepwise reference. The octant uses only the shared exact swaps and sign
changes. `bm_zero_angle` additionally checks the zero-angle sine bits.

The independent Sollya checks are in
`generators/normal_random_poly.sollya`; the Gappa certificates are
`formal/normal/normal_pair_sin.g`, `normal_pair_cos.g`, and
`normal_pair_log.g`. The last is reproduced by
`generators/fast_random_radius.py` from the existing logarithm coefficients. The generated
constants, source, derivation and proofs are bound by `formal/binding.sha256`
(normal compositions use the end-to-end manifest). The kernel audit records the assumptions
of these theorems. The extracted kernel is compared bit for bit against
the 2,048 seeded reduced input pairs and all radius-fixture inputs in the
internal cross-check corpus.

`crates/reference/tests/fast_random.rs` checks the independent pair fixture,
signed zeros, discarded-word-bit semantics, scalar/slice identity including
empty/short/remainder slices, and output preservation on length mismatch.
The private radius test additionally uses the interval-oracle fixture from
`generators/fast_random_radius_reference.py`: reciprocal boundaries and
midpoints, uniform exponents, adjacent grid points, near-one branch
neighbors, extrema, and retained error witnesses. Its error comparison uses
exact integer arithmetic. The digest adds independent `fast_normal_pair` and `fast_normal_pair_slice`
sections without changing any earlier corpus inputs.

The owning issue/PR records source revisions, checked artifacts, observed
errors, host/toolchain/features, native timing samples and qualification
limitations. No end-to-end consumer or universal performance claim follows
from this derivation. Existing strong APIs retain their complete contracts.
