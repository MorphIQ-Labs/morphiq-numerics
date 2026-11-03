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
`2^-53 <= L < 37`. The fast logarithm supplies
`|L_fast - L| <= 2^-53 L + 2^-65`; the correctly rounded logarithm's
error is at most `2^-53 L`. The absolute term cannot be dropped near one.
Both magnitudes are positive. Use

```text
|sqrt(2a) - sqrt(2b)| = 2 |a-b| / (sqrt(2a) + sqrt(2b))
```

to propagate their difference, then include both correctly rounded square
roots. The radii are below nine. The angle is the identical rounded
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
The scalar and slice paths call the same function by construction.

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
`FastRandomBound.v` proves the radius/output error composition, and
`FastRandom.bm_pair_ok` applies it to the finite binary64 kernel and strong
stepwise reference. The octant uses only the shared exact swaps and sign
changes. `bm_zero_angle` additionally checks the zero-angle sine bits.

The independent Sollya checks are in
`generators/trig_normal_pair_poly.sollya`; the Gappa certificates are
`formal/trig/normal_pair_sin.g` and `normal_pair_cos.g`. The generated
constants, source, derivation and proofs are bound by `formal/binding.sha256`
and `formal/trig/binding.sha256`. The kernel audit records the assumptions
of these theorems. The extracted kernel is compared bit for bit against
2,048 reduced input pairs in the internal cross-check corpus.

`crates/reference/tests/fast_random.rs` checks the independent pair fixture,
signed zeros, discarded-word-bit semantics, scalar/slice identity including
empty/short/remainder slices, and output preservation on length mismatch.
The digest adds independent `fast_normal_pair` and `fast_normal_pair_slice`
sections without changing any earlier corpus inputs.

The owning issue/PR records source revisions, checked artifacts, observed
errors, host/toolchain/features, native timing samples and qualification
limitations. No end-to-end consumer or universal performance claim follows
from this derivation. Existing strong APIs retain their complete contracts.
