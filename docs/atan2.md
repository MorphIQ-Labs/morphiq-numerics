# `atan2`

`atan2(y, x)`, the angle of the point `(x, y)` to the positive `x` axis in
`[−π, π]`, rounded to nearest, ties to even: a certified fast path in
double-word arithmetic, the shared rounding test, and a `Q256` accurate path.
The code is `crates/morphiq-numerics/src/atan2/`; the constants are generated
and every bound is a Gappa certificate in `formal/atan2`.

## Status

| Item | State |
|---|---|
| Specification and special values (§1) | done; IEEE 754-2019 §9.2 |
| Reduction to `φ = atan(n/d)`, `n ≤ d`, and the four forms (§3) | done; the tiny and subnormal ratios are exact (§3) |
| Fast path: the double-word ratio, 64 segments, the series, the forms (§3, §4) | **certified** (Gappa): relative error below `2^-63.04` |
| Rounding test at `ε₁ = 2^-62` (§6) | sound given the fast bound, as [ln] §5 |
| Accurate path: one cubic Newton step in `Q256` (§5) | **certified** (Gappa): relative error below `2^-190.6`, given the facts §5 lists |
| Correct rounding (§6) | wherever the test decides, and on every pair of [CM]'s list; **not** claimed over the whole domain (§6) |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§7) | done by the formal lane (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Coq transcription of the Rust (`formal/atan2/Atan2Kernel.v`) compared with it bit for bit (§7) | **done**: the entry (special values, forms, tiny ratios), the fast path and its decision at every form, the accurate path (before rounding), 11,477 corpus cases; five planted faults (a series coefficient, the scale, the subnormal midpoint's exponent, Newton's numerator sign, the doubling of `π/2`) each give mismatches. Proofs that it meets §3 and §5's bounds are not written |
| ARM NEON, SSE2, AVX2+FMA, AVX-512F lanes; `atan2_slice` | **done** (`atan2/lanes.rs`, [lanes.md](lanes.md)): bit-identical to `atan2` on every backend over the fixture's pairs, every pair of special values, ratios at every scale, the segment boundaries and random encodings; run on NEON, and on x86-64 SSE2 under Rosetta; AVX-512F is CI's SDE job |
| Mutation witnesses | **done** (§7): 215 mutants of `atan2/mod.rs` and `atan2/lanes.rs`, 194 caught, 10 unviable, 6 timed out (detected), 5 equivalent |
| Same-host performance against the best alternatives | measured on NEON only: 1.05–1.64× over the scalar loop ([measurements](../crates/reference/measurements/asin-asinh-atan2-m1pro/README.md)); native x86 not measured |

## Sources

- **[CM]** CORE-MATH, `src/binary64/atan2/atan2.wc` at commit
  `0ce0cbc15935e24c656280e5a46c34e89f301b7a` (SHA-256
  `9e4fb81a3c4a789ea739203d2db3ef9689c48208d94196726fa7a22886e573db`, MIT): 26,270
  worst cases, a restricted set rather than an exhaustive search. Used as test
  inputs and to size the accurate path (§6), never as code.
- **[M]** J.-M. Muller, *Elementary Functions*, 3rd ed., 2016.
- **[DW]** [double-word.md](double-word.md): the double-word operations' proved bounds.
- **[ln]** [ln.md](ln.md) §5: the rounding test.
- **[sin_cos]** [sin_cos.md](sin_cos.md) §5, §8: the `Q256` `sin`/`cos` series and `Q256::recip`.

## 1. Specification

| Input | `atan2(y, x)` |
|---|---|
| a NaN in either argument | NaN |
| `y = ±0`, `x > 0` or `+0` | `±0` |
| `y = ±0`, `x < 0` or `−0` | `±RN(π)` |
| `y` finite nonzero, `x = ±0` | `±RN(π/2)` |
| `y = ±∞`, `x` finite | `±RN(π/2)` |
| `y = ±∞`, `x = +∞` | `±RN(π/4)` |
| `y = ±∞`, `x = −∞` | `±RN(3π/4)` |
| `y` finite, `x = +∞` | `±0` |
| `y` finite, `x = −∞` | `±RN(π)` |
| both finite and nonzero | §3–§6, odd in `y` |

`RN(π) = 0x1.921fb54442d18p+1`, `RN(π/2) = 0x1.921fb54442d18p+0`,
`RN(π/4) = 0x1.921fb54442d18p−1`, `RN(3π/4) = 0x1.2d97c7f3321d2p+1`. The sign of
`y` is the result's, zeros included.

## 2. Accuracy needed

[CM]'s hardest listed pair is 101.7 bits from a midpoint, ranked here at 500
bits (`generators/atan2_reference.py` takes the hardest 40); the accurate path's
`2^-190` is far inside it. The list is restricted, so it does not bound the
distance of every pair from a midpoint (§6).

## 3. Reduction and fast path

For finite nonzero `a = |y|`, `b = |x|`, let `n = min(a, b)`, `d = max(a, b)`,
`t = n/d ∈ (0, 1]` and `φ = atan t ∈ (0, π/4]`. The angle's magnitude is one of
four forms:

| `\|y\| ≤ \|x\|` | `x > 0` | `x < 0` |
|---|---|---|
| yes | `φ` | `π − φ` |
| no | `π/2 − φ` | `π/2 + φ` |

- **`t < 2^-900`.** `π/2 ∓ φ` and `π − φ` are `RN(π/2)` and `RN(π)`: the
  constants lie 0.28 ulp from their roundings, so 0.22 ulp from a midpoint, far
  more than `φ`. The form `φ` is `RN(n/d)` itself: `atan t` is below `t` by a
  relative `2^-1800`, so the two round alike unless `t` is within that of a
  midpoint. A midpoint of normal binary64 numbers has 54 significant bits, which
  `n/d` with 53-bit `n` and `d` cannot have, and any other `t` is at least `2^-107`
  relatively from one. The exceptions are the midpoints of the subnormal grid
  and the one between the largest subnormal and `MIN_POSITIVE`, which have at most
  53 bits: `n/d = (2m + 1)·2^-1075` exactly. There ties-to-even may pick the upper
  neighbour while `atan` lies just below `t`, so the result is the lower one
  (`tiny_phi`: the odd parts `m_n`, `m_d` with `m_d | m_n` and exponents
  differing by exactly 1075). `generators/atan2_reference.py` includes these
  pairs, and the oracle found the boundary one.
- **Otherwise.** Both `n` and `d` are scaled by `2^-e` (exactly, in two steps),
  `e` the exponent of `d`, so `d ∈ [1, 2)`. `q = RN(n/d)`, `(p, p_e) =
  two_prod(q, d)` (exact, `|q d| ≥ 2^-900`), the remainder `(n − p) − p_e` (`n − p`
  is exact by Sterbenz's lemma), `q_l = RN(remainder/d)`, and `t = q + q_l`
  (`fast_two_sum`). Certified: `divide.g`, `|t − n/d| ≤ 2^-104 (n/d)`.
- **`φ = atan t`** (§4), then the form: `φ`; `π/2 − φ` and `π/2 + φ` by double-word
  subtraction and addition of `π/2` (`2^-107`); `π − φ` from twice `π/2`, exact.
  Certified: `half_minus.g`, `half_plus.g`, `pi_minus.g`.

## 4. `atan t` on a double-word

`i = RN(64·t_hi)` through the shifter `1.5·2^52`.

- **`i = 0` (`t < 1/128`): the series** `atan t = t − t³·Q(t²)`, `Q` of degree 3
  (`generators/atan2_poly.sollya`: relative error `0x1.000002p-54`; the kernel
  evaluates `P = −Q` with the coefficients' signs, the same operations negated).
  Certified: `series_tail.g` (`2^-51`) and `series_compose.g`.
- **`i ≥ 1`: the table.** `a = i/64`, `s = (t_hi − a) + t_lo` (`t_hi − a` exact),
  `atan(a + s) = atan a + c₁ s + s² G(s)`, `c₁ = 1/(1 + a²)`, `G` of degree 8 with
  binary64 coefficients, `|s| ≤ 0.0078126`. `(p_hi, p_lo) = two_prod(s_hi, c_hi)`,
  `tail = p_lo + (s_hi c_lo + s_lo c_hi) + s_hi² g`, `Y = atan a + fast_sum(p_hi,
  tail)`. Certified per segment: `eval_<kk>.g` (the evaluation, bound `6.5
  T² 2^-53 sup|G|`, with the Horner value within `[−2, 2]`) and `compose_<kk>.g`
  (against `atan(a + s)`).

The structure is `asin`'s ([asin.md](asin.md) §4) with the segment tables of `atan`;
it is written out here rather than shared so that `asin`'s hash-bound sources stay
as proved.

## 5. Accurate path

Given `φ₀` (the fast `φ`, a double-word) and the exact `n`, `d` in `Q256`: with
`(sin, cos) = ` the `Q256` series of [sin_cos] §5 at `φ₀`,
`φ₁ = φ₀ + (n cos φ₀ − d sin φ₀)/(d cos φ₀ + n sin φ₀)`, the reciprocal scaled into
`[1, 2)` first. With `φ₀ = φ* + δ` the numerator is `−R sin δ` and the denominator
`R cos δ`, so the step lands at `φ* + δ − tan δ = φ* − δ³/3 (1 + O(δ²))`: a cubic
error. The form's constant (`π/2`, `π` in `Q256`) is added or subtracted, and the
result is rounded once.

- Certified: `newton.g`: relative to `φ*`, within `2^-190.6`, from `|δ| ≤ 2^-63.04 φ*`.
- **Stated, not certified:** `c₃ ≤ 1.001` in `tan δ = δ + c₃ δ³/3` (`|δ| ≤ 2^-52`), the
  `Q256` sine and cosine's `2^-198` ([sin_cos] §5) carried through the numerator
  and denominator (at most `2^-196 φ*`, using `t/atan t ≤ 4/π` and `cos φ₀ ≥ 0.7`),
  and `φ₀ ≤ π/4 + 2^-62`, a hair outside the series' `(π/4)²` domain, covered by its
  slack as in [asin.md](asin.md) §5.

## 6. Rounding test and claims

`decide_with(Y, EPS)`, `EPS = 2^-62(1 + 2^-50)`, as [ln] §5.

- The fast bound is `2^-63.04` (the largest `compose_<kk>.g` and the series, plus the
  ratio's `2^-104`), inside `ε₁ = 2^-62`.
- When the test passes, the result is `RN(atan2(y, x))`.
- Otherwise the accurate value is within `2^-190.6` relatively, so the result is
  within `(1/2 + 2^-137)` ulp of `atan2(y, x)`: correctly rounded unless the value
  lies within `2^-190.6` of a midpoint. [CM]'s list is a restricted set, so no
  search excludes that over the whole domain, and **correct rounding is not
  claimed there**. Every pair of [CM]'s list is correctly rounded by the bound (the
  hardest is `2^-101.7` ulp from a midpoint, §2).

### Heuristic estimate beyond the guaranteed claim (NOT a proof)

What is guaranteed is stated above: the result is within `(1/2 + 2^-137)` ulp of `atan2(y, x)`
always, and correctly rounded wherever the test decides and on every pair of [CM]'s list. Beyond
that, correct rounding is supported **heuristically only**, as follows (`generators/atan2_hardness.py`
prints the figures).

- **Assumption (the part that is not proved).** The bits of `atan2(y, x)` past the 54th behave as
  equidistributed for the pairs that matter. Nothing here proves it; [CM]'s list is a restricted
  set, not a search of the domain.
- **Which pairs can matter.** The angle depends on `t = min/max ∈ (0, 1]` and the form (four
  forms; a sign of `y` only negates it; the absolute scale of the pair does not change the angle).
  With `e` the difference of the two exponents there are at most `2^104` significand pairs (52
  fraction bits each, ratios not deduplicated) per `e`. Deep ratios cannot be hard: `t` is at
  least `2^-107` relatively from every midpoint (§3's argument, not machine-checked) and
  `atan t` is within a relative `t²/3` of `t`, so for the form `φ` nothing lies within the window
  once `t < 2^-52.7`; for `π/2 ∓ φ` and `π ∓ φ` the constants sit 0.28 ulp from their roundings,
  so `φ` must reach about `2^-54.2` (`2^-53.2` for `π`) before a midpoint is within range. The
  deepest exponent differences that can matter are therefore 52 (`φ`), 54 (`π/2 − φ`,
  `π/2 + φ`) and 53 (`π − φ`), which gives at most `2^104 · (53 + 55 + 54 + 55) ≈ 2^111.76`
  effective pairs.
- **Per-pair probability.** The accurate bound is `δ = 2^-190.61`. A value equidistributed past
  the 54th bit has a midpoint inside the two-sided window `±δ|Z|` with probability
  `2δ|Z|/ulp(Z)`; with `|Z|/ulp(Z)` log-uniform in a binade (mean `2^52/ln 2`) that is `2^-137.08`.
- **Estimate.** `2^111.76 · 2^-137.08 ≈ 2^-25.3` (about `2.4·10^-8`) expected pairs whose accurate
  value could round the wrong way. This is an upper-bound style estimate of the chance that any
  pair is affected, not a count of known counterexamples, and it is only as good as the
  equidistribution assumption.

**The claim stays as stated.** `atan2` returns a value within `(1/2 + 2^-137)` ulp of the exact
angle for every finite pair; it is correctly rounded where the rounding test decides and on
[CM]'s list (proved for the transcription, §7 and the Coq files); beyond those, correct rounding
is supported heuristically only, by the estimate above.

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/atan2_poly.sollya` (Sollya 8.0) | the series and the 64 segments' polynomials and bounds, in `generators/atan2_poly.out` |
| `generators/atan2_constants.py` | `src/atan2/tables.rs`: the polynomials, the table, `π/2`; and `formal/atan2/Atan2Tables.v`, the same constants for the transcription |
| `formal/atan2/Atan2Kernel.v`, `Atan2Tables.v` (Coq 8.15) | the transcription of `atan2/mod.rs` (with trig's `Q256` sine and cosine through `formal/asin/AsinKernel.v`) and its constants; extracted by `formal/extraction/InternalCrosscheck.v` and run against `src/internal_crosscheck/atan2.rs`'s corpus by `check_formal.sh` step 7 |
| `generators/atan2_certificates.py` | writes every certificate in `formal/atan2` (135) |
| `formal/atan2/*` (Gappa 1.4.1, at 400 bits) | §3's ratio and forms, §4's evaluations and compositions and series, §5's step |
| `generators/atan2_reference.py` | the fixture: the 40 hardest pairs of [CM], every pair of special values, the subnormal midpoints, the segment and ratio boundaries, random pairs |

The binding `formal/atan2/binding.sha256` covers this document, the Sollya script
and output, the generated tables, every certificate and the source `atan2/mod.rs`.

Tests:
- `crates/reference/tests/atan2.rs`: 10,405 cases, bit for bit.
- `src/atan2/tests.rs`: special values, oddness in `y`, equal magnitudes and the
  constants, and 60,000 random pairs on which every fast-path decision equals the
  accurate path's result for all four forms.
- The formal lane's Coq proof of each certificate (`check_formal.sh` step 5).
- **Mutation.** cargo-mutants 27.1.0 over `atan2/mod.rs` and `atan2/lanes.rs`, built with the `simd`
  feature and run against `atan2`'s unit tests, the reference fixture, the determinism digest and the
  lane suites, generates 215 mutants: 194 are caught by a failing test, 10 do not compile and 6 run
  past the timeout, which also detects them. Five are equivalent:
  - `>` against `>=` where `|y|` and `|x|` are compared (twice) and `<` against `<=` at the ratio `2^-900`:
    at equality both forms (or both paths) are valid and return the same value;
  - `(j - 1) / 2` against `j / 2` in `tiny_phi`: `j` is odd, so integer division gives the same quotient;
  - `|` against `^` in `odd_part`: the bit being set is not in the fraction field.
  A first run left the power-of-two helpers' and the table's tail-sum mutants alive; they were invisible to
  results (scale invariance; an error below the rounding test's margin), and `the_power_of_two_helpers_are_exact`
  and `the_fast_value_is_within_its_certified_bound_of_the_accurate_value` now kill them.
