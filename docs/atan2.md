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
| Accurate path: one cubic Newton step in `Q256` (§5) | **certified** (Gappa): relative error below `2^-190.6`, given the facts §5 lists; and **proved in Coq for the transcription** (`Atan2Accurate.v`), the facts discharged: within `5.2·10^-58` (`2^-190.29`) of the form's value |
| Correct rounding (§6) | wherever the test decides (and on the tiny path), and on every pair of [CM]'s list; **not** claimed over the whole domain (§6). The Coq end-to-end theorem (`Atan2Entry.v`) states exactly this, with the list's completeness as an explicit hypothesis (`CoreMathAtan2`) |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§7) | done by the formal lane (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Coq transcription of the Rust (`formal/atan2/Atan2Kernel.v`) compared with it bit for bit (§7) | **done**: the entry (special values, forms, tiny ratios), the fast path and its decision at every form, the accurate path (before rounding), 11,477 corpus cases; five planted faults (a series coefficient, the scale, the subnormal midpoint's exponent, Newton's numerator sign, the doubling of `π/2`) each give mismatches |
| Coq proofs about the transcription (§7) | **done**, no `Admitted`: the double-word ratio and the 64 segments' and the series' fast values (`Atan2Ratio.v`, `Atan2Segments.v`, `Atan2SeriesSmall.v`, `Atan2Fast.v`), the four forms and their composition (`Atan2Forms.v`, `Atan2FastPath.v`: every fast value within `2^-62` relatively), the rounding decision lowered to `2^-905` (`Atan2Decide.v`), the accurate path (`Atan2Newton*.v`, `Atan2Accurate.v`), the tiny ratios including the subnormal midpoints (`Atan2Tiny*.v`, `Atan2Odd.v`, `Atan2Decode.v`), the constants (`Atan2Consts.v`), and the public entry over every binary64 pair (`Atan2Entry.v`). What the proofs do **not** establish: that the Rust code is the transcription (the corpus comparison above is the only link), correct rounding off the rounding test's decisions and off [CM]'s list (`CoreMathAtan2` is an explicit hypothesis, as are the Gappa certificates' own axioms audited by `check_formal.sh`) |
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
- **Proved in Coq for the transcription** (`Atan2Newton.v`, `Atan2NewtonReal.v`, `Atan2Accurate.v`; all
  errors scale with `t = n/d`, so the bound holds down to the smallest quotient the fast path admits):
  with `|φ₀ − φ*| ≤ 2^-63(1 + 1e-4) φ*`, the exact step is `φ₀ + tan(φ* − φ₀)`
  (`n cos φ₀ − d sin φ₀ = tan(φ* − φ₀)(d cos φ₀ + n sin φ₀)`) and `|φ* − φ₀ − tan(φ* − φ₀)| ≤
  |tan(φ* − φ₀)|³/3`; the `Q256` sine and cosine's `2^-196` relative errors, each product's `2^-255`,
  each sum's `2^-254 · max`, the reciprocal's `2^-252` and the scaling by `2^-top` are carried through
  the numerator, denominator and quotient (`newton_atan_P`); the start's `Q256` sum, `φ₀ ≤ π/4 +
  2^-62` (inside `sin`/`cos`'s `[0, 0.7854]`), `cos φ₀ ≥ 0.7071`, and `φ*/t ≥ 1/2` close the bound at
  `5·10^-58` relative to `φ*` (`newton_phi1_ok`), and the form's constant (`q_half_pi`, within `10^-70`;
  twice it for `π`) keeps the value within `5.2·10^-58` (`2^-190.29`) of `π/2 ∓ φ*`, `π − φ*`, `π/2 + φ*`
  (`atan2_accurate_ok`).

## 6. Rounding test and claims

`decide_with(Y, EPS)`, `EPS = 2^-62(1 + 2^-50)`, as [ln] §5.

- The fast bound is `2^-63.04` (the largest `compose_<kk>.g` and the series, plus the
  ratio's `2^-104`), inside `ε₁ = 2^-62`; the Coq proof (`Atan2FastPath.atan2_fast_ok`) shows each form's
  fast value within `2^-62` relatively and the start within `2^-63(1 + 2^-39)`.
- When the test passes, the result is `RN(atan2(y, x))` (`Atan2Angle.atan2_main_ok`, with the decision
  lowered to `|Y| ≥ 2^-905`, which the smallest fast value, about `2^-902`, needs).
- Otherwise the accurate value is within `2^-190.29` relatively (the Gappa certificate's tighter `2^-190.6`
  is not used by the Coq theorem), so the result is within `(1/2 + 2^-137)` ulp of `atan2(y, x)`
  (`Atan2Angle.accurate_ulp`): correctly rounded unless the value lies within `2^-190` of a midpoint
  (`Stable190`; the proofs use `2^-190`, the bound the `2^-137` slack needs). [CM]'s list is a restricted set, so no
  search excludes that over the whole domain, and **correct rounding is not claimed there**. Every pair of
  [CM]'s list is correctly rounded by the bound (the hardest is `2^-101.7` ulp from a midpoint, §2); in
  Coq that is the hypothesis `CoreMathAtan2` of `Atan2Entry.atan2_entry_correct`.
- Quotients below `2^-900` take the tiny path (§3) and are always correctly rounded (`Atan2Tiny.tiny_phi_ok`:
  `RN(n/d)` is `RN(atan(n/d))` unless `n/d` is exactly the midpoint of two subnormals, where the lower
  neighbor is the answer; no other midpoint is within `2^-108` relatively, which `atan t = t(1 − t²/3 + …)`
  cannot cross).

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
- **Per-pair probability.** The accurate bound (the Coq-proved one) is `δ = 2^-190.29`. A value equidistributed past
  the 54th bit has a midpoint inside the two-sided window `±δ|Z|` with probability
  `2δ|Z|/ulp(Z)`; with `|Z|/ulp(Z)` log-uniform in a binade (mean `2^52/ln 2`) that is `2^-136.76`.
- **Estimate.** `2^111.76 · 2^-136.76 ≈ 2^-25.0` (about `3.0·10^-8`) expected pairs whose accurate
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
| `generators/atan2_proofs.py` | `formal/atan2/Atan2Approx.v` (each of the 64 segments' polynomials approximates `atan(k/64 + t)` within `2^-63`, relatively, by `interval`) and `Atan2Segments.v` (each segment's evaluation certificate over its table words and `SegOkRow`'s facts) |
| `generators/atan2_hardness.py` | §6's heuristic figures; `--check` fails unless this document quotes them |
| `formal/atan2/Atan2{Ratio,Segment,Segments,SeriesSmall,Within,Fast,Forms,FastPath,Decide}.v` (Coq 8.15) | the fast path: the scaled double-word ratio and its scaling, the 64 segments' and the series' evaluations, the four forms, the composition `atan2_fast_ok` (every form's fast value within `2^-62` relatively, normalized, in the decision's range), and the rounding decision lowered to `2^-905` |
| `formal/atan2/Atan2{Recip,Newton,NewtonReal,Accurate}.v` | the accurate path: the scaled `Q256` reciprocal, the exact Newton step for `atan`, its real-arithmetic bound with every rounding carried, and the computed value within `5.2·10^-58` of each form |
| `formal/atan2/Atan2{Odd,Decode,TinyMid,Tiny,Consts}.v` | the tiny ratios: the odd part of an encoding, the midpoints as odd multiples of a power of two, a quotient's relative distance from them, the subnormal-midpoint case, and the constants as correctly rounded values |
| `formal/atan2/Atan2{Angle,Angle2,Spec,Entry}.v` | the main branch (`atan2_main_ok`: correct where decided, within `(1/2 + 2^-137)` ulp otherwise), the tiny and main paths against the real angle, the public entry over every binary64 pair: NaN, the special-value table, signs and quadrants, the finite contract and its corollary under `CoreMathAtan2` |
| `generators/atan2_reference.py` | the fixture: the 40 hardest pairs of [CM], every pair of special values, the subnormal midpoints, the segment and ratio boundaries, random pairs |

The binding `formal/atan2/binding.sha256` covers this document, the Sollya script
and output, the generated tables, every certificate, the generators of the Coq facts, every Coq file above and the source `atan2/mod.rs`.

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
