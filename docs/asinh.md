# `asinh`

`asinh(x) = sign(x)·ln(|x| + √(x² + 1))`, correctly rounded over binary64:
a certified fast path in double-word arithmetic, the shared rounding test, and
a `Q256` accurate path. The code is `crates/morphiq-numerics/src/asinh/`; the
constants are generated and every bound is a Gappa certificate in
`formal/asinh`.

## Status

| Item | State |
|---|---|
| Specification, special values and the `asinh x = x` threshold (§1) | done; threshold by oracle bisection |
| Fast path: series, `ln(x + √(x² + 1))`, large form (§3) | **certified** (Gappa): relative error below `2^-63` |
| Rounding test at `ε₁ = 2^-63` (§5) | sound given the fast bound, as [ln] §5 |
| Accurate path: two Newton steps for `sinh y = x` in `Q256` (§4) | **certified** (Gappa): relative error below `2^-216`, given the facts §4 lists |
| Correct rounding on `(0x1.7137449123ef6p−26, ∞)` (§5) | **proved in Coq for the transcription** (`asinh_entry_finite`), given `CoreMathH`, the hypothesis that [CM]'s worst-case list is complete (no binary64 midpoint within `2^-124` of `arcsinh a`); the Rust is tied to the transcription by the 13,030-case corpus, not by a proof |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§6) | done by the formal lane (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Coq transcription of the Rust (`formal/asinh/AsinhKernel.v`) compared with it bit for bit (§6) | **done**: fast path, rounding decision, exponential, accurate path (before rounding) and entry, 13,030 corpus cases; four planted faults (a series coefficient, the root's correction, Newton's residual sign, the large form's correction) each give mismatches. The proofs in `formal/asinh/` (below) show it meets §3 and §4's bounds |
| Coq proofs over the transcription (`formal/asinh/Asinh*.v`, no admits, axioms audited in `formal/audit/KernelAudit.v`) | **done**: series, logarithm and large fast paths each within `2^-63` relatively (series `2^-66`); the rounding decision at `2^-63` returns only `RN(arcsinh x)`; the `Q256` exponential, reciprocal and Newton step; the accurate path within `2^-124` relatively (weaker than the `2^-216` Gappa figure, and all the rounding needs); `asinh x = x` for `|x| ≤ 0x1.7137449123ef6p−26` with its sign; special values and sign through the encoding. Entry: `asinh_entry_finite` (finite `x`: result is `RN(arcsinh x)` given `CoreMathH`), `asinh_entry_nan`, `asinh_entry_inf` |
| ARM NEON, SSE2, AVX2+FMA, AVX-512F lanes; `asinh_slice` | **done** (`asinh/lanes.rs`, [lanes.md](lanes.md)): bit-identical to `asinh` on every cascade over the fixture, thresholds, region edges and random encodings; run on NEON and on x86-64 SSE2 under Rosetta; AVX-512F is CI's SDE job |
| Mutation witnesses | **done** (§6): 98 mutants of `asinh/mod.rs` and `asinh/lanes.rs`, 72 caught, 22 unviable, 4 equivalent |
| Same-host performance against the best alternatives | measured on NEON only: 1.01–1.66× over the scalar loop ([measurements](../crates/reference/measurements/asin-asinh-atan2-m1pro/README.md)); native x86 not measured |

## Sources

- **[CM]** CORE-MATH, `src/binary64/asinh/asinh.wc` at commit
  `0ce0cbc15935e24c656280e5a46c34e89f301b7a` (SHA-256
  `c5835d0d56244e3ce1455358225934c9c5360c2abb7de512680bc9d64ea29e30`, MIT): the
  inputs with at least 43 identical bits after the round bit on
  `0x1.7137449123ef6p-26 ≤ x < 2^1024`, found with BaCSeL. Used as test inputs
  and to size the accurate path (§2), never as code.
- **[M]** J.-M. Muller, *Elementary Functions*, 3rd ed., 2016.
- **[DW]** [double-word.md](double-word.md): the double-word operations' proved bounds.
- **[ln]** [ln.md](ln.md) §4 and §5: the double-word logarithm and the rounding test.
- **[sin_cos]** [sin_cos.md](sin_cos.md) §8: `Q256::recip`'s certified bound.

## 1. Specification

| Input | `asinh` |
|---|---|
| NaN | the NaN |
| `±0` | `±0` |
| `±∞` | `±∞` |
| `\|x\| ≤ 0x1.7137449123ef6p−26` | `x`, exactly (*generated*, below) |
| otherwise | §3–§5, odd in `x` |

**The `asinh x = x` threshold.** `asinh x = x − x³/6 + 3x⁵/40 − …` lies below `x`
by about `x³/6`, so `x` is the nearest binary64 while `x³/6` is below half the
gap toward zero. The oracle (`generators/asinh_reference.py`) bisects the least
argument whose `asinh` is not `x`: `0x1.7137449123ef7p−26`. It is the same
threshold as `sin` and `asin` share, and it is where [CM]'s list begins.

## 2. Accuracy needed

[CM]'s list is complete for the domain it covers, so no input outside it is
closer than `2^-43` ulp to a midpoint, and the hardest listed one, ranked here
at 400 bits over the whole list, is 62.03 bits from one
(`0x1.fd15daa6ce332p+731`). The accurate path's `2^-216` (Gappa; the Coq proof uses `2^-124`, which
`CoreMathH` also names) is far inside that.
`asinh x` is transcendental for `x ≠ 0`, so it is never a midpoint.

## 3. Fast path

For `a = |x| > 0x1.7137449123ef6p−26`, the result `Y` is a double-word.

- **`a < 2^-7`: the series.** `asinh a = a − a³·Q(a²)`, `Q` of degree 3 in `a²`
  (`generators/asinh_poly.sollya`: relative error `0x1.000002p-54`). The kernel
  evaluates `P = −Q` with the coefficients' signs, which is the same operations
  negated. `Y = a + RN(RN(a·a²)·P(a²))` by `DoubleWord::add_f64`. Certified:
  `series_tail.g` (the tail, `2^-51`) and `series_compose.g` (`2^-66.4`).
- **`2^-7 ≤ a < 2^28`: `ln(a + √(a² + 1))`.** `a²` is exact by `two_prod`;
  `u = 1 + a²` is a double-word; `s = √u` is `root = RN(√u_hi)` plus the Newton
  correction `RN(r/(2·root))`, `r = ((u_hi − root²_hi) − root²_lo) + u_lo`
  (`root.g`: `2^-100`); `v = a + s` is a double-word. Then
  `Y = ln(v_hi) + RN(v_lo/v_hi)`, with `ln(v_hi)` the double-word of `ln`'s fast
  path ([ln] §4, within `2^-64`). Certified: `log.g` (below `2^-63`).
- **`a ≥ 2^28`: `ln a + ln 2 + 1/(4a²)`.** `asinh a = ln 2a + t/4 − 3t²/32 + …`,
  `t = 1/a² ≤ 2^-56`, so the omitted terms are below `2^-114`. `ln a` is `ln`'s fast
  path, `ln 2` a double-word (`2^-109`), `1/(4a²)` is `RN(RN(¼/a)/a)`, which
  underflows harmlessly for the largest `a`. Certified: `large.g`.

Every operation is binary64, in the written order, on every target.

## 4. Accurate path

`y₀ = Y`. Two Newton steps for `sinh y = x`, `y ← y + (x − sinh y)/cosh y`, in
`Q256`.

- **The exponential.** `e^y = m·2^k`, `k = RN(y/ln 2)` in binary64,
  `r = y − k·ln 2` in `Q256` (`|r| ≤ 0.3467`), `m` the 45-term series
  `1 + r(1 + r/2(1 + r/3(…)))` with `Q256` constants (`EXP_STEPS`). Certified:
  `exp_level_01.g` … `exp_level_45.g` (each Horner level) and `exp.g`
  (the reduction's error, `2^-243.8`).
- **`sinh` and `cosh`** are `(e^y ∓ e^−y)/2` from `m` and `1/m`; the reciprocal
  scales its argument into `[1, 2)` first so `Q256::recip`'s binary64 start is
  finite for every `y` (`Q256::recip`: [sin_cos] §8, `2^-252.6`).
- **The steps.** The exact step lands at `y* + q`, `q = c₂(εy*)²/2`,
  `c₂ = sinh ξ/cosh y₀ ∈ [0, 1.001]`; the computed step adds the exponential's
  error (absolute), the reciprocal's and product's (relative to the
  correction) and the last sum's. `newton_1.g` and `newton_2.g` carry the two
  steps from `ε = 2^-63`; the result is within `2^-216.8` relatively.
- **Stated in the Gappa certificates, proved in Coq:** the mean value theorem for `sinh` (`newton_exact`) and the `Q256` operations' error model are proved over the transcription in `formal/asinh/` for the `2^-124` bound; the `2^-216.8` figure remains the Gappa certificates' with their stated facts.

## 5. Rounding test and claims

`decide_with(Y, EPS)`, `EPS = 2^-63(1 + 2^-50)`, as [ln] §5: `Y_hi` is returned when
it is provably `RN` of every real within `2^-63` of `Y`. Otherwise the
accurate value is rounded once by `Q256::to_f64`.

- The fast bound is `2^-63` (`log.g`, `large.g`; the series `2^-66.4`).
- When the test passes, the result is `RN(asinh x)`.
- Otherwise the accurate value is within `2^-216` relatively (Gappa; the Coq proof carries
  `2^-124`, all the rounding needs), and the hardest input of the domain is `2^-62` ulp from a
  midpoint ([CM], §2), so the result is `RN(asinh x)`.

So `asinh` is correctly rounded on `(0x1.7137449123ef6p−26, ∞)` given [CM]'s list
is complete, and exactly `x` below. The Coq proof covers the transcription
(`asinh_entry_finite`); `CoreMathH` is its only hypothesis beyond the
audited axioms, and the Rust-to-transcription link is the corpus comparison.

## 6. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/asinh_poly.sollya` (Sollya 8.0) | the series polynomial and its bound, in `generators/asinh_poly.out` |
| `generators/asinh_constants.py` | `src/asinh/tables.rs`: the polynomial, `ln 2` as a double-word, `Q256` `ln 2` and the series' steps; and `formal/asinh/AsinhTables.v`, the same constants for the transcription |
| `formal/asinh/AsinhKernel.v`, `AsinhTables.v` (Coq 8.15) | the transcription of `asinh/mod.rs` (with `ln`'s proved fast value, `formal/ln/LnFastValue.v`) and its constants; extracted by `formal/extraction/InternalCrosscheck.v` and run against `src/internal_crosscheck/asinh.rs`'s corpus by `check_formal.sh` step 7 |
| `generators/asinh_certificates.py` | writes every certificate in `formal/asinh` (53) |
| `formal/asinh/*` (Gappa 1.4.1, at 400 bits) | §3's series, root, logarithm and large form; §4's exponential levels, reduction and two Newton steps |
| `generators/asinh_reference.py` | the fixture: the 40 hardest arguments of [CM], the threshold and its neighbours, special values, the regions' edges, random arguments |

The binding `formal/asinh/binding.sha256` covers this document, the Sollya script
and output, the generated tables, every certificate and the source `asinh/mod.rs`.

Tests:
- `crates/reference/tests/asinh.rs`: the fixture's cases, bit for bit.
- `src/asinh/tests.rs`: special values, oddness, the regions' boundaries,
  100,000 random arguments on which every fast-path decision equals the
  accurate path's result, and the accurate path against the fast value.
- The formal lane's Coq proof of each certificate (`check_formal.sh` step 5).
- **Mutation.** cargo-mutants over `asinh/mod.rs` and `asinh/lanes.rs`, built with the `simd` feature and
  run against the unit tests, the reference fixture, the determinism digest and the lane suites,
  generates 98 mutants: 72 are caught by a failing test and 22 do not compile. Four are equivalent:
  - `<` against `==` or `<=` where `fast` chooses the series at `2^-7` (twice), and `<` against `<=`
    where it chooses the large form at `2^28`: at the boundary point both forms are valid and the
    results stay neighbouring values of one increasing function, which
    `the_regions_agree_where_they_meet` pins;
  - `>>` against `<<` in the lane's fallback loop: it only moves which decided lanes are recomputed by the
    scalar function, whose result the lane equals bit for bit.
- A negative control was run by hand: tightening `root.g`'s claim makes Gappa
  exit non-zero. It is not a gate.
