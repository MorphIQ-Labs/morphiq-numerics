# `asin`

`morphiq_numerics::elementary::asin` (`crates/morphiq-numerics/src/asin/`) follows this derivation:
- a complement reduction above `√½`;
- a table-driven double-word fast path;
- the rounding test;
- an accurate path: one Newton step in `Q256`, from the fast path's result.

This document states what each check establishes and what it does not. Nothing
below claims more than the named artifact does.

## Status

| Item | State |
|---|---|
| Specification, special values and the `asin x = x` threshold (§1) | done; threshold by oracle bisection and §1's argument |
| Fast path: 45 segments, the series, the complement (§3, §4) | **certified** (Gappa): relative error below `2^-63.5` |
| Rounding test at `ε₁ = 2^-62` (§6) | sound given the fast bound, as [ln] §5 |
| Remaining facts outside Gappa (§4 and §5) | **proved in Coq** (`AsinApprox.v`, `AsinLip.v`, `AsinWithin.v`, `AsinQSeries.v`, `AsinSinCos.v`, `AsinRecip.v`, `AsinNewton.v`) by `interval`, replacing the Sollya and `mpmath` claims |
| Accurate path: Newton step in `Q256` (§5) | **certified** (Gappa): relative error below `2^-124.8`, given the facts §5 lists |
| Correct rounding on `[0x1.7137449123ef6p−26, 1)` (§6) | **proved in Coq** for the transcription (`AsinCorrect.v`: `positive_correct`), given `CoreMath`, the published worst-case search; the Rust is tied to the transcription by the corpus (next row) |
| Coq transcription of the Rust (`formal/asin/AsinKernel.v`) compared with it bit for bit (§7) | **done**: reduction, series, fast path, rounding decision, accurate path (before rounding) and entry, 19,532 corpus cases |
| Proof that the transcription's series branch evaluates as `series_tail.g` models (`AsinSeriesSmall.v`: `series_small_eval`) | **proved in Coq**: `B h + B l = (zh + zl + Tx (1 + ec))(1 + ea)`, `Tx = zh³ P(zh²)` exact, `|ec| ≤ 2^-51`, `|ea| ≤ 2^-104`; the step to `asin z` (Sollya's bound on `P`, the series of `asin`) is `series_compose.g`'s hypotheses, stated not proved |
| Proof that the transcription's complement reduction meets `sqrt.g` (`AsinSqrtStep.v`: `reduced_complement`) | **proved in Coq**, applying the generated certificate theorem |
| Proof that the transcription's table-segment branch evaluates as `eval_<kk>.g` models (`AsinSegment.v`: `series_segment`; `AsinSegments.v`: `segok_all`) | **proved in Coq**, for every `k = 1..45`: `B h + B l = (c0 + c1 + (c_hi + c_lo) t + t² G(t) + e1)(1 + ea)`, `t = (zh − k/64) + zl` exact, `G` the segment's polynomial at the table's own coefficients, `\|e1\| ≤ 2^-63` (each segment's generated bound), `\|ea\| ≤ 3u²/(1 − 4u)`, `u = 2^-53`; the step to `asin(a + t)` (Sollya's bound on `G`, the double-word accuracy of `asin a` and `c1`) is `compose_<kk>.g`'s hypotheses, stated not proved |
| Proofs that the rest of the transcription meets §4 and §5's bounds | **proved in Coq**: the fast path (`AsinPath.v`: `fast_direct`, relative error ≤ `2^-63`; `fast_complement`, ≤ `2^-62`, both with the leading word normalized), the rounding decision (`AsinCorrect.v`: `decide_some`), and the accurate path (`AsinAccurate.v`: `accurate_direct`, `accurate_complement`, relative error ≤ `2^-124`, with the `Q256` sine and cosine series within `2^-196` and the reciprocal within `2^-252`) |
| Entry point over every binary64 input (`AsinEntry.v`) | **proved in Coq**: `asin_entry_finite` (`\|x\| ≤ 1`: `RN(asin x)`, sign through the encoding, `±RN(π/2)` at `±1`, `x` below the threshold, `AsinSmall.v`), `asin_entry_nan`, `asin_entry_inf`, `asin_entry_large` (`\|x\| > 1`: NaN) |
| The Taylor remainders, the argument ranges, `sin t/t` (§5) | **proved in Coq** (`formal/asin/AsinFacts.v`) |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§7) | **done** (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Mutation witnesses | **done** (§7, decision on cargo-mutants): 135 mutants of `asin/mod.rs` and `asin/lanes.rs`, 117 caught, 16 unviable, 1 timed out (counted as detected), 1 equivalent |
| ARM NEON, SSE2, AVX2+FMA, AVX-512F lanes; `asin_slice` | **done** (`asin/lanes.rs`, [lanes.md](lanes.md)): bit-identical to `asin` on every cascade over the fixture, thresholds, `k/64` shifter edges, the complement, and random encodings; run on NEON, and on x86-64 SSE2 under Rosetta; AVX-512F is CI's SDE job |
| Same-host performance against the best alternatives | measured on NEON only: 1.10–1.16× over the scalar loop ([measurements](../crates/reference/measurements/asin-asinh-atan2-m1pro/README.md)); native x86 not measured |

## Sources

- **[CM]** CORE-MATH, `src/binary64/asin/asin.wc` at commit
  `0ce0cbc15935e24c656280e5a46c34e89f301b7a` (SHA-256
  `c7869311e52f598490c4d67f57f1fd6b25737da7672cd3b266704426a9970830`, MIT): the
  inputs with at least 43 identical bits after the round bit on
  `2^-26 ≤ x ≤ 1`, found with BaCSeL. Used as test inputs and to size the
  accurate path (§2), never as code.
- **[M]** J.-M. Muller, *Elementary Functions*, 3rd ed., 2016: argument
  reduction, the rounding test's setting.
- **[DW]** [double-word.md](double-word.md): the double-word operations' proved bounds.
- **[ln]** [ln.md](ln.md) §5: the rounding test.
- **[sin_cos]** [sin_cos.md](sin_cos.md) §5: the `Q256` `sin`/`cos` series.

## 1. Specification

| Input | `asin` |
|---|---|
| NaN | NaN |
| `\|x\| > 1`, `±∞` | NaN |
| `±0` | `±0` |
| `\|x\| < 0x1.7137449123ef6p−26` | `x`, exactly (*generated*, below) |
| `±1` | `±RN(π/2)` = `±0x1.921fb54442d18p+0` |
| otherwise | §3–§6 |

**The `asin x = x` threshold.**
- `asin x = x + x³/6 + 3x⁵/40 + …`, and `asin x − x ≤ (x³/6)(1 + x²)` for `x ≤ 1/2`.
- In the binade `x = m·2^e`, `x` is the nearest binary64 to `asin x` when
  `m³·2^(2e)·(1 + x²) < 6·2^-53`. At `e = −26` that is `m ≤ 3^(1/3) = 1.4422…`;
  for `e ≤ −27` it holds for every `m < 2`; for `e ≥ −25` it fails.
- `generators/asin_reference.py` finds the least `x` whose correctly rounded `asin`
  differs from `x` by bisection with the interval oracle, and writes it to the
  fixture: `0x1.7137449123ef6p−26`. The function compares `|x|` against it.

**Odd symmetry.** The function computes `asin |x|` and applies the sign of `x`.

`generators/asin_reference.py` writes the fixture `crates/reference/fixtures/asin.json`.

## 2. Accuracy needed

[CM]'s list holds every argument on `2^-26 ≤ x ≤ 1` whose `asin` lies within
`2^-43` ulp of a rounding midpoint. Re-measured here at 400 bits, the closest
is `x = 0x1.c373ff4aad79bp−14`, `2^-58.6` ulp from a midpoint; the next are
`0x1.a4816b2066707p−5` (`2^-55.5`) and `0x1.7137449123ef6p−26` (`2^-55.5`).

So an accurate path whose relative error is below `2^-(53 + 59 + 1) = 2^-113`
rounds correctly on every listed argument (a relative error `r` is at most
`r·2^53` ulp, and `2^-113·2^53 = 2^-60` is below the closest `2^-58.6`), and every unlisted
argument is farther than `2^-43` ulp from a midpoint. The completeness of [CM]'s list is a published
result that this repository accepts; it is not re-derived here.

Below `x = 0x1.7137449123ef6p−26` the answer is `x` (§1).

## 3. Reduction

`SPLIT = 0x1.6a09e667f3bccp−1`, the largest binary64 below `√½`.

- **`x ≤ SPLIT`:** `y = asin x < π/4`; the fast path evaluates `asin(z)` at `z = x`.
- **`x > SPLIT`:** `y > π/4`, and
  `asin x = π/2 − δ`, `δ = 2·asin(w)`, `w = √((1 − x)/2)`.
  - `1 − x` is exact for `x ∈ [1/2, 1)`, and so is the halving: `u = (1 − x)/2`.
  - `s = RN(√u)`; `(p, q) = two_prod(s, s)`; `s_lo = RN(RN(RN(u − p) − q)/(2s))`;
    the double-word `z = s + s_lo` equals `w` within `2^-103` relatively, since
    `z − w = (s − w)²/(2s)` plus three roundings (*certified*: `formal/asin/sqrt.g`).
  - The result is `π/2 − 2·F(z)` with the double-word `π/2` (*generated*,
    relative error below `2^-107`).
  - `y ≥ π/4` and `δ ≤ π/4`, so the subtraction loses no bit to cancellation.
- **Why the accurate path needs `δ`.** Recovering `δ` as `π/2 − y` from a result
  accurate to `2^-63` absolute would leave `δ` with a relative error up to
  `2^-37` at `x → 1`, where `δ ≈ 2^-26`. The fast path therefore returns `δ`
  itself for the complement, to the accurate path (§5).

## 4. Fast path

**Decision 1: a table at `a = k/64`, `k = 1..45`, and one polynomial per segment in
`t = z − a`, `|t| ≤ 0.0078126`.**
1. `z = z_hi + z_lo` (a double-word; `z_lo = 0` on the direct branch).
2. `i = RN_int(64·z_hi)`; `k = i`. `z_hi − i/64` is exact by Sterbenz's lemma for
   `i ≥ 1`, and `t = (z_hi − i/64) + z_lo` is formed by `two_sum`, so `t = t_hi + t_lo` exactly.
3. `asin(a + t) = asin(a) + c₁·t + t²·G_k(t)`, `c₁ = 1/√(1 − a²)`:
   - `asin(a)` and `c₁` are the table's double-words (*generated*, relative error
     below `2^-107`).
   - `G_k` is degree 8 with binary64 coefficients (*generated*: Sollya `fpminimax`,
     absolute, `generators/asin_poly.sollya`). Its error against the true
     `G` is Sollya's `supnorm` plus the omitted Taylor terms, bounded by Cauchy's
     estimate on `|t| = (1 − a)/2` from the ODE recurrence of the coefficients (`u<kk>` and `r<kk>` in
     `generators/asin_poly.out`). The worst segment's relative polynomial error is `2^-67.4`.
4. Evaluation, in binary64: `g = Horner(G_k, t_hi)`; `(p_hi, p_lo) = two_prod(t_hi, c_hi)`;
   `tail = p_lo + (t_hi·c_lo + t_lo·c_hi) + RN(t_hi²)·g`; `V = fast_sum(p_hi, tail)`
   (exact); `F = (asin a) ⊕ V` with `add` (3u²/(1 − 4u), [DW]).
5. **Below `1/128`:** `asin z = z + z³·P(z²)`, `P` of degree 3 (Sollya, relative
   `2^-54`), `F = z ⊕ RN(RN(z_hi·u)·p)` with `add_f64` (2u², [DW]).

**Certified** (Gappa 1.4.1, `-Eprecision=400`; `generators/asin_certificates.py`):

| Certificate | Establishes |
|---|---|
| `formal/asin/eval_<kk>.g` (45) | the binary64 tail, Horner chain included, is within `4·T²·2^-52·sup\|G_k\|` of the exact polynomial's value after `p_hi` (at most `2^-64.0` absolute; the proven bound is within `2^1.6` of the claim) |
| `formal/asin/compose_<kk>.g` (45) | the fast result is within `2^-63.5` (`k = 45`) to `2^-64.8` (`k = 9`) of `asin(a + t)`, relative |
| `formal/asin/series_tail.g`, `series_compose.g` | on `z` in `[2^-28, 0.0078126]`: the series' cubic term within `2^-51`; the fast result within `2^-66.5` of `asin z`, given `rc ≤ 1.1·10⁻⁵` and `eps ≤ 2^-50`, the sum of the tail's `2^-51`, Sollya's `2^-54(1 + 2^-23)` and `3.1·2^-53` for `zl` and the rounding of `zh²` (the generator asserts that sum) |
| `formal/asin/sqrt.g` | `z` within `2^-103` of `w` |
| `formal/asin/complement.g` | the complement's result within `2^-63.6` of `asin x` |

The dominant term at the large segments is the neglected `t_lo` inside `t²`:
about `2^-66·sup G`.

**Outside the certificates, proved in Coq** (`AsinSegment.v`, `AsinApprox.v`, `AsinLip.v`): the index `i = RN_int(64·z_hi)` keeps `|t| ≤ 0.0078126` and `i ≤ 45` (direct) or `i ≤ 24` (complement); each segment's polynomial is within its budget of `asin(k/64 + t)`, by `interval` on `sin(S ± E) − v` and `sin` monotonicity (`asin_within`); and `asin(zv)/asin(w) − 1 ≤ 1.1·(zv/w − 1)` through the Lipschitz bound `asin_lip`.

## 5. Accurate path

**Decision 2: one Newton step in `Q256`**, from the fast path's double-word.
- **`x ≤ SPLIT`:** `y₁ = y₀ + (x − sin y₀)/cos y₀`, with `(sin y₀, cos y₀)` from
  [sin_cos] §5's series and `recip` from `Q256`.
- **`x > SPLIT`:** `δ₁ = δ₀ + (cos δ₀ − x)/sin δ₀`, `y = π/2 − δ₁`, with `δ₀` the fast
  path's `δ`.
- The step is quadratic: with a start error `e₀`, the new error is
  `½·tan(ξ)·e₀²` (direct) or `½·cot(ξ)·e₀²` (complement). With
  `e₀ ≤ 2^-63.5·y₀` that is below `2^-126`, against the `2^-113` needed (§2).

**Certified** (Gappa 1.4.1, `-Eprecision=400`): `formal/asin/newton_direct.g` and
`newton_complement.g` prove a relative error below `2^-124.8` for each branch (`2^-124.849` and
`2^-124.848` proven; the files claim `2^-124`). The quadratic term dominates; everything
else is below `2^-144`. The hypotheses are named in the certificates:
- the start's relative error `η ≤ 2^-62` (§4, asserted by the generator);
- `sin` and `cos` at an exact argument within `2^-198` (`formal/trig/accurate_sin.g`,
  `accurate_cos.g`, whose reduction term is zero here), and `Q256::recip`'s `650·2^-262`
  (`formal/trig/recip_3.g`), read from those files by the generator;
- `Q256`'s contract: a product truncated by at most `2^-255`, a sum within `2^-254` of its
  larger operand (§5 of [sin_cos], proved in Coq in `formal/q`).

**Proved in Coq, outside the certificates** (`formal/asin/AsinFacts.v`, built and axiom-audited by
the formal lane, `check_formal.sh` step 6). The Taylor remainder uses no mean value theorem:
`sin(y₀ + d) = sin y₀ cos d + cos y₀ sin d`, with `0 ≤ 1 − cos d ≤ d²/2` and `|sin d − d| ≤ |d|³/6`
from the standard library's alternating Taylor bounds (`sin_bound`, `cos_bound`).
- `taylor_sin`, `taylor_cos`: for `y₀` (or `d₀`) in `[0, π/4]` and `|d| ≤ 2^-61`,
  `sin(y₀ + d) = sin y₀ + cos y₀·d − rr·d²` and `cos(d₀ + d) = cos d₀ − sin d₀·d − rr·d²` with
  `rr` in the certificates' range `[−2^-60, 0.5000001]`;
- `sin_split_range`, `cos_split_range`: `sin Y ≤ SPLIT` gives `Y ≤ π/4 − 8·10⁻¹⁷`, and
  `cos D ≥ SPLIT⁺` gives `D ≤ π/4 − 6·10⁻¹⁷`, so the Newton step's start stays in `[0, π/4]`
  (a start error is at most `2^-62·π/4 = 1.7·10⁻¹⁹`);
- `y_lower` (`Y ≥ 2^-26`), `d_lower` (`D ≥ 2^-27` for `x ≤ 1 − 2^-53`), `sin_ratio`
  (`sin t ≥ 0.89 t` on `(0, π/4]`) and `quarter_pi_ranges` (`cos y₀ ≥ 0.7071`, `sin y₀ ≤ 0.70711`).
They are stated as the certificates' hypotheses; the formal lane does not machine-link a certificate
to the lemma it assumes (the proofs about the Rust's transcription, which would, are not written).

The accurate path's facts are proved in Coq rather than assumed: the `Q256` sine and cosine series
(`AsinQSeries.v`, `AsinSinCos.v`), the three-step reciprocal (`AsinRecip.v`) and the Newton step's
algebra (`AsinNewton.v`, `AsinAccurate.v`). The facts the fast path uses outside Gappa are listed in §4.

The rewrite hints' algebra, which Gappa takes on trust, is proved in Coq by the formal
lane (each hint a lemma proved by `field`, `formal/gappa/Hints.v`); the generator also checks every
hint in exact rational arithmetic at random points, so a slip fails generation before it fails
the lane.

## 6. Rounding test and claims

**Decision 3: `ε₁ = 2^-62`** in [ln] §5's test, with `EPS = 2^-62·(1 + 2^-50)`,
shared with `sin`. The certified fast bound is below `2^-63.5`.
- At that `ε₁` the test sent fewer than 1% of 200,000 random arguments to the
  accurate path (the exact rate is not yet measured).

**Claims:**
- **Certified:** the fast path's result is within `2^-63.5` of `asin x`, relative (§4), and
  the accurate path's within `2^-124.8` (§5).
- **Correct rounding** on `[0x1.7137449123ef6p−26, 1)` follows: the test accepts `y_hi` only
  when the fast bound places the true value in `y_hi`'s rounding cell; otherwise the
  accurate value, `2^-124.8·2^53 = 2^-71.8` ulp from `asin x`, is closer than the nearest midpoint
  can be (`2^-58.6` ulp, §2), so rounding it gives `RN(asin x)`. This rests on [CM]'s
  list being complete (a published result, §2), stated in Coq as `CoreMath`: no binary64
  midpoint within `2^-124` relatively of `asin a`, where [CM]'s distance is at least `2^-110`.
- **Proved in Coq:** that the transcription of the Rust returns `RN(asin x)` for every finite
  `|x| ≤ 1`, NaN for `|x| > 1` and for infinities, and passes NaN through (`AsinEntry.v`), from
  `CoreMath`, the certificates and the lemmas above; the primitive integers and floats that
  CoqInterval computes with are Coq's own axioms (`formal/axioms.int63.expected`,
  `formal/axioms.float.expected`).
- **Not established:** that the Rust is the transcription, as a theorem.
  `formal/asin/AsinKernel.v` transcribes `asin/mod.rs` operation for operation and the formal lane
  runs it against the Rust on 19,532 corpus cases, so a difference in an operation, its order or a
  table word shows (§7); no tool checks the Rust against the transcription beyond that corpus.
  `CoreMath` is a published search, not proved here.
- **Tested:** the fixture's 5,970 cases match bit for bit, including the 40
  hardest of [CM].

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/asin_poly.sollya` (Sollya 8.0) | the polynomials and their bounds, in `generators/asin_poly.out` |
| `generators/asin_constants.py` | `src/asin/tables.rs`: the table, the polynomials, `π/2`; spot-checks each segment's polynomial against `mpmath` at 400 points |
| `generators/asin_certificates.py` | writes every certificate in `formal/asin` (96) |
| `formal/asin/AsinKernel.v`, `AsinTables.v` (Coq 8.15) | the transcription of `asin/mod.rs` and its generated constants; extracted by `formal/extraction/InternalCrosscheck.v` and run against `src/internal_crosscheck/asin.rs`'s corpus by `check_formal.sh` step 7 |
| `formal/asin/AsinSqrtStep.v` (Coq 8.15) | `reduced_complement`: for `x` in `[SPLIT⁺, 1 − 2^-53]`, `asin_reduced x` takes the complement branch and returns a double-word within `2^-103` of `sqrt((1 − x)/2)`, relatively; it applies `asin_sqrt.l1` (the generated proof of `sqrt.g`), after showing `1 − x`, the halving, `two_prod`, the two subtractions, the doubling, the division and `two_sum` behave as the certificate's rounding model |
| `formal/asin/AsinSeriesSmall.v` (Coq 8.15) | `series_small_eval`: for a binary64 double-word `(zh, zl)` with `zh` in `[2^-28, 2^-7]`, `zh = RN(zh + zl)` and `\|zl\| ≤ zh/2`, `asin_series` takes the series branch (`index_zero`: the shifter index is 0, by `ExpReduction.shifter_round`) and returns `(h, l)` finite with the evaluation above, from `series_tail.g`'s generated proof (applied at its real variable, with the nine rounded operations' ranges) and `add_f64_ieee` |
| `formal/asin/AsinSegment.v`, `AsinSegments.v` (Coq 8.15, Interval) | `series_segment`: for `zh` in `[1/128, 0.7072]` with `k = round(64 zh)` in `1..45` and a double-word tail `\|zl\| ≤ 2^-60`, `asin_series` takes the table branch (`segment_reduction`: the shifter index is `k`, `k/64` and `zh − k/64` are exact) and returns `(h, l)` finite with the evaluation above. It composes `t_split` (the second `two_sum`, `\|th\| ≤ 0.0078126`, `\|tl\| ≤ 8.7e-19`), the Horner chain's range, `two_prod` on `th·c_hi`, `tail_facts` (every tail operation finite, `\|tail\| ≤ 2^-4 \|th\|`), `fast_two_sum`'s exactness, `two_sum`, `add_ieee` and `eval_<kk>.g`'s generated proof through `EvalCert`, with `G(th + tl) − G(th)` bounded by `pl_diff`. `AsinSegments.v` (written by `generators/asin_certificates.py`) discharges `SegOkRow` for each `k` from the table words and the 45 certificates, and `segok_all` dispatches |
| `formal/asin/AsinFacts.v` (Coq 8.15, Interval) | §5's Taylor remainders, argument ranges and `sin t/t` |
| `formal/asin/*` (Gappa 1.4.1, at 400 bits) | §4's evaluations, compositions, series, square root and complement; §5's two Newton steps |
| `generators/asin_reference.py` | the fixture: the 40 hardest arguments of [CM], the threshold and its neighbours, special values, multiples of 1/64, the crossover, arguments next to 1, random arguments |

The binding `formal/asin/binding.sha256` covers this document, the Sollya script
and output, the generated tables, every certificate, `AsinFacts.v` and the source `asin/mod.rs`.

**Checked by:**
- `check_formal.sh` step 7: the extracted transcription reproduces the Rust bit for bit on 19,532 cases
  (the entry, the reduction, the series, the fast path with its decision, the accurate path's `Q256`
  value before rounding, and `sin`/`cos` and `Q256::recip` each on its own: through the rounded result the
  Newton correction, about `2^-63` relative, and through the `Q256` value `recip`'s third step are invisible).
- Mutation testing of the comparison (by hand, in a local harness, not a gate): eleven planted faults in the
  transcription, namely the reduction's operation order, a table coefficient (`g0`, `g1`), the rounding-test
  constant, both Newton residual signs, the cosine series' steps, the series' order, `recip`'s Newton steps,
  the `Q256` value of `π/2`, and a Horner coefficient, each give 113 to 9,197 mismatches. One does not: a
  high-order table bit (`g8`'s bit 30) is absorbed by the binary64 Horner chain and changes no output, so only
  the generator's replay (`asin_constants.py --check`) guards the table's low-order words.
- `crates/reference/tests/asin.rs`: 5,970 cases, bit for bit.
- `src/asin/tests.rs`: special values, oddness, the branch boundary, and 200,000
  random arguments on which every fast-path decision equals the accurate path's result.
- The formal lane's Coq proof of each certificate (`check_formal.sh` step 5): 96 proofs, each hint
  proved, the global axioms those theorems rest on equal to `formal/axioms.expected`'s classical-real set.
  It found one wrong hint (`series_compose.g`), now fixed, and missing side conditions on four more.
- A negative control was run by hand on eight certificates (one of each kind): shrinking the claimed
  bound makes Gappa exit non-zero. It is not a gate.
- **Mutation.** cargo-mutants 27.1.0 over `asin/mod.rs` and `asin/lanes.rs`, built with the `simd`
  feature and run against `asin`'s unit tests, the reference fixture, the determinism digest and the lane
  suites, generates 135 mutants. 117 are caught by a failing test, 16 do not compile, and one (`replace *
  with / in series`) makes the tests run past their timeout, which also detects it. One is equivalent:
  `decided >> i & 1` against `decided << i & 1` in the lane kernel's fallback loop sends every lane after the
  first through the scalar `asin`, which returns the same bits, so only the speed differs.
