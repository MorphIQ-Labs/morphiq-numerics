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
| Remaining facts outside Gappa (§4 and §5, "Not covered") | tested or stated, not proved |
| Accurate path: Newton step in `Q256` (§5) | **certified** (Gappa): relative error below `2^-124.8`, given the facts §5 lists |
| Correct rounding on `[0x1.7137449123ef6p−26, 1)` (§6) | follows from the two bounds and [CM]'s list; **not machine-checked end to end**: the Coq transcription of the Rust is compared with it on a corpus but its bounds are not proved (next row) |
| Coq transcription of the Rust (`formal/asin/AsinKernel.v`) compared with it bit for bit (§7) | **done**: reduction, series, fast path, rounding decision, accurate path (before rounding) and entry, 19,532 corpus cases |
| Proofs that the transcription meets §4 and §5's bounds, applying the certificates | **not written** |
| The Taylor remainders, the argument ranges, `sin t/t` (§5) | **proved in Coq** (`formal/asin/AsinFacts.v`) |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§7) | **done** (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Mutation witnesses | not done |
| ARM NEON, SSE2, AVX2+FMA, AVX-512F lanes; `asin_slice` | not done |
| Same-host performance against the best alternatives | not measured |

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
| `formal/asin/series_tail.g`, `series_compose.g` | the series' cubic term within `2^-49`; the fast result within `2^-65.2` of `asin z` |
| `formal/asin/sqrt.g` | `z` within `2^-103` of `w` |
| `formal/asin/complement.g` | the complement's result within `2^-63.6` of `asin x` |

The dominant term at the large segments is the neglected `t_lo` inside `t²`:
about `2^-66·sup G`.

**Not covered by a certificate** (stated, tested, not proved here):
- `i = RN_int(64·z_hi)` keeps `|t| ≤ 0.0078126`, and `i ≤ 45` on the direct branch, `i ≤ 24` on the complement.
  Only the fixture's multiples-of-1/64 and crossover cases exercise it;
- the bound on `G(t_hi + t_lo) − G(t_hi)` uses the mean value theorem with
  `sup|G′|` summed from the coefficients in exact rational arithmetic
  (`generators/asin_certificates.py`);
- `asin(zv)/asin(w) − 1 ≤ 1.1·(zv/w − 1)` (a derivative bound: `(w/asin w)/√(1 − w²) ≤ 1.055` for `w ≤ 0.3827`);
- the bounds on the widened `A` range of each segment come from `mpmath` interval arithmetic.

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

**Not covered by a certificate or a Coq lemma** (stated, not proved here):
- `asin(zv)/asin(w) − 1 ≤ 1.1·(zv/w − 1)` in the complement (a derivative bound:
  `(w/asin w)/√(1 − w²) ≤ 1.055` for `w ≤ 0.3827`);
- `i = RN_int(64·z_hi)` keeps `|t| ≤ 0.0078126`, and `i ≤ 45` on the direct branch, `i ≤ 24` on the
  complement (only the fixture's multiples-of-1/64 and crossover cases exercise it);
- the bound on `G(t_hi + t_lo) − G(t_hi)` uses the mean value theorem with `sup|G′|` summed from the
  coefficients in exact rational arithmetic (`generators/asin_certificates.py`);
- the widened `A` range of each segment comes from `mpmath` interval arithmetic.

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
  list being complete (a published result, §2) and on the facts §5 lists.
- **Not established:** that the Rust computes the certified operation sequence, as a theorem.
  `formal/asin/AsinKernel.v` transcribes `asin/mod.rs` operation for operation and the formal lane
  runs it against the Rust on 19,532 corpus cases, so a difference in an operation, its order or a
  table word shows (§7); the proof that the transcription meets the certified bounds, which would
  also machine-link each certificate to the lemma it assumes, is not written.
- **Tested:** the fixture's 5,970 cases match bit for bit, including the 40
  hardest of [CM].

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/asin_poly.sollya` (Sollya 8.0) | the polynomials and their bounds, in `generators/asin_poly.out` |
| `generators/asin_constants.py` | `src/asin/tables.rs`: the table, the polynomials, `π/2`; spot-checks each segment's polynomial against `mpmath` at 400 points |
| `generators/asin_certificates.py` | writes every certificate in `formal/asin` (96) |
| `formal/asin/AsinKernel.v`, `AsinTables.v` (Coq 8.15) | the transcription of `asin/mod.rs` and its generated constants; extracted by `formal/extraction/InternalCrosscheck.v` and run against `src/internal_crosscheck/asin.rs`'s corpus by `check_formal.sh` step 7 |
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
