# `ln` and `ln_1p`: correctly rounded logarithms

`morphiq_numerics::elementary::{ln, ln_1p}` (`crates/morphiq-numerics/src/ln/`)
follow this derivation step for step, with [exp]'s `Q128` type. Every bound
below is certified, and every constant generated, by the artifacts in §8. Each
numbered **decision** is a design choice open to review.

`ln(x)` returns `ln x` rounded to nearest, ties to even, for every binary64 `x`.
`ln_1p(x)` returns `ln(1 + x)`, without rounding `1 + x`. It is correctly rounded
whenever one of its stages or its fast path decides the rounding, and otherwise
within a proved bound (§7). Here `u = 2^−53` and `RN` is round-to-nearest-even.

## Sources

- **[DLM]** F. de Dinechin, C. Lauter, J.-M. Muller, "Fast and correctly rounded
  logarithms in double-precision", *RAIRO – Theoretical Informatics and
  Applications* 41, 85–102, 2007, doi:10.1051/ita:2007003: the exact reduction
  shared by both paths (§3.1) and the fast path's double-word evaluation of
  `ln(1 + z)` (§3.3).
- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: the accuracy that
  decides every case (Property 2, Table 5).
- **[Ziv]** A. Ziv, "Fast evaluation of elementary mathematical functions with
  correctly rounded last bit", *ACM TOMS* 17(3), 1991: the fast path returns only
  when its result provably rounds correctly.
- **[Tang]** P. T. P. Tang, "Table-driven implementation of the logarithm
  function in IEEE floating-point arithmetic", *ACM TOMS* 16(4), 378–400, 1990,
  doi:10.1145/98267.98294: the table-driven reduction indexed by the leading
  bits that `ln_1p`'s stages use (§7).
- **[DW]** This crate's double-word arithmetic ([double-word.md](double-word.md)):
  its operations have machine-checked error bounds in IEEE 754 arithmetic.
- **[exp]** [exp.md](exp.md): the rounding test (§8.3) and the `Q128` type (§8.4),
  shared with `exp`.

Issue #30 cites Tang's table-driven logarithm (*ACM TOMS* 16(4), 1990). This
derivation follows [DLM]'s variant instead: its reduction is exact, so the fast
and accurate paths share it and its tables.

**Provenance of `ln_1p`'s stages (§7).** CORE-MATH (MIT licence), commit
`cd0b9d9091604338e9ea4f1fcb7bcd92233d6b08`, was consulted for ideas only; no
code was copied:
- `src/binary64/log1p/log1p.c`, SHA-256
  `068da268a928d8f18792e6a9ae8a0c54291925788b4e8c3b3c3c33daac220666`, read in
  full;
- `src/binary64/log1p/log1p.wc`, SHA-256
  `9b4806982f220765e89dd0378e185f68353bca01f7428c8696c2b1c0f46ad1b8`, its hard
  cases used as test inputs offline, not committed;
- `LICENSE`, SHA-256
  `81830875362f4d477637de58eecd6d458db108cc90c40904fca3694807b86de3`.

The ideas taken are listed in §7. glibc, CRlibm, Apple Libm and copyleft or
unclear-licence sources were not read.

## 1. Specification

**`ln`:**

| Input | Result | Why |
|---|---|---|
| NaN, `x < 0`, `−∞` | NaN | outside the domain |
| `±0` | `−∞` | IEEE 754-2019 §9.2 |
| `+∞` | `+∞` | |
| `1` | `+0` | exact |
| otherwise | `RN(ln x)` | §3–§6 |

**`ln_1p`:**

| Input | Result | Why |
|---|---|---|
| NaN, `x < −1`, `−∞` | NaN | outside the domain |
| `−1` | `−∞` | IEEE 754-2019 §9.2 |
| `+∞` | `+∞` | |
| `\|x\| < 2^−54`, `±0` included | `x` | correctly rounded (§7); keeps the sign of zero |
| otherwise | §7 | |

`generators/ln_reference.py` (on `main`) derives every reference value with a
rigorous interval oracle. Its fixture `crates/reference/fixtures/ln.json` is the
test reference.

## 2. Accuracy needed

[LM] Property 2: if `y*` is within mantissa distance `2^−118` of `ln x`, for any
binary64 `x`, then rounding `y*` rounds `ln x` correctly. There's no exception
range: unlike `exp`, the whole domain needs only this bound. A relative error
`ε` is a mantissa distance below `2ε` ([LM] footnote 10), so a relative error
below `2^−119` suffices. [DLM] §3.1 states the same requirement.

`ln x` is never subnormal: for `x ≠ 1`, `|ln x| > 2^−54`. So no result needs
gradual underflow, and none overflows (`|ln x| < 745`).

**`ln_1p`:** [LM] gives no worst cases for `ln(1 + x)`, so §7 states the bound
proved instead of claiming correct rounding everywhere.

## 3. Argument reduction (after [DLM] §3.1)

**Decision 1: [DLM]'s exact reduction, with 128 reciprocals of 10 significant
bits.**
1. **Subnormal `x`:** multiply by `2^54`, exactly, and subtract 54 from the
   exponent below. So `x = 2^e·m` with `m ∈ [1, 2)`, and `−1,074 ≤ e ≤ 1,023`.
2. **The index:** `i` is the top 7 bits of `m`'s fraction, so
   `m ∈ [1 + i/128, 1 + (i+1)/128)`.
   - `i < 53`: `y = m`, `E = e`.
   - `i ≥ 53`: `y = m/2`, `E = e + 1`.

   So `y ∈ [0.70703125, 1.4140625)`, an interval around 1 bounded near
   `[√2/2, √2]`, as in [DLM]. Also `−1,074 ≤ E ≤ 1,024`.
3. **The reciprocal:** `R[i]` approximates `1/y` at the centre of `i`'s
   interval, rounded to 10 significant bits. `R[0] = R[127] = 1` exactly, so
   arguments near 1 reduce with no table term (*generated*: `R_BITS`). Over
   every interval, `|y·R[i] − 1| ≤ 2^−7` (*generated* and checked).
4. **Then** `ln x = E·ln 2 + (−ln R[i]) + ln(1 + z)`, with `z = y·R[i] − 1`.

**`z` is exact, as a double-word** ([DLM]'s portable version):
1. `(p, q) = two_prod(y, R[i])`. `y·R[i]` has at most 63 significant bits, and
   `two_prod` is exact on its domain [DW].
2. `p − 1` is exact: by Sterbenz's lemma, since `p ∈ [1/2, 2]`.
3. `(z_hi, z_lo) = two_sum(p − 1, q)`, so `z_hi + z_lo = z` exactly, with
   `|z_lo| ≤ 2^−53·|z_hi|`.

`y` is a multiple of `2^−53` and `R[i]` of `2^−10`, so `z` is a multiple of
`2^−63`. So `z` is `0` or `|z| ≥ 2^−63`, and `|z_hi| ≥ 2^−64`. The certificates
assume that range (§4).

**Machine-checked:** `formal/ln/LnReduction.v` transcribes `Reduced::of`,
`Reduced::z` and `Reduced::z_exact` on binary64 and the proved `Q128`
transcription, and proves them.
- **`reduce_ok`:** for every finite `x > 0`, subnormals included, `x = 2^E·y`
  exactly, with `y` in table interval `i`, on `2^−53`'s grid, and
  `−1,074 ≤ E ≤ 1,024`. The proof reads the fields from `x`'s encoding as the
  code does.
- **`z_ok`:** `(z_hi, z_lo)` is `y·R[i] − 1` exactly, a double-word with
  `|z_lo| ≤ 2^−53·|z_hi|`, `|z| ≤ 2^−7`, and either zero or
  `|z_hi| ≥ 2^−63`.
- **`z_exact_ok`:** `z_exact` is the same value in `Q128`, normalized or zero.

`formal/ln/LnTables.v`, which `generators/ln_constants.py` writes with the
tables, proves each `R[i]` from its encoding: on `2^−10`'s grid, and within
`2^−7` of `1/y` at both ends of its interval. The formal job compares the
reduction with the Rust code bit for bit on the internal cross-check corpus.

**The three cases** for the error analysis. Each certificate is relative to
`ln x`, so it needs each term's size over `ln x`:
- **A:** `E = 0` and `R[i] = 1`. Then `ln x = ln(1 + z)`, with no other term.
- **B:** `E = 0` and `R[i] ≠ 1`. Then `|ln x| ≥ 0.003913` (`i = 126`).
- **C:** `E ≠ 0`. Then `|ln x| ≥ 0.34646`.

`generators/ln_constants.py` encloses the ratios in interval arithmetic
(`mpmath.iv`, 128 bits, outward rounding):
- over every table interval, closed and widened by `2^−52` on each side, which
  covers `ln_1p`'s `y'` (§7);
- over every exponent of the case, `−1,074 ≤ E ≤ 1,024`.

Each expression uses `ln y` once, so its enclosure is tight. No monotonicity
argument is needed.

| Case | `\|E·ln 2 / ln x\|` | `\|−ln R[i] / ln x\|` | `\|ln(1 + z) / ln x\|` |
|---|---|---|---|
| B | 0 | ≤ 1.51475 | ≤ 0.51475 |
| C | ≤ 2.00062 | ≤ 0.99205 | ≤ 0.01136 |

Every certificate's hypotheses carry these bounds widened by at least 1%.

**Machine-checked:** `formal/ln/LnTableCheck.v` proves, by one reflective
computation over the 128 intervals (`ratios_ok`), the bounds the accurate
certificates take for cases B and C (§6): `|ln(1 + z)/ln x|` below `533/1024`
in case B, and `|−ln R[i]/ln x|`, `|ln(1 + z)/ln x|` and `|E·ln 2/ln x|` below
`514/512`, `752/2^16` and `2071/1024` in case C, for every `E ≠ 0` and every
`y` in its interval widened by `2^−52`. Each interval's endpoints, `R[i]` and
`ln 2` are enclosed by `formal/ln/LnCheck.v`, a reflective enclosure of `ln`
at a rational (the series of `2·artanh`, its remainder bounded by the mean
value theorem, evaluated in integers rounded outward).

## 4. Fast path (after [DLM] §3.3)

**Decision 2: [DLM]'s portable evaluation, on the crate's proved double-word
operations.**
1. **The cubic tail.** `t ≈ z_hi³·W(z_hi)`, with
   `W(z) = c3 + z·(c4 + … + z·c9)`:
   - `w` is `W(z_hi)` by Horner's scheme in binary64;
   - `z3 = RN(z_hi·RN(z_hi²))`;
   - `t = RN(z3·w)`.

   `c3`–`c9` are binary64 coefficients from Sollya's `fpminimax` for
   `ln(1 + z) − z + z²/2`, relative, on `|z| ≤ 0.0078126` (*generated*). Their
   relative approximation error is below `0x1.0881…p−54` (Sollya's `supnorm`).
   The evaluation error of `t` is below `2^−50` relative (*certified*:
   `formal/ln/tail.g`, proves `2^−51.09`).
2. **`−z²/2`.** `(s_hi, s_lo) = two_prod(z_hi, z_hi)`, exact. Halving it is
   exact, which gives `B = (−s_hi/2, −s_lo/2)`.
3. **The cross term.** `c = RN(z_hi·z_lo)`, then `v = RN(t − c)`. That is
   `z³W − z_hi·z_lo`, with `z_lo²/2` dropped.
4. `P = DoubleWord(z_hi, z_lo).add(B).add_f64(v)`, which is `ln(1 + z)`.
   - Its relative error is below `3·2^−66 ≈ 2^−64.4` (*certified*:
     `formal/ln/p.g`, proves `2^−64.92`).
   - That covers the tail, the approximation error, `W(z) − W(z_hi)`, the dropped
     `z_lo²/2` and both double-word additions.
5. `S = NEG_LN_R[i].add(P)`. `NEG_LN_R[i]` is `−ln R[i]` as a double-word, and its
   relative error is below `2^−107.1` (*generated*: `NEG_LN_R_BITS`).
6. **Decision 3: `E·ln 2` from a 42-bit split** (after [DLM] §3.3, which uses 40
   bits).
   - `LN2_HI` is `ln 2` rounded to 42 bits, and `LN2_LO = RN(ln 2 − LN2_HI)`.
     Together they're within `2^−101.5` of `ln 2` (*generated*).
   - `E·LN2_HI` is exact for `|E| < 2^11`.
   - `(l_hi, l_lo) = two_sum(E·LN2_HI, RN(E·LN2_LO))`.
   - Its relative error against `E·ln 2` is below `2^−96.47` (*generated*).
7. `Y = DoubleWord(l_hi, l_lo).add(S)`.

The kernel adds every term, including a zero one (`E = 0`, or `R[i] = 1`);
the fast-path certificates also cover skipping it.

**The fast-path bound:** relative to `ln x`, `Y`'s error is below `2^−64`
(*certified*, by case):
- `formal/ln/fast_a.g` proves `2^−64.42`;
- `formal/ln/fast_b.g` proves `2^−65.36`;
- `formal/ln/fast_c.g` proves `2^−70.86`.

Each certificate composes four things:
- `P`'s bound;
- the tables' errors;
- `E·ln 2`'s error;
- the `add` bound `3u²/(1 − 4u)`, machine-checked [DW].

[DLM] §3.3 reports about `2^−60` for its portable fast path. The difference is
the degree-9 polynomial against [DLM]'s degree 7, with the double-word
additions certified here.

## 5. Rounding test

[exp] §8.3, unchanged, with **`ε₁ = 2^−63`**: `EPS = 2^−63·(1 + 2^−50)`, shared by
`ln` and `ln_1p`. `ln`'s fast path proves `2^−64`, and `ln_1p`'s `2^−63` (§7).
- The proof needs `ln x` not to be a breakpoint. For rational `x ≠ 1`, `ln x` is
  transcendental (Lindemann: `e^a` is transcendental for algebraic `a ≠ 0`). And
  `x = 1` never reaches the test (§1).
- Every result is normal (§2), so no scaling follows, and the test's `ulp` is
  the result's.

When the test passes, the returned `y_hi` is `RN` of the exact value. This holds
for `ln_1p` too: the test needs only the fast path's bound, not worst cases.

## 6. Accurate path

**Decision 4: [exp]'s `Q128` type, under its contract** (multiplication truncated,
relative error in `[−2^−127, 0]`; addition within `2^−126·max(|a|, |b|)`; exact
conversion from and rounding to binary64).

1. `z = y·R[i] − 1` exactly. It's computed in integer arithmetic from `y`'s and
   `R[i]`'s significands and converted to `Q128` exactly: `z` is a multiple of
   `2^−63`, with `|z| ≤ 2^−7`.
2. `ln(1 + z) = z·(1 − z/2 + z²/3 − …)`. Its series to degree 18, in Horner form:
   ```
   G_18 = 1/18;   G_k = 1/k − z·G_(k+1),  k = 17, …, 1;   Lz = z·G_1
   ```
   - `1/k` are `Q128` constants (*generated*: `RECIPROCALS`).
   - **The degree** is the least `d` whose truncation, `|z|^d / (d + 1)` (the
     first omitted term of an alternating, decreasing series), is at most
     `2^−125`. That is negligible next to `Q128`'s rounding (*generated*:
     `DEGREE = 18`).
   - Each Horner level's absolute error is bounded from the previous one
     (*certified*: `formal/ln/accurate_level_01.g` to `_17.g`). With the
     truncation, `|G_1 − ln(1 + z)/z| ≤ 818·2^−135`.
3. `Y = (E·LN2_Q128 + NEG_LN_R_Q128[i]) + Lz`.
   - `E` converts exactly.
   - `LN2_Q128` and `NEG_LN_R_Q128[i]` have relative errors below `2^−127`
     (*generated*).
   - **Unlike the fast path,** a zero term is skipped: with `E = 0` there's no
     `E·ln 2` term, and with `R[i] = 1` no table term. The certificates for cases
     A and B assume no addition there.
4. The result is `Y` rounded to binary64 once, in integer arithmetic.

**Total:** `Y`'s relative error against `ln x` is below `2^−123` (*certified*):
- `formal/ln/accurate_sum_a.g` proves `2^−125.32`;
- `formal/ln/accurate_sum_b.g` proves `2^−123.86`;
- `formal/ln/accurate_sum_c.g` proves `2^−123.51`.

That is a mantissa distance below `2^−122`, against `2^−118` needed (§2). So
rounding `Y` once rounds `ln x` correctly.

**Machine-checked:** `formal/ln/LnAccurate.v` transcribes `series`,
`Reduced::accurate_value` and `ln`'s accurate branch on the proved `Q128`
transcription (`formal/q`) and proves them:
- **`series_ok`:** the seventeen Horner levels compose, so `G_1` is within
  `782·2^−135` of the exact partial series at the computed `z`. Each level is
  its certificate's theorem (`formal/ln/LnAccurateLevels.v`, which
  `generators/ln_certificates.py` writes with the same bounds as the `.g`
  files). Its hypotheses are proved about the transcription: the `mul` and
  `add` contracts, the reciprocals' errors, and every partial series in the
  certificate's range.
- **The truncation:** `|X_1 − ln(1 + z)/z| ≤ 28·2^−135`, from
  `|ln(1 + z) − Σ_(j ≤ 18) (−1)^(j+1) z^j/j| ≤ |z|^19/(19·(1 − |z|))`, proved by
  the mean value theorem.
- **`acc_value_ok`:** `accurate_value` is within `2^−123` relatively of
  `E·ln 2 + ln y`, by case, through `accurate_sum_a.g`, `_b.g` and `_c.g`. The
  constants are proved by one reflective check per table
  (`formal/ln/LnTableCheck.v`: `−ln R[i]`, `ln 2` and `1/k` within `2^−127`),
  and the case ratios as in §3.
- **`ln_acc_ok`:** for every finite `x > 0`, `x ≠ 1`, the value is within
  `2^−123` relatively of `ln x`, and `Q128::to_f64` rounds it once.
- **`ln_accurate_ok`:** if `ln x` keeps [LM]'s mantissa distance `2^−118`
  from every rounding breakpoint (Property 2, the one stated hypothesis, as
  for `exp`), the accurate path returns `RN(ln x)`. `rounds_as` is the
  rounding step for either sign.

The internal cross-check compares the extracted transcription with the Rust
code's 128-bit value bit for bit on 4,000 `ln` arguments.

## 7. `ln_1p`

**Decision 5: two stages before the double-word path, none rounding `1 + x`.**
`ln_1p` tries stage H (§7.3), then stage B (§7.4), then `ln_1p_reference`
(§7.6), the double-word and `Q128` paths of earlier releases, unchanged. A
stage returns only when its rounding test (§7.5) proves its result is
`RN(ln(1 + x))`, with room for any value within `2^−123` of `ln(1 + x)`. So
`ln_1p` returns the bits it returned before the stages existed, at every
argument (§7.7). Every argument a stage doesn't decide, specials included, takes
the next path.

| Order | Path (`ln/stages.rs`, `ln/mod.rs`) | Screen, on the encoding (false on NaN) | Work |
|---|---|---|---|
| 1 | stage H | `2^−46 ≤ \|x\|`, `−1 < x < 2^53` | about 45 binary64 operations; no branch, no select |
| 2 | stage B | `2^−54 ≤ \|x\|`, `−1 < x < 2^1020` | about 70 operations; one branch, on `\|x\| < 2^−9` |
| 3 | `ln_1p_reference` | every other argument, and those the stages don't decide | §7.6 |

Measured on 107.4 million arguments (§9), the shares that pass each stage:

| Family | past H (stage B runs) | to `ln_1p_reference` |
|---|---|---|
| `e^d`, `d ∈ [−30, 0]` | `2^−8.6` | `2^−19.9` |
| `z²/4`, `\|z\| ≤ 6` | `2^−11.7` | `2^−21.6` |
| `1 + x = 2^U`, `U ∈ [−10, 20]` | `2^−16.7` | 0 of 5,000,000 |

The design follows [Tang]'s table-driven reduction indexed by the leading
bits, with [Ziv]'s rule that a fast result is returned only when it provably
rounds correctly. CORE-MATH's `log1p` was consulted for ideas (see Sources:
provenance). Its ideas, not its code: the exponent and index read from the
encoding, `R[i]` scaled by `2^−E`, `l` folded into the reduced argument,
Fast2Sum`(1, x)` up to `2^53`, `E·L1 + TH` exact, and the `lb == ub` test. This
derivation's own: the reciprocals that make `z` exact without FMA, `R = 1`
around 1, the error bounds' form, the `E·ln 2` table and Estrin's form, stage B,
and every constant.

### 7.1 Notation

`RN` rounds to nearest, ties to even, and every operation below is one binary64
operation, in the order written. No operation is fused or reordered: the proofs
transcribe this order (`formal/ln/Ln1pStageH.v`, `Ln1pStageB.v`), and the
internal cross-check compares the transcription with the code bit for bit.

### 7.2 The reduction, exact without FMA

**Decision 6: `J = 9`, 512 reciprocals of 10 significant bits.**

1. **The split.** For `x < 2^53`, `s0 = RN(1 + x)` and `l = x − (s0 − 1)`
   (Fast2Sum, exact for `−1 < x < 2^53`): `1 + x = s0 + l` and
   `|l| ≤ 2^−53·s0`. Stage B takes `(h, l) = (x, 1)` for `x ≥ 2^53`, where
   `|l| ≤ 2^−53·h` too. Write `h` for `s0` or `x`.
2. **The index.** `u = bits(h) − OFF`, `OFF = bits(0x1.6ap−1)`; `E = u >> 52`
   (arithmetic) and `i = (u >> 43) & 511`. Then `h = 2^E·y` exactly, with
   `y ∈ [0x1.6ap−1, 0x1.6ap0)` and `y` in interval `i`, which holds `2^43`
   encodings. Intervals 0–299 lie below 1, 300–511 above; none straddles 1.
   `h ≥ 2^−53`, so `h` is normal and `−53 ≤ E ≤ 1020`.
3. **The reciprocal.** `R[i]` has 10 significant bits and
   `|y·R[i] − 1| ≤ 2^−9` over the interval (*generated* and checked). The three
   intervals with `y` within `2^−9` of 1 (`i = 298, 299, 300`) take `R[i] = 1`,
   so arguments near 0 reduce with no table term and stage H needs no
   small-argument branch.
4. **`rs = R[i]·2^−E`,** built by subtracting `E·2^52` from `R[i]`'s encoding:
   exact, and normal for `−53 ≤ E ≤ 1020`.
5. **`z = y·R[i] − 1`, exactly:** `hh` is `h` with its low 10 bits cleared,
   `hl = h − hh`, and `z = (hh·rs − 1) + hl·rs`.
   - `hh` has at most 43 significant bits and `rs` 10, so `hh·rs` is exact;
     it lies in `[1/2, 2]`, so `hh·rs − 1` is exact (Sterbenz).
   - `hl` has at most 10 significant bits, so `hl·rs` is exact.
   - Below 1, `y` is a multiple of `2^−53` and `R[i] ≥ 1` of `2^−9`; above,
     `2^−52` and `2^−10`. So `z` and both terms are multiples of `2^−62`, and
     with `|z| ≤ 2^−9` the sum is exact.

   So `z` is 0 or `|z| ≥ 2^−62`, and no FMA is needed.
6. **Then** `1 + x = 2^E·R[i]^−1·(1 + z + L)`, `L = l·rs`, and
   `ln(1 + x) = E·ln 2 − ln R[i] + ln(1 + z) + ln(1 + L/(1 + z))`, with
   `|L| ≤ 2^−53·(1 + 2^−9)`.

**The tables** (`ln/stage_tables.rs`, 14 KiB, *generated*):
- `T[i] = (TH, TL)`: `TH` is `−ln R[i]` rounded to `2^−43`'s grid, `TL` binary64,
  and `|TH + TL + ln R[i]| ≤ 2^−97`; `|TH| ≤ 711·2^−11`, `|TL| ≤ 2^−44`.
- `L1` is `ln 2` rounded to `2^−43`'s grid and `|L1 + L0 − ln 2| ≤ 2^−101`. So
  `E·L1 + TH` is exact for `|E| ≤ 1020`: both lie on `2^−43`'s grid, below
  `2^10`.
- `EL[k] = (E·L1, RN(E·L0))` for `E = k − 64`: stage H's `E·ln 2`, one load.
- Away from the three intervals around 1, `|TH|` exceeds the interval's
  largest `|z|` by at least `181·2^−18`, so `|ln1 + z|` stays clear of zero
  (the Fast2Sum conditions below).

**Machine-checked:**
- `formal/ln/Ln1pReduction.v`, **`split_ok`** and **`reduce_ok`**: for every
  finite `h` in `[2^−53, 2^1020]`, the fields read from `h`'s encoding give
  `h = 2^E·y` with `y` in interval `i`, `rs = R[i]·2^−E`, and
  `z = y·R[i] − 1` exactly, 0 or at least `2^−62`, at most `2^−9`.
- `formal/ln/Ln1pTables.v`, which `generators/ln1p_constants.py` writes with
  the tables, proves every bound above by **one reflective check per table**
  (`st_rt_check` over the 512 intervals, `st_l_check` over `L1`, `L0` and `EL`),
  through `formal/ln/Ln1pCheck.v`; `ln` at the rationals involved is enclosed
  by `formal/ln/LnCheck.v` (§3).

### 7.3 Stage H

```
s0 = 1 + x;  l = x − (s0 − 1);  (E, i, rs, z) = reduce(s0)
(th, tl) = T[i];  (eh, el) = EL[E + 64]
ln1 = eh + th;  ln0 = el + tl;  lr = l·rs
z2 = z·z;  t0 = z·H0 − 0.5;  t1 = z·H2 + H1;  a1 = z2·H3 + t1
p = z2·a1 + t0;  q = z2·p                         (q ≈ z²·P(z), Estrin)
s = ln1 + z;  e1 = z − (s − ln1)                  (Fast2Sum)
lo = (e1 + (lr·(1 − z) + ln0)) + q
eps = z2·K_H + (|s|·K2_H + A_H)
```

`P(z) = −1/2 + H0·z + H1·z² + H2·z³ + H3·z⁴` approximates
`(ln(1 + z) − z)/z²` on `|z| ≤ 2^−9` (Sollya `fpminimax`, relative error
`2^−40.22` for `ln(1 + z) − z`, *generated*). The term `L/(1 + z)` enters as
`lr·(1 − z)`: no division. The Fast2Sum is exact: `ln1 = 0` (`E = 0` and
`R[i] = 1`) or `|z| ≤ |ln1|`.

**The bound.** `s + lo − ln(1 + x) = z²·Gz + s·Gs + GA`, each term certified:

| Term | Collects | Bound | Certificate |
|---|---|---|---|
| `Gz` | `P`'s approximation (`592·2^−60`, proved in `Ln1pApprox.v`) and evaluation (`577·2^−61`, `stage_h_q.g`), `L·z/(1 + z)`, `lo`'s last rounding | `543·2^−59 = 2^−49.92` | `stage_h_gz.g` |
| `Gs` | the tables' and `E·ln 2`'s errors, `ln0`'s rounding, the Fast2Sum, `lo`'s roundings of `s`-sized terms | `925·2^−94 = 2^−84.15` | `stage_h_gs.g` |
| `GA` | `lr·(1 − z)`'s roundings (`stage_h_lr.g`), `ln(1 + u) − u`, their propagation | `263·2^−111 = 2^−102.96` | `stage_h_ga.g` |

`K_H = 2^−49`, `K2_H = 2^−83` and `A_H = 2^−102` are those bounds rounded up to
powers of two. The room between them pays for `eps`'s own roundings, the test's
`2^−53·(|lo| + eps)` (§7.5) and `2^−123·|ln(1 + x)|`.

**Machine-checked:** `formal/ln/Ln1pStageH.v`, **`stage_h_ok`**: for every
finite `x` that passes the screen, if stage H returns `v`, then
`v = RN(ln(1 + x))`, and every real within `2^−123` relatively of
`ln(1 + x)` rounds to `v`.

### 7.4 Stage B

**`|x| < 2^−9`: `z = x`.**
```
(p, pl) = two_prod(x, x);  m = −0.5·p                   (exact)
s = x + m;  e1 = m − (s − x)                            (Fast2Sum)
tail = (x·p)·W(x)                                       (W by Horner, B0..B5)
lo = e1 + (−0.5·pl + tail)
eps = |x|·(p·K_B + EPS_B_REL)
```
`W` approximates `(ln(1 + z) − z + z²/2)/z³` (Sollya, relative error
`2^−54.0`; the bound proved in `Ln1pApprox.v` is `691·2^−65`). The error is at
most `|x|³·137·2^−59 + |x|·263·2^−114` (*certified*: `stage_b_small_tail.g`,
`stage_b_small.g`), under `K_B = 2^−51` and `EPS_B_REL = 2^−102`.

**`|x| ≥ 2^−9`: the reduction of §7.2,** with `(h, l) = (x, 1)` from `2^53`:
```
ln1 = E·L1 + TH;  ln0 = E·L0 + TL                       (ln1 exact)
(p, pl) = two_prod(z, z)
s1 = ln1 + z;  e1 = z − (s1 − ln1);  m = −0.5·p          (Fast2Sum)
s = s1 + m;  e2 = m − (s − s1)                          (Fast2Sum)
tail = (z·p)·W(z);  lrt = lr·(((1 − z) + p) − z·p)
lo = (e1 + e2) + ((ln0 + lrt) + (−0.5·pl + tail));  eps = EPS_B = 2^−78
```
Both Fast2Sums are exact (`|z| ≤ |ln1|` or `ln1 = 0`, then `|m| ≤ |s1|`), and
both errors are kept. The error is at most `117·2^−86 = 2^−79.13`
(*certified*: `stage_b_total.g`), from `lo`'s roundings (`415·2^−88`,
`stage_b_lo.g`), the tables and `E·ln 2` with `ln0`'s roundings
(`533·2^−95`), `W`'s approximation (`349·2^−91`) and the `l` term
(`263·2^−97`).

**Machine-checked:** `formal/ln/Ln1pStageB.v`, **`stage_b_ok`**: as
`stage_h_ok`, on both branches, for every finite `x` that passes stage B's
screen.

### 7.5 The rounding test

```
lb = s + (lo − eps);  ub = s + (lo + eps);  return lb if lb == ub
```
**Validity** (`formal/ln/Ln1pTest.v`, **`decide_ok`**). If `eps ≥ 0`,
`|s| ≤ 2^999`, `|lo| + eps ≤ 1` and `lb == ub`, then every real `w` with
`|w − (s + lo)| + 2^−53·(|lo| + eps) ≤ eps` rounds to `lb`:
`s + RN(lo − eps) ≤ w ≤ s + RN(lo + eps)`, and rounding is monotone. Nothing
about `w` is assumed beyond the distance. In particular `w` may be a rounding
breakpoint, so no worst-case search is needed. Each stage proves the distance
for `ln(1 + x)` and for every real within `2^−123` relatively of it.

### 7.6 The fallback: `ln_1p_reference`

**Decision 7: three branches, none rounding `1 + x`.** These are the paths of
`ln_1p_reference`, unchanged from earlier releases.

**`|x| < 2^−54`: return `x`.** This is correctly rounded.
- For `0 < |x| < 2^−54`, `|ln(1 + x) − x| ≤ x²/(2(1 − |x|))`, which is below
  `2^−55·(1 + 2^−53)·|x|`.
- `ln(1 + x)` lies on the side of `x` toward `−∞`. For `x > 0`, that is toward
  zero, where `x`'s half-gap is at least `2^−54·|x|`, even at a power of two. For
  `x < 0`, it is away from zero, where the half-gap is `ulp(x)/2 > 2^−54·|x|`.
- For subnormal `x`, the distance is below `2^−2000`, far inside half an `ulp`.

So `RN(ln(1 + x)) = x`, and `±0` keeps its sign.

**`2^−54 ≤ |x| < 2^−7`: `z = x`, exactly.** This is case A with
`(z_hi, z_lo) = (x, 0)`, so `|z_hi| ≥ 2^−54`. Both paths and both certificates
apply unchanged: §4's steps 1–4 and §6 at `z = x`, with no `E` or table term.
The fast path is within `2^−64`, and the accurate path within `2^−123`.

**`|x| ≥ 2^−7`: `1 + x = h + l`, exactly.**
- **The split:**
  - for `x < 2^53`, `(h, l) = two_sum(1, x)` (`|x| ≤ 2^1020`, so it's exact [DW]);
  - for `x ≥ 2^53`, `(h, l) = (x, 1)`.

  Either way, `|l| ≤ 2^−53·(1 + 2u)·|h|`. For `x ∈ (−1, −1/2]`, `l = 0` (Sterbenz).
- **No case A here.** `h ≥ 1 + 2^−7` or `h ≤ 1 − 2^−7`, so `h` reduces with
  `i ∉ {0, 127}` or `E ≠ 0`. And `|ln(1 + x)| ≥ ln(1 + 2^−7) > 0.00778`.
- **Fast path:** `ln(1 + x) = ln h + ln(1 + l/h)`.
  - `Y_h` is `ln`'s fast path at `h` (§4), within `2^−64` of `ln h`.
  - Then `Y = Y_h.add_f64(RN(l/h))`.
  - Using `l/h` for `ln(1 + l/h)` costs at most `(l/h)²/(2(1 − |l/h|))`.
  - The bound is `2^−63` relative to `ln(1 + x)` (*certified*:
    `formal/ln/fast_ln_1p.g`, proves `2^−64.0`).
- **Accurate path:** `z' = (y·R[i] − 1) + R[i]·l·2^−E`. With `y`, `E` and `i`
  from `h`, `ln(1 + x) = E·ln 2 − ln R[i] + ln(1 + z')`.
  - The first term is exact, as in §6, and the second is an exact `Q128`
    product. Their `Q128` sum is within `2^−126·2^−7`.
  - That moves `ln(1 + z')` by less than `2^−133/(1 − 2^−7)`. Relative to
    `|ln(1 + x)|`, that is below `524·2^−135`, carried by `accurate_sum_b.g` and
    `_c.g` (zero for `ln`).
  - `|z'| ≤ 2^−7 + 2^−52 < 0.0078126`, inside every certificate's range.
  - `y' = (1 + x)·2^−E` lies within `2^−52` of `h`'s interval, so the case
    ratios of §3, enclosed over the widened intervals, cover `ln_1p` directly.
  - Then §6 steps 2–4 run on `z'`, with total relative error below `2^−123`.

**The bound.**
- When the rounding test passes, the result is `RN(ln(1 + x))` (§5).
- Otherwise the accurate result `Y` is within `2^−123` relative error, so
  `|ln_1p(x) − ln(1 + x)| ≤ ½·ulp + 2^−123·|ln(1 + x)| < (½ + 2^−70)·ulp`.
- It is correctly rounded unless `ln(1 + x)` lies within mantissa distance
  `2^−122` of a breakpoint. No published search excludes that, so it isn't
  claimed. Only arguments neither stage decides reach this path (§7.7).

**Machine-checked:** `formal/ln/LnAccurate.v` transcribes `ln_1p`'s accurate
branches (`small_accurate`, and `split`, `Reduced::z_prime` and
`accurate_value`), and `ln_1p_acc_ok` proves, for every finite `x > −1` with
`|x| ≥ 2^−54`, that the value is within `2^−123` relatively of `ln(1 + x)`
and that `Q128::to_f64` rounds it once. On the general branch it proves
`1 + x = 2^E·y'` with `y'` within `2^−52` of `h`'s interval, the `dz` bound
(`|ln(1 + z'_computed) − ln(1 + z')|` against `ln(1 + 2^−7)`), and that no
argument takes case A. The internal cross-check compares the transcription
with the Rust code bit for bit on 4,000 arguments over both branches.

### 7.7 Today's bits

Let a stage return `v` at `x`. Then `v = RN(ln(1 + x))`, and every real within
`2^−123` relatively of `ln(1 + x)` rounds to `v` (§7.3, §7.4). Before the
stages, `ln_1p` returned at `x`:
- its double-word fast path's result, when that path's rounding test passed:
  `RN(ln(1 + x))` (§5, `fast_ln_1p.g`), which is `v`; or
- its accurate value rounded once, which is within `2^−123` (§7.6): `v` again.

So `ln_1p` returns the same bits as before at every argument a stage decides,
and every other argument takes `ln_1p_reference` itself. The determinism
digest's `ln_1p` and `ln_1p_slice` sections are unchanged.

**Machine-checked:** `formal/ln/Ln1p.v`, **`ln_1p_stage_h_bits`** and
**`ln_1p_stage_b_bits`**: when a stage returns `v`, `v` is the binary64
`Q128::to_f64` makes of `ln_1p`'s accurate value (`ln_1p_acc_ok`), encoding for
encoding (`v` is nonzero: `|ln(1 + x)| ≥ 2^−55`). **`ln_1p_stages_ok`** states
it for `ln_1p_stages`, the screens and stages as `ln_1p` runs them, for every
`x`: `formal/ln/Ln1pScreen.v` transcribes both screens on the encoding and
proves what they admit (**`h_screen_ok`**, **`b_screen_ok`**): a finite `x` in
the ranges of the table in §7. The double-word fast path's
step rests on its certificates and the rounding test's proof (§4, §5), as it
did before; that path's transcription isn't machine-checked end to end.

So wherever a stage decides, `ln_1p` is correctly rounded, which §7.6's bound
alone doesn't claim.

### 7.8 Review points

- **No FMA.** The 10-bit reciprocals and `h`'s 10-bit split make `z` exact
  with plain multiplications on every target. An FMA kernel (`z = fma(h, rs,
  −1)`, about 40% more proof) is a follow-up.
- **`J = 9` against `J = 10`.** `J = 10` (26 KiB) sends fewer arguments past H
  (`2^−9.7` against `2^−8.6` on `e^d`) and measured no faster. 14 KiB and
  `exp`'s 16 KiB table fit a 32 KiB L1 data cache together.
- **H's floor `2^−46`.** Below it, `A_H` is a large share of an `ulp` of
  `ln(1 + x)` and H would rarely decide. Stage B's small branch has a relative
  bound and takes those arguments.
- **Stage B's constant `eps`.** `|ln(1 + x)| ≥ 2^−9.01` on the table branch,
  so `2^−78` is far below an `ulp`.
- **`ln` is unchanged.** Its fast path keeps §4; giving it this reduction is a
  follow-up.
- **Lanes.** Stage H has no branch or select, so `ln_1p_slice` runs it in
  lanes ([lanes.md](lanes.md)).

## 8. Certificates and generators

| Artifact | Tool | Establishes |
|---|---|---|
| `generators/ln_constants.py` | mpmath 1.4.1 | writes `crates/morphiq-numerics/src/ln/tables.rs` and `formal/ln/LnTables.v`: `R[i]`, `−ln R[i]` (double-word and `Q128`), `LN2_HI`/`LN2_LO`, `ln 2` and `1/k` in `Q128`, `c3`–`c9`, each checked against its bound; derives `E·ln 2`'s error, the case ratios (§3) and the series degree (§6) |
| `generators/ln_poly.sollya` | Sollya 8.0 | `c3`–`c9` (`fpminimax`, relative) and the approximation bound (`supnorm`), in `generators/ln_poly.out` |
| `generators/ln_certificates.py` | Python, mpmath | writes every certificate below from those values, with each hypothesis widened by at least 1%, and `formal/ln/LnAccurateLevels.v`; no number in a certificate is typed by hand |
| `formal/ln/tail.g` | Gappa 1.4.1 | the cubic tail, within `2^−50` relative |
| `formal/ln/p.g` | Gappa | `P` against `ln(1 + z)`, within `3·2^−66` relative |
| `formal/ln/fast_a.g`, `_b.g`, `_c.g` | Gappa | `ln`'s fast path, within `2^−64` relative, by case |
| `formal/ln/fast_ln_1p.g` | Gappa | `ln_1p`'s fast path, within `2^−63` |
| `formal/ln/accurate_level_*.g` | Gappa | the series' Horner levels |
| `formal/ln/accurate_sum_a.g`, `_b.g`, `_c.g` | Gappa | the accurate result, within `2^−123` relative, by case |
| `formal/ln/LnAccurateLevels.v` | Coq, written by `generators/ln_certificates.py` | the accurate certificates restated over reals |
| `formal/ln/LnCheck.v` | Coq | a reflective enclosure of `ln` at a rational |
| `formal/ln/LnTableCheck.v` | Coq | the accurate path's `Q128` tables and the case ratios, one reflective check each |
| `formal/ln/LnAccurate.v` | Coq | the accurate paths of `ln` and `ln_1p`, end to end (§6, §7.6) |
| `generators/ln_poly.sollya` (stages) | Sollya 8.0 | `H0`–`H3` (`h3`–`h6`) and `B0`–`B5` (`b3`–`b8`), `fpminimax`, relative on `\|z\| ≤ 2^−9`, with their approximation bounds, in `generators/ln_poly.out` |
| `generators/ln1p_constants.py` | Python, mpmath | writes `crates/morphiq-numerics/src/ln/stage_tables.rs` and `formal/ln/Ln1pTables.v`: `OFF`, `R`, `T`, `L1`/`L0`, `EL` and the stages' polynomials, each bound of §7.2 checked |
| `generators/ln1p_certificates.py` | Python, mpmath | writes the stage certificates below and `formal/ln/Ln1pCertificates.v`, their theorems over reals; hypotheses derived, goals widened by at least 1% |
| `formal/ln/stage_h_q.g`, `_lr.g`, `_gz.g`, `_gs.g`, `_ga.g` | Gappa 1.4.1 | stage H's `q`, `l` term and the three error terms (§7.3) |
| `formal/ln/stage_b_small_tail.g`, `_small.g` | Gappa | stage B's small branch (§7.4) |
| `formal/ln/stage_b_lo.g`, `_total.g` | Gappa | stage B's table branch (§7.4) |
| `formal/ln/Ln1pCheck.v`, `Ln1pTables.v` | Coq | the stage tables, one reflective check each (§7.2) |
| `formal/ln/Ln1pApprox.v` | Coq | `P`'s and `W`'s approximation bounds, from the series of `ln(1 + z)` |
| `formal/ln/Ln1pReduction.v` | Coq | the split and the reduction, exact (§7.2) |
| `formal/ln/Ln1pTest.v` | Coq | the stage test's validity (§7.5) |
| `formal/ln/Ln1pLemmas.v`, `Ln1pStageH.v`, `Ln1pStageB.v` | Coq | stages H and B, end to end (§7.3, §7.4) |
| `formal/ln/Ln1pScreen.v` | Coq | the screens, on the encoding (§7) |
| `formal/ln/Ln1p.v` | Coq | the stages return the accurate path's bits (§7.7) |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

**Gates:**
- **Certificates:** `scripts/check_certificates.sh` checks `formal/ln` as it
  does `formal/exp`, in the `certificates (sollya, gappa)` job:
  - the binding manifest matches;
  - the Sollya script reproduces its output exactly;
  - every certificate proves its goal.
- **Replay:** `scripts/check_generators.sh` replays all four generators.

**The binding** (`formal/ln/binding.sha256`) covers this document, the
constants, the Sollya script and output, every certificate, and the kernels'
source (`ln/mod.rs`, `ln/stages.rs`, `ln/stage_tables.rs`, `q128.rs`). The
formal job's manifest (`formal/binding.sha256`) binds the Coq proofs to
`ln/stages.rs` and `ln/stage_tables.rs` too.

## 9. Checked by

- **Bit-exact agreement** with `crates/reference/fixtures/ln.json`
  (`crates/reference/tests/ln.rs`): 4,019 `ln` cases, including [LM] Table 5's
  worst cases, and 3,960 `ln_1p` cases. An `ln_1p` mismatch would be an input
  inside §7's window. It's reported, not waived.
- **Every unrounded result within its certified bound,** against values to 192
  bits (the fixture's `precise` section), in exact arithmetic
  (`src/ln/tests.rs`):
  - `ln`'s fast path within `2^−64` and accurate path within `2^−123`, on 1,200
    arguments;
  - `ln_1p`'s within `2^−63` and `2^−123` on 1,400 arguments across its
    branches, 200 of them around `2^53`, where `1 + x` splits as `(x, 1)`;
  - `P` against `ln(1 + z)` within `3·2^−66` for 600 double-word `z` with a
    nonzero low word, which random arguments rarely produce.
- **The fast paths against the accurate paths:** equal whenever the fast path
  returns, on 2^20 `ln` and about 550,000 `ln_1p` arguments. Measured, they send
  `2^−9.4` of arguments to the accurate path (1,502 of 1,048,576 for `ln`, 761 of
  550,857 for `ln_1p`), against the analytic bound `2^−9`; the tests fail above
  four times that.
- **The rounding test at its boundary,** for both signs and at powers of two.
- **Each stage against `ln_1p_reference`** (`src/ln/tests.rs`): bit for bit
  wherever it decides, on about 630,000 arguments across both stages' branches
  (`e^d`, `z²/4`, log-uniform, random encodings, small `|x|`, near −1,
  `l ≠ 0`, the table intervals' edges, every threshold ±2,000 encodings and
  powers of two with their neighbours); each stage must decide at least 63/64
  of the arguments its screen admits.
- **The stages against their transcriptions:** the internal cross-check
  compares `(s, lo, eps)` and the test's result with the extracted
  `Ln1pStageH.v` and `Ln1pStageB.v`, bit for bit, on 4,000 arguments each, and
  both screens with `Ln1pScreen.v` on all 7,507 arguments drawn for them.
- **Offline, before the change:** 107,373,586 arguments, 0 mismatches between
  `ln_1p` and `ln_1p_reference`, stage by stage and through `ln_1p_slice`: the
  `e^d` and `z²/4` families (25M each), log-uniform over `(−1, 2^1024)` (20M),
  `1 + x = 2^U` (5M), random encodings (15M), small `|x|` (6M), near −1 (3M),
  `l ≠ 0` (3M), the interval edges for `J` = 7 to 10 (4M), the thresholds, the
  powers of two, the `ln.json` fixture, and CORE-MATH's `log1p.wc` hard cases
  with their neighbours (1.04M, inputs only, not committed).
- **The determinism digest's `ln` and `ln_1p` sections** on every target
  ([determinism.md](determinism.md)).
- Exhaustive checks of chosen sub-intervals against the oracle (scheduled).
