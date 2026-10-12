# `exp`: correctly rounded exponential

`morphiq_numerics::elementary::exp` (`crates/morphiq-numerics/src/exp/`) follows
this derivation step for step. Every bound below is certified, and every
constant generated, by the artifacts in §9; §10 lists what checks the code
against them. Each numbered **decision** is a design choice open to review, and
each **review point** is an argument a second reader should check.

`exp(x)` returns `e^x` rounded to nearest, ties to even, for every binary64 `x`.
Subnormal results are rounded once. Here `u = 2^−53`, `RN` is
round-to-nearest-even, and `L = ln 2 / 512`.

**Paths.** A screen (§3) sends every `|x| < 704` to two fast stages: stage A
(§5), a lean evaluation that decides all but about one argument in 2^7.4, then
stage B (§6), a tighter one that decides all but about one in 2^17. Each
returns its result only when a rounding test with a constant error bound (§7)
proves it is `RN(e^x)`. Everything else goes to the fallback (§8): the special
values of §1, `|x| ≥ 704`, and the arguments neither stage decides, which take
a third fast path and, past it, an accurate path in 128-bit arithmetic whose
error bound is proved against [LM]'s worst cases.

## Sources

- **[Tang]** P. T. P. Tang, "Table-driven implementation of the exponential function
  in IEEE floating-point arithmetic", *ACM TOMS* 15(2), 1989: the table-driven
  reduction and reconstruction (§3, §8).
- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: the accuracy that
  decides every case (Property 1, Tables 2 and 4).
- **[Ziv]** A. Ziv, "Fast evaluation of elementary mathematical functions with
  correctly rounded last bit", *ACM TOMS* 17(3), 1991: a fast path that returns
  only when its result provably rounds correctly, with a slower accurate path
  otherwise.
- **[DW]** This crate's double-word arithmetic ([double-word.md](double-word.md)):
  its operations have machine-checked error bounds in IEEE 754 arithmetic.
- **[CM]** CORE-MATH's binary64 `exp`, `src/binary64/exp/exp.c` at commit
  `81a899d6` (SHA-256 `39b15256ce4632b163a9f93325c9ada678aacedcdf46cb32ee56f44860a87e64`),
  MIT. It was consulted during the research for this design (issue #114), for
  ideas only: the rounding test with a constant bound (§7), a lean first stage
  (§5), assembling the result as `th + (tl + th·u)`, scaling on the exponent
  field (§7) and reading the index from the shifter's encoding (§3). No code was
  taken, so no notice is carried. Every constant here comes from this
  repository's generators, and stage B's exact product (§6) is this
  derivation's own.

## 1. Specification

| Input | Result | Why |
|---|---|---|
| NaN | NaN | |
| `x ≥ X_OVERFLOW` | `+∞` | `X_OVERFLOW` is the least `x` whose exponential rounds to `+∞` (*generated*) |
| `x ≤ X_ZERO` | `+0` | `X_ZERO` is the greatest `x` whose exponential rounds to `+0` (*generated*) |
| `−2^−54 ≤ x < 2^−53` | `1` | the exponential rounds to 1 exactly there ([LM] Table 2; *generated* and checked) |
| otherwise | `RN(e^x)` | the rest of this document |

Covered by those rows: `+∞` (first row), `−∞` (second) and `±0` (third).

The thresholds come from `generators/exp_reference.py`, which derives them by
bisection with a rigorous interval oracle. Its fixture
`crates/reference/fixtures/exp.json` is the test reference:
- `X_OVERFLOW = 709.7827128933841` (`0x40862E42FEFA39F0`);
- `X_ZERO = −745.1332191019412` (`0xC0874910D52D3052`).

## 2. Accuracy needed

[LM] Property 1 bounds how close `e^x` can come to a rounding breakpoint, over the
whole binary64 range. The bound is a *mantissa distance*: the distance between
significands in `[1, 2)`.
- **`|x| ≥ 2^−30`:** an approximation within `2^−113` of `e^x` rounds correctly.
- **`2^−54 ≤ |x| < 2^−30`:** within `2^−158`.
- **`|x| < 2^−54`:** the table in §1 applies.

**Subnormal results** (`X_ZERO < x < X_SUBNORMAL ≈ −708.396`). Their breakpoints,
the midpoints `(2m + 1)·2^−1075`, are among the 54-bit test numbers of their
binade, which [LM]'s search covers. Its first interval in Table 4 starts at
`ln(2^−1074)`. So the `2^−113` bound applies to them as well.
- **Review point:** this argument should be checked by a second reader.

The stages need none of this: their test (§7) proves its result is `RN(e^x)`
from the error bound alone, without any distance from a breakpoint. [LM]
matters only to the fallback's accurate path (§8.4), which must decide every
argument.

## 3. The screen and the stages' reduction (after [Tang] §4, Step 2)

**The screen.** `x.to_bits() & !SIGN < 704.to_bits()`: one unsigned comparison
on `|x|`'s encoding. It holds exactly for finite `|x| < 704`; NaN and the
infinities have larger encodings, so they fail it and go to the fallback, with
`|x| ≥ 704`.

**Decision 1: `|x| < 704`.** There `k` (below) lies in `[−1016, 1016]`, so
every result the stages form, `2^k` times a number in `[0.9, 2.1]`, is normal
and finite, and the scaling is exact (§7). The arguments between 704 and the
thresholds of §1 (about 3% of the interval between them, all with results
above `2^1015` or below `2^−1015`) take the fallback.

**Decision 2: a table of `N = 512` entries `T_j = 2^(j/512)`** (8 KiB, §4). It
keeps `|r| ≤ 2^−10.5`, where a degree-5 polynomial is accurate to `2^−75.9`.
`N = 1024` (16 KiB) would cut stage A's undecided rate from `2^−7.4` to
`2^−8.4` and stage B's from `2^−16.9` to `2^−18` (the research's measurements,
issue #114); measured inside a consumer's EM loop on an Apple M1 Pro, `N = 512`
cost 2.6% more. The smaller table was chosen to leave
room in a 32 KiB L1 data cache, as on many x86-64 cores, for a consumer's own
working set and `ln_1p`'s table. That trade-off is inferred for x86-64, not
measured there (§11).

1. `t = RN(RN(x·INV_N) + S)`, with `INV_N = RN(512 / ln 2)` (*generated*) and
   the shifter `S = 1.5·2^52`. `|x·INV_N| < 520,017`, so `t` lies in
   `[2^52, 2^53)`, where binary64 numbers are the integers: `t = S + ni` with
   `ni` the integer nearest `RN(x·INV_N)`, ties to even.
2. `n = t − S`, exact, and `ni` itself as `t`'s encoding minus `S`'s: in that
   binade the encoding is `0x4330… + t − 2^52`.
3. `j = ni & 511` and `k = ni >> 9` (two's complement), so `ni = 512k + j`,
   `0 ≤ j < 512`, and `|ni| ≤ 520,018` gives `|k| ≤ 1016`.
4. `|x/L − ni| ≤ 1/2 + 2^−31`: the half from rounding to an integer, the rest
   from `INV_N`'s error (`2^−42`) and `x·INV_N`'s rounding. So the exact reduced
   argument `R = x − ni·L` has `|R| ≤ (1/2 + 2^−31)·L < 0.000677`.
5. `L` is split as `L1 + L2 + L3`, with `L1` and `L2` rounded to 31 significant
   bits and `L3 = RN(L − L1 − L2)`, so `|L − (L1 + L2 + L3)| < 2^−129`; and as
   `L1 + L2D`, `L2D = RN(L − L1)`, with `|L − (L1 + L2D)| < 2^−98` (*generated*).
   `ni·L1` and `ni·L2` are exact: `|ni| < 2^20` and 31 bits leave 51.
6. `r1 = x − n·L1`, exact. For `ni = 0`, `r1 = x`. Otherwise
   `|x| ≥ (1/2 − 2^−31)·L > 2^−11`, so `x` is a multiple of `2^−63`, as is
   `ni·L1` (a multiple of `2^−40`), and `|r1| ≤ |R| + |ni|·|L − L1| < 2^−10`
   needs at most 53 bits at that quantum.

Then `e^x = 2^k·T_j·e^R`. Stage A (§5) and stage B (§6) finish the reduction
in their own ways.

**Machine-checked:** `formal/exp/ExpStageReduction.v` transcribes `Stages::of`
on binary64 and proves steps 1–6 for every finite `|x| < 704` (`stage_of_ok`),
`ni` read from the encoding as the Rust code reads it. The bounds on `L`'s
splits and `INV_N` are proved with CoqInterval in `formal/exp/ExpStageTables.v`
(`st_l_split`, `st_l_split_d`, `st_inv_close`). The screen is
`formal/exp/ExpStageB.v`'s `screen_ok`: an encoding that passes it is finite
and below 704 in magnitude.

## 4. The table

`T_j = 2^(j/512)` for `0 ≤ j < 512` as a double-word `(th, tl)`:
`th = RN(T_j)` in `[1, 2)` and `tl = RN(T_j − th)`, `|tl| ≤ 2^−53`, both
binary64 encodings (`S_T`, *generated* by `generators/exp_constants.py`, which
checks `|th + tl − T_j| < 2^−107` in 600-bit arithmetic).

**Decision 3: one reflective check proves the whole table.**
`formal/exp/TableCheck.v` defines a boolean function over the list of encodings
and proves it sound (`table_check_ok`); `ExpStageTables.v` evaluates it once by
`vm_compute` (`st_t_check`). For each entry it decodes both words, requires
`th` in `[1, 2)` and `|tl| ≤ 2^−53`, and bounds `|th + tl − T_j| ≤ 2^−104`
without evaluating `T_j`: `v ↦ v^512` is increasing on the nonnegative reals
and `T_j^512 = 2^j`, so it suffices that

    (th + tl − 2^−104)^512 ≤ 2^j ≤ (th + tl + 2^−104)^512.

Each power is nine squarings in integer arithmetic, rounded outward to 128 bits
after each, so the computed bounds enclose the exact powers. The actual error,
below `2^−106`, leaves a margin near `2^−96` relatively after the 512th power,
far above the squarings' `2^−118`. The bound `2^−104` is what the certificates
take (`Dt` in `formal/exp/stage_a.g` and `stage_b.g`). Building
`ExpStageTables.v`, the check included, takes about 20 seconds on an Apple M1
Pro.

## 5. Stage A

A lean evaluation in binary64, which decides most arguments.

1. `r = RN(r1 − RN(ni·L2D))`. `r1 − RN(ni·L2D) = R + dr` with `|dr| ≤ 2^−77`:
   the tail `ni·(L − L1 − L2D)` and the rounding of `ni·L2D`
   (*certified*: `formal/exp/stage_a_reduction.g`).
2. `u = RN(r + RN(RN(r·r)·h))`, `h = RN(1/2 + RN(r·RN(d3 + RN(r·RN(d4 + RN(r·d5))))))`:
   `e^r − 1` to degree 5. `d3`–`d5` are binary64 coefficients from Sollya's
   `fpminimax` for `e^r − 1 − r − r²/2` on `|r| ≤ 0.000677`, and the
   approximation error is below `0x1.11efe3daa4fb92df2df8cp−76 ≈ 2^−75.9`
   (*generated*: `generators/exp_poly.sollya`'s `supnorm`; proved again with
   CoqInterval in `ExpStageTables.v`, `st_poly_approx`). Stage B uses the same
   polynomial.
3. `y = th` and `l = RN(tl + RN(th·u))`.

**Error: `|th + l − T_j·e^R| ≤ 0x1.2ep−61 < 2^−60.76`** (*certified*:
`formal/exp/stage_a.g`, which also bounds `|l| ≤ 0x1.6ap−10 < 2^−9.5`). Its
hypotheses, each certified or proved: the reduction (step 1); the
approximation error (step 2); the table's `2^−104` (§4); and `m`, the cost of
evaluating the polynomial at `r` instead of `R`: `|r − R| ≤ ulp(r)/2 + 2^−77
< 0x1.01p−64`, so `|m| ≤ 2^−74` (*certified*: `formal/exp/stage_mvt.g`). The
dominant terms are the roundings of `r`, `u`, `th·u` and `l`, each at most
`2^−63`.

**`E_A = 1.5·2^−61`,** the bound the test (§7) takes: the certified error plus
the test's own rounding, `0x1.2ep−61 + 2^−63 = 1.43·2^−61`, rounded up. The
research prototype took `E_A` from the same analytic estimate; the certificate
confirms it with a margin of `0.07·2^−61`.

**Machine-checked:** `formal/exp/ExpStageA.v` transcribes `Stages::a_value`
and `Stages::a` on binary64. `stage_a_value_ok` proves the error bound for the
transcription: every operation is finite and rounds as `stage_a.g` models it,
and each hypothesis holds (the reduction, `stage_mvt.g`, the approximation and
table bounds). `exp_stage_a_ok` composes it with the test (§7): for every finite
`|x| < 704`, a value stage A returns is `RN(e^x)`.

## 6. Stage B

A tighter evaluation for the arguments stage A leaves undecided, with one
exact product doing the work of a double-word multiplication.

1. **The reduced argument as `r_h + r_t`.** `r0 = RN(r1 − ni·L2)` (`ni·L2`
   exact), and `r_h = RN(RN(r0 + SPLIT) − SPLIT)` with `SPLIT = 1.5·2^12`: in
   `[2^12, 2^13)` binary64 numbers are the multiples of `2^−40`, so `r_h` is
   `r0` rounded to that grid, ties to even, exactly, with `|r_h − r0| ≤ 2^−41`
   and `|r_h| ≤ 0.000678` (at most 30 significant bits). Then
   `r_t = RN(RN(RN(r1 − r_h) − ni·L2) − RN(ni·L3))`, whose first two
   operations are exact:
   - `r1 − r_h`: for `ni ≠ 0` both are multiples of `2^−63` and the
     difference is below `2^−10`; for `ni = 0`, `r_h` is `x` rounded to `2^−40`'s
     grid, so either `r_h = 0` or `|x| ≥ 2^−41`, and `x − r_h` is a multiple of
     `2^−93` below `2^−41`;
   - minus `ni·L2`: for `ni ≠ 0` all three are multiples of `2^−72` and the
     result, `r0 − r_h` plus `r0`'s rounding error, is below `2^−40`; for
     `ni = 0`, `ni·L2 = 0`.

   So `|r_h + r_t − R| ≤ 2^−93` and `|r_t| ≤ 2^−40` (*certified*:
   `formal/exp/stage_b_reduction.g`).
2. `r_hi = RN(r_h + r_t)` and `q = RN(RN(r_hi·r_hi)·RN(1/2 + r_hi·(d3 + …)))`,
   the same polynomial at `r_hi`, within `2^−73` of its exact value, with
   `0 ≤ q ≤ 2^−22` (*certified*: `formal/exp/stage_b_poly.g`).
3. **The exact product.** `A = th` with the low 32 bits of its encoding
   cleared: its 21 leading significant bits, a multiple of `2^−20` in `[1, 2)`.
   - `d = RN(th − A) = th − A`, exactly: `0 ≤ d < 2^−20`, a multiple of `2^−52`.
   - `A·r_h` is exact: `A = a·2^−20` with `a < 2^21` and `r_h = b·2^−40` with
     `|b| < 2^30`, so `A·r_h = ab·2^−60` with `|ab| < 2^51`.
   - `(y, e) = Fast2Sum(th, A·r_h)`: `y = RN(th + A·r_h)` and `y + e = th + A·r_h`
     exactly, since `th ≥ 1 > |A·r_h|`.
4. `l = RN(e + rest)`, with
   `rest = RN(tl + RN(RN(tl·r_hi) + RN(RN(d·r_h) + RN(th·RN(r_t + q)))))`.

So `y + l` approximates `th·(1 + r_h + r_t + q) + tl·(1 + r_hi)`: the leading
term `th + th·r_h` is carried exactly by `y + e`, and only terms below `2^−20`
go through rounded binary64 operations.

**Error: `|y + l − T_j·e^R| ≤ 0x1.a2p−71 < 2^−70.29`** (*certified*:
`formal/exp/stage_b.g`, which also bounds `|l| ≤ 2^−20`). Its hypotheses: the
reduction (step 1), the polynomial's evaluation (step 2), the approximation
error (§5), `m` at `r_hi` (`|R − r_hi| ≤ 2^−64 + 2^−93`, `stage_mvt.g`), the
table (§4), and the exactness facts of step 3.

**`E_B = 2^−70`:** the certified error plus the test's rounding,
`0x1.a2p−71 + 2^−73 = 1.88·2^−71`, rounded up.

- **Review point:** the exactness of `r1 − r_h` and of the subtraction of
  `ni·L2`, in both cases of step 1, and of step 3's product.

**Machine-checked:** `formal/exp/ExpStageB.v` transcribes `Stages::b_value` and
`Stages::b`, the bit mask included (`mask_ok`, on the encoding as Rust computes
it), and proves the exactness facts and the error bound
(`stage_b_value_ok`, with `ExpStageReduction.v`'s `stage_b_r_ok` for step 1),
and `exp_stage_b_ok`: a value stage B returns is `RN(e^x)`. `exp_stages_ok`
composes the screen and both stages as `exp` runs them.

## 7. The rounding test, and the scaling

**Decision 4: a test with a constant absolute bound, before scaling** (after
[Ziv], in the form [CM] uses). With `Z = T_j·e^R = e^x / 2^k`, a stage has
`(y, l)` with `|Z − (y + l)| ≤ ε`, and a binary64 constant `E`:

    low  = RN(y + RN(l − E))
    high = RN(y + RN(l + E))
    return low·2^k   if   low == high
    otherwise the next stage, or the fallback

**Proof.** Let `|l| + E ≤ 2^em` (stage A: `em = −9`; stage B: `em = −19`).
Then `|l ± E| ≤ 2^em`, and rounding a number that small errs by at most
`2^(em−54)` (half an ulp below `2^em`; zero at `2^em` itself, which is
representable). If `E ≥ ε + 2^(em−54)`:
- `RN(l − E) ≤ l − E + 2^(em−54) ≤ l − ε ≤ Z − y`, and likewise
  `RN(l + E) ≥ Z − y`;
- so `y + RN(l − E) ≤ Z ≤ y + RN(l + E)`, and rounding is monotone:
  `low ≤ RN(Z) ≤ high`;
- when `low = high`, `RN(Z) = low`.

Unlike §8.3's relative test, this needs no fact about `Z`: not that it is
transcendental, nor its distance from a breakpoint. Stage A's `E_A` and stage
B's `E_B` meet the condition (§5, §6).

**Why the bound is constant.** `Z` lies in `[0.9, 2.1]` before scaling
(`T_j ∈ [1, 2)`, `|R| < 0.000677`), where an absolute bound plays the role a
relative one plays across binades; scaling by `2^k` then carries the decided
`RN(Z)` to `RN(e^x)`, because rounding commutes with exact scaling while both
are normal. So one comparison of two roundings replaces the ulp computation of
§8.3.

**The scaling** adds `k` to the exponent field:
`low.to_bits().wrapping_add((k << 52) as u64)`. `low = RN(Z)` lies in
`[0.5, 4)`, a normal number whose biased exponent is 1022 to 1024, and
`|k| ≤ 1016` keeps the sum's exponent field in `[6, 2040]`: the encoding of
`low·2^k`, exact and normal.

**The undecided rate** is near `2E/ulp(y) ≈ 2E·2^52`: `3·2^−9 ≈ 2^−7.4` for
stage A and `2^−17` for stage B. Measured on 2^28 arguments (§10; three in
four uniform in `|x| < 704`, the rest of magnitude `2^−64` to 1): stage A
leaves `2^−7.33`, and stage B `2^−16.9` of all arguments.

**Machine-checked:** `formal/binary64/RoundingConstant.v` transcribes the test
and the scaling (`decide_const`, from the encodings as Rust forms them) and
proves `const_test_real` (the argument above) and `decide_const_ok`: when the
test passes, the returned value is `RN(Z·2^k)`.

## 8. The fallback

`fallback(x)` is `exp` before the stages, unchanged: the special values of §1,
then a reduction with a 128-entry table, a fast value in double-word
arithmetic with a relative rounding test, and an accurate path in 128-bit
arithmetic. Arguments reach it from the screen (`|x| ≥ 704`, NaN, infinities)
and when neither stage decides, about one in 2^17 of the rest. It also serves
as the test oracle for the stages (§10), and `exp2` and `expm1` share its
fast value and test.

Within this section, `L = ln 2 / 128`.

### 8.1 Argument reduction (after [Tang] §4, Step 2)

**Decision 5: a table of `N = 128` entries `T_j = 2^(j/128)`.** This keeps
`|r| ≤ L/2 ≈ 2^−8.53`, so a degree-6 polynomial meets the fast path's budget,
with a table of 2 KiB for the fast path and 2 KiB for the accurate path.
[Tang] uses 32 entries for a 0.54-ulp result; correct rounding needs a tighter
fast path.

1. `t = RN(x · INV_L)`, with `INV_L = RN(128 / ln 2)` (*generated*).
2. `n = RN_int(t)`, as `(t + S) − S` with `S = 1.5·2^52`. This is exact while
   `|t| < 2^51`, and here `|t| < 137,700 < 2^18`.
3. `j = n mod 128` (0 to 127) and `k = (n − j) / 128`, with `−1,076 ≤ k ≤ 1,024`.
4. `r = x − n·L`, with `L` split into four binary64 constants, named as in [Tang]
   (*generated*):
   - `L1`: `L` rounded to 35 significant bits, so `n·L1` is exact for `|n| < 2^18`;
   - `L2 = RN(L − L1)`;
   - `L3 = RN(L − L1 − L2)`;
   - `L4 = RN(L − L1 − L2 − L3)`.

   So `|L − (L1 + L2 + L3 + L4)| < 2^−206` (*generated*).
   - **Fast path:** `r1 = x − n·L1` is exact: `r1 = x` for `n = 0`; otherwise
     `|x| ≥ 2^−9`, so `x` and `n·L1` are both multiples of
     `2^min(cexp(x), −42) ≥ 2^−61`, and `|r1| < 2^−8` needs at most 53 bits at
     that quantum. (Sterbenz's lemma, as in [Tang] §5.1, would need
     `x ≥ n·L1/2`, which a tie at `n = ±1` can miss.) `(p2, e2) = two_prod(n, L2)`
     is exact.
     Then `r` is the double-word `(r_hi, r_lo)`:
     ```
     (s, t) = two_sum(r1, −p2)
     rr     = RN(RN(t − e2) − RN(n·L3))
     (r_hi, r_lo) = two_sum(s, rr)
     ```
     `two_sum`, not `fast_two_sum`, for the last step: `|s| ≥ |rr|` isn't
     guaranteed when `r` is tiny. The absolute error
     `|r_hi + r_lo − (x − n·L)|` is below `2^−113` (*certified*:
     `formal/exp/reduction.g`), and `|r_lo| ≤ 2^−62`.
   - **Accurate path:** `r1`, `p2`, `e2`, `(p3, e3) = two_prod(n, L3)` and
     `RN(n·L4)` are summed in 128-bit arithmetic (§8.4).

Then `e^x = 2^k · T_j · e^r`.

**Machine-checked:** `formal/exp/ExpReduction.v` transcribes `Reduced::of` on
binary64 and proves steps 1–4 for every `x` in `[−745.1333, 709.79]` (the
domain past the overflow and underflow thresholds) and every `L` within
`2^−206` of `L1 + L2 + L3 + L4` (`reduce_ok`): `n` is an integer with
`|n| ≤ 137,601`, `r1` and `p2 + e2` are exact, `|x − n·L| ≤ 0.0027076063`
(inside the certificates' `0.0027077`), `r_hi = RN(r_hi + r_lo)`, and
`(r_hi, r_lo)` is within `2^−113` of `x − n·L`. For `|x| ≥ 2^−99` every word of
the reduction is a multiple of `2^−151`. The `2^−113` bound is
`formal/exp/reduction.g`'s theorem, applied through Gappa's Coq proof.
`formal/exp/ExpTables.v` proves with CoqInterval that the generated split is
within `2^−206` of `ln 2 / 128`, so `L` is exactly `ln 2 / 128`. The formal job
compares the transcription with the Rust code bit for bit on the internal
cross-check corpus: arguments across the domain, at ties of `x/L`, and tiny.

### 8.2 Fast value

**Decision 6: everything after the polynomial uses the crate's proved
double-word operations,** so the only new error analysis is the polynomial's.

1. **Polynomial.** `q = r_hi² · (½ + r_hi·(c3 + r_hi·(c4 + r_hi·(c5 + r_hi·c6))))`
   in binary64, Horner order.
   - `c3`–`c6` are binary64 coefficients from Sollya's `fpminimax` for
     `e^r − 1 − r − r²/2` on `|r| ≤ 0.0027077` (*generated*).
   - The approximation error `|e^r − 1 − r − q*(r)|` is certified with Sollya's
     `supnorm`: below `2^−77.2` (*generated*; target `2^−72`).
   - The evaluation error `|q − Q(r_hi)|`, against the same polynomial evaluated
     exactly, is below `2^−70` (*certified*: `formal/exp/poly.g`).
2. `P = DoubleWord(r_hi, r_lo).add_f64(q)`: `e^r − 1`. The polynomial is evaluated
   at `r_hi`, not the exact `r`; `r − r_hi` is at most `|r_lo| + 2^−113 ≤
   2^−62 + 2^−113`, and the difference `|Q(r) − Q(r_hi)|` is below
   `0x1.9p−71 ≈ 2^−70.4` (*certified*: `formal/exp/mvt.g`).
3. `E = DoubleWord::from_f64(1.0).add(P)`: `e^r`.
4. `Y = T_j.mul(E)`, where `T_j` is a double-word table entry, `2^(j/128)` rounded
   to double-word (*generated* as encodings `T_BITS`, error below `2^−107`).

**Fast-path error bound: `ε₁ = 2^−69`** (*certified*: `formal/exp/fast.g` proves
`2^−69.17`). It is the relative error of `Y` against `T_j·e^r`, composed from:
- the reduction error, the polynomial's evaluation error and `Q(r) − Q(r_hi)`
  (the certificates above);
- the approximation error (Sollya);
- the double-word operations' bounds (`2u²`, `3u²/(1 − 4u)`, `5u²`, machine-checked
  in [double-word.md](double-word.md));
- the table's error.

At that bound the rounding test (§8.3) should send roughly one argument in 2^15 to
the accurate path; measured, it sends one in 2^15.4 (§10).

**Machine-checked:** `formal/exp/ExpFast.v` transcribes `fast_at` on binary64
and proves `ε₁` for it (`fast_ok`): for `(r_hi, r_lo)` within `2^−113` of `R`,
`|R| ≤ 0.0027076063`, both on `2^−151`'s grid, and every `j`, `Y` is a
double-word number within `2^−69` relatively of `2^(j/128)·e^R`, with `y_hi` in
`[3/4, 4]`.
- **The certificates' theorems,** applied through Gappa's Coq proofs:
  `fast.g`, and `mvt.g` for `Q(r) − Q(r_hi)`.
- **Their hypotheses about the transcription.** The polynomial is `fast.g`'s
  rounded Horner chain. The double-word steps meet their machine-checked bounds
  and return double-word numbers. Every word stays on `2^−967`'s grid, so the
  last product's low terms are normal or zero, as its bound requires.
- **The constants,** in `formal/exp/ExpTables.v`, which
  `generators/exp_constants.py` writes from the same encodings as `tables.rs`.
  CoqInterval proves Sollya's approximation bound, every table pair within
  `2^−107`, and the `L` split, from the definitions of `exp` and `ln`.

`exp_fast_ok` composes the reduction, `fast_ok` and the rounding test
(`decide_scaled_ok`): for every finite `x` with `−745.1333 ≤ x < X_OVERFLOW`,
`|x| ≥ 2^−99` and `k ≥ −1021`, a value the fast path returns is `RN(e^x)`. The
formal job also compares `fast_at` with the Rust code bit for bit, at the
corpus's reduced arguments, cycling through every table index.

CoqInterval computes with Coq's primitive 63-bit integers, so these theorems
also rest on their specification, listed in `formal/axioms.int63.expected`.

**Decision 7: the fast path doesn't handle results that may be subnormal**
(`k < −1021`). They go straight to the accurate path, which rounds once. Scaling
a rounded fast result by `2^k` there would round twice.

### 8.3 Rounding test

`Y = (y_hi, y_lo)` is a double-word number, so `y_hi = RN(y_hi + y_lo)`. `y_hi` is
the correctly rounded `e^x / 2^k` whenever the interval
`y_hi + y_lo ± ε₁·|Y|` contains no rounding breakpoint. Those are the midpoints
between `y_hi` and its neighbours.

**Decision 8: the test, with the crate's exact `ulp`:**
```
g = ulp(y_hi), halved when y_hi is a power of two     (the smaller gap)
return y_hi · 2^k   if   RN(|y_lo| + RN(EPS · |y_hi|))  <  g / 2
otherwise take the accurate path
```
with `EPS = ε₁·(1 + 2^−50) = 2^−69·(1 + 2^−50)`, a binary64 constant.

**Proof.** Let `Z = T_j·e^r`, the exact value `Y` approximates, with
`|Y − Z| ≤ ε₁·|Z|`. `Z` isn't a breakpoint: `e^x` is transcendental for `x ≠ 0`
(Lindemann), and `x = 0` never reaches this point (§1).
1. **The computed comparison implies the exact one.**
   - `g/2` is a power of two, so representable, and `RN` is monotone. So
     `RN(a) < g/2` implies `a < g/2`.
   - `RN(v) ≥ v·(1 − u)` for positive normal `v`, and `EPS·(1 − u) ≥ ε₁·(1 + 2^−52)`.
   - So the test passing implies `|y_lo| + ε₁·(1 + 2^−52)·|y_hi| < g/2`.
2. **That puts `Z` within `y_hi`'s rounding interval.**
   - `|Y| ≤ |y_hi|·(1 + 2^−53)`, so `|Z − Y| ≤ ε₁|Y|/(1 − ε₁) ≤ ε₁·(1 + 2^−52)·|y_hi|`.
   - Then `|Z − y_hi| ≤ |y_lo| + |Z − Y| < g/2`.
   - Both of `y_hi`'s half-gaps are at least `g/2`, so `Z` lies strictly inside
     the set of reals that round to `y_hi`, and `RN(Z) = y_hi`.

Scaling by `2^k` is exact (below), so the returned value is `RN(e^x)`.

**Machine-checked:** `formal/binary64/RoundingTest.v` transcribes the test
(`decide_scaled`, and `ln`'s `decide_with`, which every other kernel shares) on
binary64 and proves it: when the test passes, the returned word is `RN` of every
real within `ε₁` of `y_hi + y_lo`, for `2^−80 ≤ ε₁ ≤ 2^−60` (`decide_with_ok`),
and for `decide_scaled` the exact scaling makes it `RN(Z·2^k)`
(`decide_scaled_ok`). The formal job compares the transcriptions with the Rust
code bit for bit on the internal cross-check corpus, with cases at the test's
threshold so both outcomes occur.

**Scaling:** `y_hi · 2^k` is exact for `k ≥ −1021`. For `k = 1024`, where `Y < 1`
near overflow, it's applied as `(y_hi · 2^(k−1)) · 2`.

### 8.4 Accurate path

**Decision 9 (made): 128-bit significand arithmetic,** not triple-word.
- **Why not triple-word:** Fabiano, Muller and Picot's triple-word algorithms
  assume a fused multiply-add, which `core` doesn't offer. Their bounds don't
  hold verbatim without one.
- **The type:** a private sign-magnitude type `Q128 = (sign, m: u128, e: i32)`,
  with value `±m·2^e`, and `m` normalized (top bit set) or zero. It is
  deterministic on every target and uses only integer instructions.
- **Its contract,** which the certificates assume. It is proved in Coq (§10):
  - **Multiplication:** the exact product, truncated toward zero to 128 bits.
    Relative error in `[−2^−127, 0]`.
  - **Addition:** absolute error at most `2^−126·max(|a|, |b|)`. That allows the
    simple implementation, truncating the smaller operand to the larger's
    128-bit grid while aligning, then the sum. An absolute bound stays valid
    where terms cancel, as in step 1 below.
  - **Conversion** from binary64, and **rounding** to binary64
    (nearest-even, subnormals included): exact, in integer arithmetic.

**General case** (`|x| ≥ 2^−30`):
1. `r = r1 − p2 − e2 − p3 − e3 − RN(n·L4)`, each binary64 term converted exactly
   to `Q128` and summed left to right.
   - Five additions, each within `2^−126` of operands below `2^−8.48`, so the
     absolute error is below `2^−131`.
   - The neglected tail, `n·(L − L1 − L2 − L3)` beyond `RN(n·L4)`, is below
     `2^−187`.
2. `e^r` by its Taylor series to degree 12, in Horner form:
   `1 + r(1 + r/2(1 + r/3(… (1 + r/12))))`, with `1/k` as `Q128` constants
   (*generated*). Truncation: `|r|^13/13! < 2^−143`.
3. `Y = T_j·e^r`, with `T_j` as a `Q128` constant (*generated*, error below
   `2^−127`).
4. The result is `Y·2^k` rounded to binary64 directly from `(m, e + k)` in
   integer arithmetic, including subnormals: one rounding.

**Total.** The 128-bit evaluation of `T_j` times the series is within `2^−124`
relative error of the exact `T_j` times the series at the computed `r`
(*certified*: `formal/exp/accurate_level_01.g` to `_12.g`, one per Horner level,
and `accurate_y.g`).
- The error of `r` adds below `2^−131·1.003/0.997 < 2^−130.9`.
- The series' truncation adds below `2^−143`.

So the total relative error is below `2^−123.9`. A relative error `ε` is a
mantissa distance below `2ε` ([LM] footnote 10), so the result is within
`2^−122.9` mantissa distance, against `2^−113` needed (§2). Rounding the 128-bit
result once therefore rounds `e^x` correctly.

**Machine-checked:** `formal/exp/ExpAccurate.v` transcribes the general case,
`accurate_value` and `accurate_at`, on the proved `Q128` transcription
(`formal/q`), and proves it.
- **`acc_r_ok`:** `r` is within `2^−131` of `x − n·ln 2/128`: five additions under
  the addition contract, and the tail beyond `RN(n·L4)`.
- **`series_ok`:** the twelve Horner levels compose to `H_1` within `521·2^−135` of
  the series at the computed `r`. Each level is its certificate's theorem
  (`ExpAccurateLevels.v`, which `generators/exp_accurate_certificates.py` writes
  with the certificates), with its hypotheses proved about the transcription:
  the contracts of `mul` and `add`, zero operands included, and the reciprocal's
  error.
- **`accurate_ok`:** `accurate_at` is within `2^−120` relatively of
  `2^(j/128)·e^R·2^k`, composing `accurate_y.g`, the truncation (`2^−143`, by
  CoqInterval) and the error of `r`. `2^−120` is what rounding once needs; the
  sharper `2^−123.9` above isn't required.
- **`exp_accurate_ok`:** for every finite `x` with `−745.1333 ≤ x < X_OVERFLOW`,
  if `e^x` keeps [LM]'s mantissa distance `2^−113` from every rounding
  breakpoint, the value the accurate path returns is `RN(e^x)`. That distance
  is [LM] Property 1, a published computational result. It is the theorem's one
  stated hypothesis (`midpoint_far`), not something Coq derives.

`ExpTables.v` proves the `Q128` table `T_j` and the reciprocals `1/k` within
`2^−127` with CoqInterval. The formal job compares `accurate_at` with the Rust
code bit for bit on the internal cross-check corpus.

**Small arguments** (`2^−54 ≤ |x| < 2^−30`), which need `2^−158`:
1. `(h, l) = two_sum(1, x)`, exactly `1 + x`.
2. `d = e^x − 1 − x ≈ (x·x·k2)·(1 + (x·k3)·(1 + (x·k4)·(1 + x·k5)))` in `Q128`,
   with `k_i = 1/i`.
   - Its relative error against the same expression evaluated exactly is below
     `2^−122` (*certified*: `formal/exp/small.g`). With `|d| ≤ 2^−61`, that's
     below `2^−183` absolute.
   - Truncating after `x⁵`: `|x|^6/720 < 2^−189`.
3. `w = l + d` in `Q128`: `|l| ≤ ulp(h)/2 ≤ 2^−53` and `|d| ≤ 2^−61`, so the
   addition contract gives absolute error below `2^−179`. The total is below
   `2^−178`.
4. `RN(h + w)`: `h` if `|w|` is below half the gap on `w`'s side of `h`;
   otherwise `h`'s neighbour on that side.
   - [LM] guarantees `e^x` is at least `2^−158` from the breakpoint in mantissa
     distance, which is at least `2^−159` absolute here, and the error is below
     `2^−178`. So the comparison, done exactly in integer arithmetic, decides
     correctly, and no tie can occur.

**Machine-checked:** `formal/exp/ExpSmall.v` transcribes `small_parts` and `small`
on binary64 and the proved `Q128` transcription, and proves them.
- **`d_ok`:** `d` is within `2^−122` relatively of the degree-5 polynomial. That
  is `small.g`'s theorem, with its hypotheses proved about the transcription.
- **`small_parts_ok`:** `h = RN(1 + x)`, `|w| ≤ ulp(h)/2 + 2^−60`, and `h + w` is
  within `2^−178` of `e^x`. The truncation bound `2^−189` is CoqInterval's.
- **`exp_small_ok`:** for every finite `x` with `2^−54 ≤ |x| < 2^−30`, if `e^x`
  keeps [LM]'s mantissa distance `2^−158` from every rounding breakpoint,
  `small` returns `RN(e^x)`. That distance is the theorem's one stated
  hypothesis (`midpoint_far`). The proof covers the test as the code computes
  it: `ulp(h)` and the fraction test on `h`'s encoding, `cmp_abs` against the
  halved gap, and `h.to_bits() ± 1` for the neighbour (`bits_up`, `bits_down`
  in `formal/binary64/Encodings.v`).

The formal job compares `h`, `w` and `small`'s result with the Rust code bit for
bit on the internal cross-check corpus.

## 9. Certificates, proofs and generators

| Artifact | Tool | Establishes |
|---|---|---|
| `generators/exp_constants.py` | mpmath 1.4.1 | writes `crates/morphiq-numerics/src/exp/tables.rs`, `formal/exp/ExpTables.v` and `formal/exp/ExpStageTables.v`: the stages' `INV_N`, `S_L1`–`S_L3`, `S_L2D`, the 512-entry table `S_T` and the polynomial; the fallback's `INV_L`, `L1`–`L4`, `T_j` (double-word and `Q128`) and `1/k` in `Q128`; each checked against its bound |
| `generators/exp_poly.sollya` | Sollya 8.0 | the stages' `d3`–`d5` and the fallback's `c3`–`c6` (`fpminimax`), with their approximation errors (`supnorm`), in `generators/exp_poly.out` |
| `formal/exp/stage_a_reduction.g` | Gappa 1.4.1 | stage A's reduced argument: `r1 − RN(ni·L2D)` within `2^−77` of `R` |
| `formal/exp/stage_a.g` | Gappa | stage A's error, `0x1.2ep−61`, and `\|l\| ≤ 0x1.6ap−10` |
| `formal/exp/stage_b_reduction.g` | Gappa | stage B's `r_h + r_t` within `2^−93` of `R`, `\|r_t\| ≤ 2^−40` |
| `formal/exp/stage_b_poly.g` | Gappa | stage B's polynomial evaluation, within `2^−73` |
| `formal/exp/stage_mvt.g` | Gappa | the polynomial at `r` instead of `R`, within `2^−74` (both stages) |
| `formal/exp/stage_b.g` | Gappa | stage B's error, `0x1.a2p−71`, and `\|l\| ≤ 2^−20` |
| `formal/exp/reduction.g` | Gappa | the fallback's reduced argument, within `2^−113` |
| `formal/exp/poly.g` | Gappa | the fallback's polynomial evaluation error, below `2^−70` |
| `formal/exp/mvt.g` | Gappa | `Q(r) − Q(r_hi)` in the fallback, below `0x1.9p−71` |
| `formal/exp/fast.g` | Gappa | `ε₁ ≤ 2^−69` |
| `formal/exp/accurate_level_*.g`, `accurate_y.g` | Gappa | the accurate path's series and result, within `2^−124` |
| `formal/exp/small.g` | Gappa | the small-argument path's `d`, within `2^−122` relative |
| `generators/exp_accurate_certificates.py` | Python | writes the per-level certificates, with their bounds |

**The Coq proofs** (`formal/exp`, `formal/binary64`), each a transcription of
the Rust code on binary64 with its theorem:

| File | Proves |
|---|---|
| `ExpStageTables.v` (*generated*) | the stages' constants: `L`'s splits, `INV_N`, the polynomial's approximation error (CoqInterval), and the table by one reflective check (`st_t_ok`) |
| `TableCheck.v` | the reflective table check is sound (`table_check_ok`) |
| `StageGappa.v` | tactics that apply the stage certificates' theorems |
| `ExpStageReduction.v` | the screen's reduction (`stage_of_ok`), stage A's `r` (`stage_a_r_ok`), stage B's `r_h` and `r_t` (`stage_b_r_ok`) |
| `ExpStageA.v` | stage A's error (`stage_a_value_ok`) and result (`exp_stage_a_ok`) |
| `ExpStageB.v` | stage B's exact product (`mask_ok`), error (`stage_b_value_ok`) and result (`exp_stage_b_ok`); the screen (`screen_ok`); both stages as `exp` runs them (`exp_stages_ok`) |
| `RoundingConstant.v` | the constant-bound test and the scaling (`decide_const_ok`) |
| `ExpReduction.v`, `ExpFast.v`, `ExpAccurate.v`, `ExpSmall.v`, `ExpTables.v` | the fallback (§8) |

Each stage theorem holds for every finite `|x| < 704` and states its result is
`RN(e^x)` with no hypothesis left: the certificates' theorems are applied
through Gappa's Coq proofs, and every hypothesis they take is proved about the
transcription. The fallback's accurate-path theorems keep their one stated
hypothesis, [LM]'s distance (§8.4).

**Gates:**
- **Certificates:** `scripts/check_certificates.sh`, the `certificates (sollya, gappa)`
  job, runs in a Debian image pinned by digest, with Sollya and Gappa pinned by
  package version. It checks that `formal/exp/binding.sha256` matches, that the
  Sollya script reproduces its output exactly, and that every certificate proves
  its goal.
- **Coq:** `scripts/check_formal.sh`, the formal job, builds every certificate's
  Coq proof, which `scripts/write_gappa_proofs.sh` writes there with the same
  pinned Gappa (`gappa -Bcoq`). Gappa's proof search can take a different,
  equally valid route on a different host, so the proofs aren't committed; the
  theorem each proves is stated by the bound certificate. Gappa checks a rewriting hint only symbolically and states it as a
  hypothesis of its proof; the gate turns each hypothesis into a lemma proved
  by `formal/gappa/Hints.v`, so no hint is assumed. A hint that divides states
  its denominators' nonzero conditions (`{ x <> 0 }`), which Gappa proves from
  the bounds. The final theorems' axioms must be among
  `formal/axioms.expected` (and, for the constants CoqInterval proves,
  `formal/axioms.int63.expected`). The job then extracts the transcriptions
  and compares them with the Rust code bit for bit on the internal cross-check
  corpus: `Stages::of`'s words, both stages' values and their tests' outcomes
  on arguments across `|x| < 704`, at ties of `x/L` and tiny, including
  arguments where stage B's test fails.
- **Replay:** `scripts/check_generators.sh` replays the Python generators.

**The binding:** it covers this document, the constants, the Sollya script and
output, every certificate, and the kernel's source (`exp/mod.rs`, `q128.rs`).
Editing any of them fails the gate until the certificates are rerun and the
manifest is updated.

## 10. Checked by

- **Bit-exact agreement** with `crates/reference/fixtures/exp.json`, 4,286 cases
  (`crates/reference/tests/exp.rs`):
  - [LM] Table 4's worst cases. They are hard for the directed roundings only:
    each `e^x` lies within `2^−58` ulp of a binary64 number, but half an ulp
    from every midpoint;
  - **near midpoints, constructed:** for `x = (2k+1)·2^−53`, `1 + x` is a
    midpoint and `e^x` lies within about `(2k+1)²·2^−55` ulp of it (and below 1
    with `x = −(2k+1)·2^−54`). Every test fails on these, and the fallback's
    small-argument path decides them;
  - every threshold and its neighbour, special values, a regression (`−0.6`)
    and random arguments.
- **Every unrounded result within its certified bound,** against `e^x` to 192
  bits for 1,200 arguments (the fixture's `precise` section), in exact
  arithmetic (`src/exp/tests.rs`): stage A's `y + l` within `5·2^−63` and stage
  B's within `7·2^−73` of `e^x/2^k` (above the certified `0x1.2ep−61` and
  `0x1.a2p−71`), the fallback's fast value within `2^−69`, the accurate path's
  `Q128` value within `2^−123.9`, and the small-argument path's `h + w` within
  `2^−178`. This catches accuracy defects that no rounded result shows.
- **The stages against the old algorithm.** `exp` before this change is the
  fallback, so `src/exp/tests.rs` compares each stage's result, wherever its
  test passes, and `exp` itself with `fallback` bit for bit: on 2^20 arguments
  in every test run (uniform in `|x| < 704`, and one in four of magnitude
  `2^−64` to 1), and on 2^28 on demand
  (`stages_agree_on_a_large_corpus`). Stage B is run on every argument, not
  only those stage A leaves, so it is checked everywhere. The run also bounds
  the undecided rates: stage A at most twice its analytic `2^−7.4` and stage B
  at most four times its `2^−17`.
- **The fallback's fast value against the accurate path** on 2^20 arguments:
  equal whenever the fast value decides. It sent 23 of 1,021,637 (`2^−15.4`) to
  the accurate path, against the analytic `2^−15`; the test fails above four
  times that.
- **The `Q128` contract, proved:** `formal/q` proves the contract for any
  significand width (`QSpec.v`, `QRound.v`) and that a step-for-step
  transcription of `q128.rs` computes it (`Q128.v`: `mul_value`, `add_ok`,
  `to_f64_ok`, `from_f64_ok`, `neg_ok`, `mul_pow2_ok`). The formal job
  extracts the transcription and compares it with `q128.rs` bit for bit on the
  internal cross-check corpus (`src/internal_crosscheck.rs`). `src/q128/tests.rs` also checks
  the contract in exact big-integer arithmetic, ties and subnormals included.
- **The determinism digest's `exp` section** on every target
  ([determinism.md](determinism.md)), unchanged by the stages: a correctly
  rounded function's bits don't depend on how they are computed.
- **The lanes** ([lanes.md](lanes.md) §4) transcribe the stages operation for
  operation, checked word for word against `Stages::a_value` and `b_value`.
- Exhaustive checks of chosen sub-intervals against the oracle (scheduled).

## 11. Cost

**Stage A** is about 20 floating-point operations after the reduction's 5,
with one table load; **stage B**, which runs for about one argument in 2^7.3,
about 30 more. The fallback costs about 20 ns on its fast value and 210–240 ns
on its accurate path, for about one argument in 2^17 inside the screen.

**Local measurement** (one Apple M1 Pro, release build, Rust 1.97.1,
`cargo test --release -p morphiq-numerics --lib exp::tests::measure_cost --
--ignored --nocapture`; not a gate). The 1-minute load average was 3.2–3.3,
with one core busy with another job and no other benchmark running. Each
figure is the median of seven rounds; two runs agreed within 2%. Throughput
is independent calls over a shuffled grid of 4,096 arguments; latency chains
each argument to the previous result. `fallback` is `exp` before the stages,
the same code in the same build:

| Arguments | `exp` throughput | `fallback` throughput | `exp` latency | `fallback` latency |
|---|---|---|---|---|
| `[−30, 0]` | 4.04 ns | 20.00 ns | 25.6 ns | 56.5 ns |
| `[−1, 1]` | 4.06 ns | 20.01 ns | 25.6 ns | 56.5 ns |
| `[−700, 700]` | 4.04 ns | 20.02 ns | 25.7 ns | 56.5 ns |

That is about 5× the throughput and 2.2× shorter latency. Batched, two NEON
lanes take 2.34 ns per argument on `[−30, 0]` ([lanes.md](lanes.md) §7). Only
this host is measured. On x86-64 the table's smaller footprint (§3) is
expected to matter more than here, but that is inferred, not measured.
