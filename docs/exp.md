# `exp`: correctly rounded exponential

`morphiq_numerics::elementary::exp` (`crates/morphiq-numerics/src/exp/`) follows
this derivation step for step; its accurate path uses the `Q128` type of §6
(`crates/morphiq-numerics/src/q128.rs`). Every bound below is certified, and
every constant generated, by the artifacts in §7. Each numbered **decision** is
a design choice open to review, and one argument is marked for a second reader
(§2).

`exp(x)` returns `e^x` rounded to nearest, ties to even, for every binary64 `x`.
Subnormal results are rounded once. Here `u = 2^−53`, `RN` is round-to-nearest-even,
and `L = ln 2 / 128`.

## Sources

- **[Tang]** P. T. P. Tang, "Table-driven implementation of the exponential function
  in IEEE floating-point arithmetic", *ACM TOMS* 15(2), 1989: the table-driven
  reduction and reconstruction (§3, §4).
- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: the accuracy that
  decides every case (Property 1, Tables 2 and 4).
- **[Ziv]** A. Ziv, "Fast evaluation of elementary mathematical functions with
  correctly rounded last bit", *ACM TOMS* 17(3), 1991: a fast path that returns
  only when its result provably rounds correctly, with a slower accurate path
  otherwise.
- **[DW]** This crate's double-word arithmetic ([double-word.md](double-word.md)):
  its operations have machine-checked error bounds in IEEE 754 arithmetic.

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
bisection with a rigorous interval oracle. That generator is already on `main`,
and its fixture `crates/reference/fixtures/exp.json` is the test reference:
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

## 3. Argument reduction (after [Tang] §4, Step 2)

**Decision 1: a table of `N = 128` entries `T_j = 2^(j/128)`.** This keeps
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
   - **Fast path:** `r1 = x − n·L1` is exact (Sterbenz, as in [Tang] §5.1, for
     `n ≠ 0`; `r1 = x` for `n = 0`). `(p2, e2) = two_prod(n, L2)` is exact.
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
     `RN(n·L4)` are summed in 128-bit arithmetic (§5).

Then `e^x = 2^k · T_j · e^r`.

## 4. Fast path

**Decision 2: everything after the polynomial uses the crate's proved
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
   at `r_hi`, not the exact `r`; the difference `|Q(r) − Q(r_hi)|` is below
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

At that bound the rounding test (§5) should send roughly one argument in 2^15 to
the accurate path; measured, it sends one in 2^15.4 (§8).

**Decision 3: the fast path doesn't handle results that may be subnormal**
(`k < −1021`). They go straight to the accurate path, which rounds once. Scaling
a rounded fast result by `2^k` there would round twice.

## 5. Rounding test

`Y = (y_hi, y_lo)` is a double-word number, so `y_hi = RN(y_hi + y_lo)`. `y_hi` is
the correctly rounded `e^x / 2^k` whenever the interval
`y_hi + y_lo ± ε₁·|Y|` contains no rounding breakpoint. Those are the midpoints
between `y_hi` and its neighbours.

**Decision 4: the test, with the crate's exact `ulp`:**
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

## 6. Accurate path

**Decision 5 (made): 128-bit significand arithmetic,** not triple-word.
- **Why not triple-word:** Fabiano, Muller and Picot's triple-word algorithms
  assume a fused multiply-add, which `core` doesn't offer. Their bounds don't
  hold verbatim without one.
- **The type:** a private sign-magnitude type `Q128 = (sign, m: u128, e: i32)`,
  with value `±m·2^e`, and `m` normalized (top bit set) or zero. It is
  deterministic on every target and uses only integer instructions.
- **Its contract,** which the certificates assume. It is proved in Coq (§8):
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

## 7. Certificates and generators

| Artifact | Tool | Establishes |
|---|---|---|
| `generators/exp_constants.py` | mpmath 1.4.1 | writes `crates/morphiq-numerics/src/exp/tables.rs`: `INV_L`, `L1`–`L4`, `T_j` (double-word and `Q128`), `1/k` in `Q128`, each checked against its bound |
| `generators/exp_poly.sollya` | Sollya 8.0 | `c3`–`c6` (`fpminimax`) and the approximation error (`supnorm`), in `generators/exp_poly.out` |
| `formal/exp/reduction.g` | Gappa 1.4.1 | the fast path's reduced argument, within `2^−113` |
| `formal/exp/poly.g` | Gappa | the polynomial's evaluation error, below `2^−70` |
| `formal/exp/mvt.g` | Gappa | `Q(r) − Q(r_hi)`, below `0x1.9p−71` |
| `formal/exp/fast.g` | Gappa | `ε₁ ≤ 2^−69` |
| `formal/exp/accurate_level_*.g`, `accurate_y.g` | Gappa | the accurate path's series and result, within `2^−124` |
| `formal/exp/small.g` | Gappa | the small-argument path's `d`, within `2^−122` relative |
| `generators/exp_accurate_certificates.py` | Python | writes the per-level certificates, with their bounds |

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
  `formal/axioms.expected`.
- **Replay:** `scripts/check_generators.sh` replays the Python generators.

**The binding:** it covers this document, the constants, the Sollya script and
output, every certificate, and the kernel's source (`exp/mod.rs`, `q128.rs`).
Editing any of them fails the gate until the certificates are rerun and the
manifest is updated.

## 8. Checked by

- **Bit-exact agreement** with `crates/reference/fixtures/exp.json`, 4,286 cases
  (`crates/reference/tests/exp.rs`):
  - [LM] Table 4's worst cases. They are hard for the directed roundings only:
    each `e^x` lies within `2^−58` ulp of a binary64 number, but half an ulp
    from every midpoint, so none reaches the accurate path;
  - **near midpoints, constructed:** for `x = (2k+1)·2^−53`, `1 + x` is a
    midpoint and `e^x` lies within about `(2k+1)²·2^−55` ulp of it (and below 1
    with `x = −(2k+1)·2^−54`). These make the rounding test fail and decide the
    result on the small-argument path;
  - every threshold and its neighbour, special values, a regression (`−0.6`)
    and random arguments.
- **Every unrounded result within its certified bound,** against `e^x` to 192
  bits for 1,200 arguments (the fixture's `precise` section), in exact
  arithmetic (`src/exp/tests.rs`): the fast path's `Y` within `2^−69`, the
  accurate path's `Q128` value within `2^−123.9`, and the small-argument path's
  `h + w` within `2^−178`. This catches accuracy defects that no rounded result
  shows.
- **The fast path against the accurate path** on 2^20 arguments: equal whenever
  the fast path returns. It sent 23 of 1,021,637 (`2^−15.4`) to the accurate
  path, against the analytic `2^−15`; the test fails above four times that.
- **The `Q128` contract, proved:** `formal/q` proves the contract for any
  significand width (`QSpec.v`, `QRound.v`) and that a step-for-step
  transcription of `q128.rs` computes it (`Q128.v`: `mul_value`, `add_ok`,
  `to_f64_ok`, `from_f64_ok`, `neg_ok`, `mul_pow2_ok`). The formal job
  extracts the transcription and compares it with `q128.rs` bit for bit on the
  internal cross-check corpus (`src/internal_crosscheck.rs`). `src/q128/tests.rs` also checks
  the contract in exact big-integer arithmetic, ties and subnormals included.
- **The determinism digest's `exp` section** on every target
  ([determinism.md](determinism.md)).
- Exhaustive checks of chosen sub-intervals against the oracle (scheduled).
