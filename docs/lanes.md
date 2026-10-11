# Batched functions and lane evaluation

`morphiq_numerics::elementary::{exp_slice, ln_slice, ln_1p_slice}` apply
[`exp`](exp.md), [`ln` and `ln_1p`](ln.md) to every element of a slice. The
lane kernels are `crates/morphiq-numerics/src/lanes/`, `exp/lanes.rs` and
`ln/lanes.rs`; the SIMD backends are the `morphiq-numerics-arch` crate
([arch.md](arch.md)).

## 1. Contract

`f_slice(x, out)` sets `out[i]` to `f(x[i])`, bit for bit, for every `i`, on
every target, with or without the `simd` feature. It panics if `x` and `out`
have different lengths, as `reduce::dot` does. So the batched functions add
no claim of their own: each inherits its scalar function's (correct rounding
for `exp` and `ln`; correct rounding where its rounding test decides, and
`(1/2 + 2^−70)` ulp otherwise, for `ln_1p`).

- **Without `simd`** each loops its scalar function.
- **With `simd`** each runs on the widest backend the CPU has ([arch.md](arch.md)).
  Every lane performs the scalar function's fast path operation for operation:
  its special-argument screen, its argument reduction, its double-word
  evaluation and its rounding test (§4, §5). A lane the screen sends elsewhere,
  or the rounding test doesn't decide, calls the scalar function itself, and
  so do the last `len mod LANES` elements. A one-lane backend loops the scalar
  function.
- **Within the crate,** `log_space::log_sum_exp` evaluates its terms'
  exponentials with `exp_slice`, and `log_space::log_sum_exp_pairs` its pairs'
  exponentials and logarithms with `exp_slice` and `ln_1p_slice`, so they
  return the same bits too ([log_space.md](log_space.md), decision 7).
- **The `std` feature** turns on runtime CPU detection. It changes which
  backend runs, so speed, never a result. The library stays `no_std`.

**Why the bits are the scalar function's, by construction.** IEEE 754 fixes
each binary64 operation's result, and every lane operation is that operation
([arch.md](arch.md), "the floating-point environment"). A lane that performs the
scalar fast path's operations on the same argument therefore computes the
same double-word `Y`, word for word, and the same rounding test on it. If the
test passes, the scalar function's fast path passes it too and returns the
same value; if not, the lane calls the scalar function. The one operation that
differs between backends is `two_prod`'s error term, which §2 shows is the
same bits wherever a kernel uses it, and the one computation written
differently is the rounding test's gap, which §3 shows is the same value.

This doesn't rest on correct rounding. (It would follow from it too for `exp`
and `ln`: two correctly rounded evaluations agree whatever their operations.
But `ln_1p` isn't proved correctly rounded everywhere, and agreement
operation for operation is what the tests check.)

## 2. The error-free product: FMA or Dekker, the same bits

`eft::two_prod(a, b)` returns `p = RN(a·b)` and `e`, computed by Dekker's
split and Veltkamp's product. On its domain `D` — `a·b = 0` or
`|a·b| ≥ 2^−969`, with `|a| ≤ 2^e_a`, `|b| ≤ 2^e_b`, `e_a, e_b ≤ 994`,
`e_a + e_b ≤ 1020` — `p + e = a·b` exactly
([double-word.md](double-word.md): `two_prod_exact`,
`formal/two-prod/TwoProdBinary64.v`, Flocq's `Dekker` theorem; overflow
excluded by `two_prod_ieee`, `formal/binary64/IEEE64Eft.v`).

On a backend with a hardware fused multiply-add (NEON, AVX2 with FMA,
AVX-512F) the lane `two_prod` computes `e' = RN(a·b − p)`, one fused
operation (`mul_add(a, b, −p)`). On SSE2 and the scalar backend, which have
none, it performs Dekker's operations as `eft.rs` writes them. **On `D`,
`e' = e` bit for bit:**

1. **A nonzero error.** `e` is a binary64 number equal to `a·b − p`, so
   `a·b − p` is representable, and rounding it returns it: `e' = a·b − p = e`.
   (The FMA rounds the exact `a·b − p` once; it has no intermediate rounding to
   go wrong.)
2. **A zero error.** Then both are `+0`.
   - *FMA.* Under round-to-nearest an exact zero sum of operands of opposite
     sign is `+0` (IEEE 754-2019 §6.3). If `a·b ≠ 0`, the sum `a·b + (−p)` is
     such a sum. If `a·b = 0`, `p` is a zero with the product's sign, so `−p`
     has the opposite sign, and the sum is again `+0`.
   - *Dekker.* `e` is a chain of rounded sums, and a rounded sum is `−0` only
     when both addends are `−0`. Its first term, `a_h·b_h − p`, is `−0` only
     if `a_h·b_h = −0` and `p = +0`. On `D`, `p = +0` means `a·b = 0` with
     `a` and `b` of the same sign. The split's head of `±0` is `+0`, so if
     `a = ±0`, `a_h·b_h = −0` needs `b < 0`, hence `a = −0`, and then
     `a_t = −0` makes the third term `a_t·b_h = +0`, so the third partial sum
     is `+0`. The case `b = ±0` is symmetric, through the second term. So `e`
     is never `−0` on `D`.

These are the hypotheses Dekker's product already needs, so every place a
kernel calls `two_prod` is covered by the argument the scalar derivation makes
for it:

| Call | Operands | Why on `D` |
|---|---|---|
| `exp`: `two_prod(n, L2)` | an integer `\|n\| ≤ 137,601`; `\|L2\| < 2^−43` | product zero or above `2^−45` ([exp.md](exp.md) §3) |
| `exp`: `T_j.mul(E)` | `T_j ∈ [1, 2)`, `E` within `2^−8` of 1 | ([exp.md](exp.md) §4) |
| `ln`, `ln_1p`: `two_prod(y, R[i])` | `y ∈ [0.707, 1.415)`, `R[i]` within 0.8% of `1/y` | ([ln.md](ln.md) §3) |
| `ln`, `ln_1p`: `two_prod(z_hi, z_hi)` | `z_hi = 0` or `\|z_hi\| ≥ 2^−64` (case A: `\|x\| ≥ 2^−54`) | square zero or at least `2^−128` ([ln.md](ln.md) §3, §7) |

A lane the screen sends to the scalar function may carry operands outside `D`
(a NaN, an infinity), but its value is discarded.

The test `lane_two_prod_is_efts_two_prod` compares the lane product with
`eft::two_prod` bit for bit: on random encodings without FMA, and on `D`, with
zeros of both signs, with it.

## 3. The rounding test's gap

`ln::decide_with` (which `exp::decide_scaled` matches for `y_hi > 0`) returns
`y_hi` when `RN(|y_lo| + RN(eps·|y_hi|)) < g/2`, where `g` is `ulp(|y_hi|)`,
halved when `|y_hi|` is a power of two ([exp.md](exp.md) §5). The lane test
performs the same three operations and the same comparison, and computes `g`
from the exponent field instead of calling `ulp`:
- for a biased exponent `B > 52`, `ulp` returns the encoding `(B − 52) << 52`,
  which the lane forms by subtracting `52 << 52` from the masked field;
- the halved gap is `(B − 53) << 52`, which equals `ulp/2` when `B ≥ 54`.

So the lane computes the same `g` for `|y_hi| ≥ 2^−969` (`B ≥ 54`), and below
that it reports "not decided", which sends the lane to the scalar function.
For infinities and NaNs both tests fail. No lane reaches either case in
practice: `exp`'s `y_hi` lies in `[3/4, 4]`, and `ln`'s and `ln_1p`'s results
exceed `2^−55` in magnitude.

## 4. `exp`

Per lane, as `exp` and `Reduced::of` write them:
1. **The screen** (in scalar code, per lane): NaN, `x ≥ X_OVERFLOW`,
   `x ≤ X_ZERO` and `−2^−54 ≤ x < 2^−53` go to `exp` ([exp.md](exp.md) §1).
2. **The reduction** in lanes: `n = (x·INV_L + S) − S`, `r1 = x − n·L1`,
   `(p2, e2) = two_prod(n, L2)`, `(s, t) = two_sum(r1, −p2)`,
   `rr = (t − e2) − n·L3`, `r = two_sum(s, rr)`.
3. **The index and scale** per lane: `n` converted to an integer exactly,
   `j = n mod 128`, `k`; the table pair `T_j` is loaded per lane (no gather);
   `2^k` from its encoding. Lanes with `k < −1021` go to `exp`, as its fast path
   excludes them ([exp.md](exp.md) §4, decision 3), and so do lanes with
   `k = 1024`, which `exp` scales in two steps.
4. **`fast_at`** in lanes: the Horner polynomial, `add_f64`, `add` to 1, and the
   product with `T_j`, each double-word operation as `double_word.rs` writes it.
5. **`decide_scaled`** in lanes (§3), and `y_hi·2^k`.

## 5. `ln` and `ln_1p`

**`ln`:**
1. **The screen** per lane: NaN, `x ≤ 0`, `+∞` and `1` go to `ln`.
2. **The reduction** in lanes, as `Reduced::of` computes it: a subnormal `x`
   scaled by `2^54` (selected per lane); `m = 1.fraction` from the encoding;
   `i ≥ 53` exactly when `m ≥ 1 + 53/128`, and then `y = m/2`, which is the
   encoding with exponent 1022, else `y = m`; `E` as the biased exponent less
   1022 or 1023 and less 54 if scaled, the biased exponent read as an integer
   below `2^52` from `2^52`'s encoding, every step exact in binary64 (small
   integers). Only the index `i` and the table loads of `R[i]` and `−ln R[i]`
   are per lane. The fast values' word-for-word test (§6) checks the result
   against `Reduced::of` itself.
3. **`fast_value`** in lanes: `two_prod(y, R[i])`, `z = two_sum(p − 1, q)`,
   `ln_1p_double_word(z)`, the table term and `E·ln 2`, as `ln/mod.rs` writes
   them.
4. **`decide`** in lanes (§3).

**`ln_1p`:**
1. **The screen** per lane: NaN, `x ≤ −1`, `+∞` and `|x| < 2^−54` go to
   `ln_1p`. Lanes with `|x| < 2^−7` are case A, the others case B
   ([ln.md](ln.md) §7).
2. **Case B's split** in lanes: `(h, l) = two_sum(1, x)` below `2^53`, else
   `(x, 1)`, chosen per lane by a select. Then `ln`'s in-lane reduction of `h`.
3. **`z`** per lane: case A's `(x, 0)`, case B's `two_sum(p − 1, q)`, chosen by a
   select. `ln_1p_double_word(z)` then runs once for both cases: it is the same
   function on each lane's own `z`.
4. **Case B continues** in lanes: the table term, `E·ln 2`, and `add_f64(l/h)`.
   A case-A lane computes these on a placeholder reduction and discards them:
   a select returns `ln_1p_double_word(z)` itself there. When every lane of a chunk is
   case A (or screened), steps 2 to 4 reduce to `ln_1p_double_word((x, 0))`
   alone.
5. **`decide`** in lanes (§3).

## 6. Checked by

- **Bit equality on every backend** (`src/lanes/tests.rs`): each kernel
  against its scalar function, on every backend the CPU has, from the widest
  down to the scalar backend, each run through the backend's `vectorize` as the
  library runs it. The corpora:
  - every binary64 in the function's reference fixture (`exp.json`,
    `ln.json`), arguments and results alike;
  - special values and their neighbours, and every threshold and branch edge
    of [exp.md](exp.md) §1 and [ln.md](ln.md) §7;
  - random encodings; for `exp` the whole domain, `[−30, 0]`, ties of `x/L`
    and every binade near zero; for `ln` every positive encoding, `[0.5, 2)`,
    the neighbourhood of 1 and the subnormals; for `ln_1p` `e^d` for
    `d ∈ [−30, 0]`, `z²/4` for `z ∈ [−6, 6]`, `[−1, 2^60]` log-uniform, every
    magnitude, and the neighbourhoods of −1, `2^−7` and `2^53`.

  `MORPHIQ_LANE_CASES` sets each random section's size (default 2^18, about
  1.3 to 2.1 million arguments per function); every remainder and lane
  position is covered by slices of every length from 0 to 17 at eight
  offsets.
- **The fast values word for word** (`exp/lanes/tests.rs`,
  `ln/lanes/tests.rs`): on the same corpora, every lane the scalar function
  would try its fast path on has the scalar fast value's bits, `y_hi` and
  `y_lo`. This shows the kernels transcribe the scalar operations, which the
  final results alone could not: a different but accurate sequence would
  usually round alike.
- **The public functions** on the dispatched backend, for every length from 0
  to 17 and a long slice, and their length check.
- **The error-free product** (§2).
- **The determinism digest's `exp_slice`, `ln_slice` and `ln_1p_slice`
  sections** ([determinism.md](determinism.md)), with and without `simd`.

**Backends in CI.** `MORPHIQ_REQUIRE_BACKENDS` fails the run when a listed
backend is absent, so each job states what it exercised: the `test` job
requires `avx2` and `sse2` on its x86-64 hosts and `neon` on its aarch64
hosts; the `simd (avx512, sde)` job runs the lane and arch tests under Intel's
Software Development Emulator (pinned in `.cargo/sde-version` and
`.cargo/sde-sha256`), requiring `avx512`.

## 7. Performance

The kernels are `O(n)` in the slice length and allocate nothing; each chunk of
`LANES` elements uses fixed-size arrays on the stack. The per-lane scalar
parts are the screens, the table indices and the table loads; no gather
instruction is used. Lanes sent to the scalar function cost a scalar
evaluation on top: about `2^−15.4` of `exp`'s arguments and `2^−9.4` of `ln`'s
([exp.md](exp.md) §8, [ln.md](ln.md) §9), plus the screened ones.

`crates/reference/src/bin/bench-batched.rs` times a loop of the scalar
function against the batched one, as the median over 31 rounds of the time per
element on 4,096 arguments:

```sh
cargo run --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-batched
```

Measured on one Apple M1 Pro (NEON, 2 lanes), `--release`, Rust 1.97.1, with
the 1-minute load average at 2.8 and no other benchmark running; two
consecutive runs agreed within 0.1 ns:

| Function | Arguments | Scalar loop (ns) | Batched, NEON (ns) | Speed-up |
|---|---|---|---|---|
| `exp` | `[−30, 0]` | 19.46 | 8.39 | 2.32× |
| `exp` | `[−745, 709]` | 24.15 | 13.93 | 1.73× |
| `ln` | `[0.5, 2)` | 29.50 | 14.73 | 2.00× |
| `ln` | positive encodings | 29.54 | 14.78 | 2.00× |
| `ln_1p` | `e^d`, `d ∈ [−30, 0]` | 16.70 | 9.78 | 1.71× |
| `ln_1p` | `z²/4`, `z ∈ [−6, 6]` | 33.67 | 18.15 | 1.85× |
| `ln_1p` | `[−1, 2^60]`, log-uniform | 34.77 | 18.23 | 1.91× |

`exp` on its whole domain gains less because arguments with subnormal results
(`k < −1021`, `x < −707.7`: 2.6% of these arguments) go to `exp`
itself, and those take its accurate path.

Only the NEON figures are measured. SSE2, AVX2 and AVX-512F are checked for
bit equality, not timed: timing on a CI runner is not evidence, and no x86-64
host was measured.
