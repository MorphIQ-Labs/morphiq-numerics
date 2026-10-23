# Batched functions and lane evaluation

`morphiq_numerics::elementary::{exp_slice, exp2_slice, expm1_slice, ln_slice, ln_1p_slice, asin_slice, asinh_slice, atan2_slice}` (and the bivariate normal's slice forms, below) apply
[`exp`](exp.md), [`exp2`](exp2.md), [`expm1`](expm1.md), [`ln` and `ln_1p`](ln.md) to every element of a slice. The
lane kernels are `crates/morphiq-numerics/src/lanes/`, `exp/lanes.rs`, `exp2/lanes.rs`, `expm1/lanes.rs` and
`ln/lanes.rs`; the SIMD backends are the `morphiq-numerics-arch` crate
([arch.md](arch.md)).

`morphiq_numerics::normal::erfcx_slice` uses the same backends and cascade.
Its table, reciprocal and reflection kernels are in `erfcx/lanes.rs`;
[erfcx.md](erfcx.md) states their operation sequences and current assurance
limits. As with the elementary slices, its numerical contract is inherited
from its scalar function.

The normal-family `norm_pdf_slice`, `norm_cdf_slice`, `norm_ccdf_slice`,
`norm_cdf_centered_slice` and `log_norm_cdf_slice` also use every backend.
Their shared compositions, saturation shortcuts and scalar fallback rules
are described in [normal.md](normal.md). Both intermediate words and final
results are compared lane by lane with the scalar kernels.

## 1. Contract

`f_slice(x, out)` sets `out[i]` to `f(x[i])`, bit for bit, for every `i`, on
every target, with or without the `simd` feature. It panics if `x` and `out`
have different lengths, as `reduce::dot` does. So the batched functions add
no claim of their own: each inherits its scalar function's (correct rounding
for `exp`, `exp2` and `ln`; correct rounding where its rounding test decides, and
`(1/2 + 2^−70)` ulp otherwise for `ln_1p`, or `(1/2 + 2^−65)` ulp otherwise for `expm1`).

- **Without `simd`** each loops its scalar function.
- **With `simd`** each runs in lanes ([arch.md](arch.md)). Every lane performs
  the scalar function's first stage operation for operation: its
  special-argument screen, its argument reduction, its evaluation and its
  rounding test (§4, §5); for `ln` that is the reciprocal stage, for
  `exp` and `exp2` their stages, for `expm1` its small polynomial or stages,
  for `ln_1p` stage H. A lane the screen sends elsewhere,
  or the rounding test doesn't decide, calls the scalar function from that
  point on (for `ln_1p`, from stage B).
- **The backend cascade.** The slice runs through the backends the CPU has,
  widest first: AVX-512F, AVX2 and SSE2 on x86-64, and NEON on aarch64. Each
  backend takes as many whole chunks of its own width as remain. So a slice
  or a remainder of at least two elements still runs in lanes: seven
  elements on AVX-512F run as one AVX2 chunk, one SSE2 chunk and one scalar
  call. Only a last single element, or a target with no lane backend, is
  left to the scalar function. Every backend returns the scalar bits, so the
  order in which they share a slice changes nothing.
- **Within the crate,** `log_space::log_sum_exp` evaluates its terms'
  exponentials with `exp_slice`, and `log_space::log_sum_exp_pairs` its pairs'
  exponentials and logarithms with `exp_slice` and `ln_1p_slice`, so they
  return the same bits too ([log_space.md](log_space.md), decision 7).
- **The `std` feature** turns on runtime CPU detection. It changes which
  backend runs, so speed, never a result. The library stays `no_std`.

**Why the bits are the scalar function's, by construction.** IEEE 754 fixes
each binary64 operation's result, and every lane operation is that operation
([arch.md](arch.md), "the floating-point environment"). A lane that performs the
scalar stage's operations on the same argument therefore computes the
same values, word for word, and the same rounding test on them. If the
test passes, the scalar function's stage passes it too and returns the
same value; if not, the lane continues where the scalar function does. The one operation that
differs between backends is `two_prod`'s error term, which §2 shows is the
same bits wherever a kernel uses it. The computations written differently are
`ln`'s and `ln_1p` stage H's equality tests, which §3
shows are the same value, and `exp`'s test
and scaling, which §4 shows return the same bits.

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

`exp2` stage B uses `two_prod(d, LN2_HI)`. The screen gives
`2^−55 ≤ |x| < 1016`; reduction leaves `d = x − n/512` exactly.
If `n = 0`, a nonzero `d` is at least `2^−55`. Otherwise the smallest
nonzero distance occurs beside `1/512`, whose lower neighbour is `2^−62`
away. Hence `d = 0` or `2^−62 ≤ |d| ≤ 2^−10`, and `1/2 < LN2_HI < 1`:
the product is zero or at least `2^−63`, safely in `D`.
`expm1`'s small polynomial uses `two_prod(x, x)` for
`2^−54 ≤ |x| < 2^−5`, so the product is at least `2^−108`, also in `D`.
Both kernels substitute in-domain placeholders for inactive lanes before
these operations. NaNs, infinities and tiny inputs therefore never enter
the fused product outside its proved domain.

`exp`, `ln` and `ln_1p` need no `two_prod`: their products that must be
exact are exact by construction with plain multiplications.

**Scalar kernels.** The same equality lets scalar kernels use the fused error
term. `eft::two_prod_d` computes `RN(a·b − p)` with one fused multiply-add
when `std` is enabled and the build targets x86 FMA (`target_feature = "fma"`)
or aarch64 NEON (`target_feature = "neon"`, which includes binary64 FMA), and runs
Dekker's operations otherwise. It is crate-private, and every call names the
proof that keeps its arguments in `D`: the normal family's exact half square
(`NormalGaussianKernel.normal_half_square_exact` and the negative log-tail
table's `NormalLogFirst.normal_log_first_square`), its scaled argument
`a/√2` (`DoubleWord::mul_f64_d`, `NormalFastScaledArgument`) and its CDF first
stages' products (`NormalTailFirst`, `NormalCenterFirst`), and erfcx's products, reciprocal, square,
quotient and reflection square (`ErfcxProduct`, `ErfcxReciprocal`,
`ErfcxSquare`, `ErfcxQuotient`, `ErfcxReflectionSquare`). The public
`eft::two_prod` and `DoubleWord`'s operations stay Dekker's on every build,
since their callers' arguments are unconstrained. `scripts/check_fma.sh`
builds with FMA, runs the tests and the determinism digest, and requires both
cross-check corpora byte-identical to a Dekker build's. On x86 the baseline
explicitly disables FMA; on aarch64 it disables `std`, keeping the same
arithmetic API while selecting Dekker. The ARM test jobs run this gate as
well as the x86 FMA job.

The test `lane_two_prod_is_efts_two_prod` compares the lane product with
`eft::two_prod` bit for bit: on random encodings without FMA, and on `D`, with
zeros of both signs, with it.

`exp`'s lane kernel uses no `two_prod`: its stages' only product that must be
exact, stage B's `A·r_h`, is exact as a plain product ([exp.md](exp.md) §6),
so no backend uses a fused multiply-add for `exp`.

## 3. The interval rounding test

`ln`'s reciprocal stage and `ln_1p`'s stage H test `lb == ub`, where
`lb = s + (lo − eps)` and `ub = s + (lo + eps)`. The lanes perform the
same additions and compare with `le` both ways. That is `==` for every
pair of non-NaN operands, signed zeros included (IEEE 754-2019 §5.11).
The stages' finite bounds exclude NaNs on every lane they try.

## 4. `exp`

Per lane, as `exp` and `Stages::of` write them ([exp.md](exp.md) §3–§7):
1. **The screen** in lanes: `|x| < 704`, as an ordered comparison of `|x|`
   with 704. It holds exactly where `exp`'s comparison of encodings does: both
   are false for NaN. Lanes that fail it go to `exp`.
2. **The reduction** in lanes: `n = (x·INV_N + S) − S` and `r1 = x − n·S_L1`.
   Per lane, as `Stages::of` computes them: `n` as an integer from `t`'s
   encoding, `j = n & 511`, `k = n >> 9`, the table pair `T_j` (no gather)
   and `2^k` from its encoding.
3. **Stage A** in lanes, as `Stages::a_value` computes it, and its test.
4. **Stage B** in lanes, as `Stages::b_value` computes it, the mask of
   `T_j`'s low 32 bits included, and its test, when a lane in the chunk is
   undecided by stage A; a select takes stage B's result on those lanes.
5. **The scaling** by `2^k` in lanes.

**The test and the scaling, written differently, return the same bits.**
`exp`'s test compares `low = RN(y + RN(l − E))` with `high = RN(y + RN(l + E))`
as numbers; the lanes compare their encodings. On every lane past the screen
both are positive normal numbers (`y + l` lies near `[1, 2]`), and two such
numbers are equal exactly when their encodings are. `exp` scales by adding `k`
to the exponent field; the lanes multiply by `2^k`. The product is exact and
normal (`|k| ≤ 1016`), so it is the same number, with the same encoding.

### `exp2`

The screen and reduction reproduce `exp2::stages`: `2^−55 ≤ |x| < 1016`,
`t = x·512 + S`, `n = t − S`, `d = x − n/512`. The shared table loader
uses the low nine integer bits for `j` and the rest for `k`. Stage A uses
`d·LN2_HI`; stage B compensates that product (§2), then splits it into
`rh` and `rt`. Both call the same lane polynomial evaluators as `exp`.
Their tests use `exp2`'s own bounds, `2^−59` and `2^−70`. Scaling is exact
on the screened normal-result domain, as for `exp`. Screened or undecided
lanes call scalar `exp2`, including every subnormal-result input.

### `expm1`

Inputs with `|x| < 2^−54` return `x` directly, preserving signed zero.
For `2^−54 ≤ |x| < 1/32`, the kernel evaluates `small_fast`'s polynomial,
exact square and double-word additions in the scalar order. Its rounding
test is `ln::decide_with`: the ulp comes from the leading word's exponent,
and the gap is halved at powers of two before the final half-gap comparison.
All evaluated leading words and ulps are normal on this domain.

For `|x| ≥ 1/32`, `|x| < 704`, `x > −37`, the kernel shares `exp`'s
reduction and both stages, then reproduces `expm1::stages::parts`:
`two_sum(h, −2^−k)`, the low-word addition and the subtraction error bound.
Since `−54 ≤ k ≤ 1016`, both `2^k` and `2^−k` are normal; subtracting
`bits(2^k)` from `2046·2^52` constructs `2^−k` exactly.
The interval test uses numerical equality (§3), followed by the same
power-of-two product as the scalar stage. Small and general evaluations
run only when the chunk contains an eligible lane, and stage B only when
stage A leaves an eligible lane undecided. All remaining lanes call scalar
`expm1`, including the Q128 accurate paths.

These are operation-for-operation SIMD transcriptions of the scalar
kernels. The scalar Coq theorems and certificates retain their stated
coverage; the lane equivalence is checked by intermediate-word tests and
the cross-target digest, not a separate Coq model of SIMD instructions.

## 5. `ln` and `ln_1p`

**`ln`:**
1. **The screen** per lane: NaN, `x ≤ 0`, `+∞` and `1` go to `ln`.
2. **The reduction** in lanes, as `Reduced::of` computes it: a subnormal `x`
   scaled by `2^54` (selected per lane); `m = 1.fraction` from the encoding;
   `i ≥ 53` exactly when `m ≥ 1 + 53/128`, and then `y = m/2`, which is the
   encoding with exponent 1022, else `y = m`; `E` as the biased exponent less
   1022 or 1023 and less 54 if scaled, the biased exponent read as an integer
   below `2^52` from `2^52`'s encoding, every step exact in binary64 (small
   integers).
3. **The reciprocal reduction:** the 512-entry table index and loads are per
   lane. Masking the low ten significand bits produces `hh`; the lanes form
   `hl = h − hh` and `z = (hh·rs − 1) + hl·rs`, exactly as `stages::reduce`.
4. **The reconstruction** computes `E·L1`, `E·L0`, the degree-six polynomial,
   `(s, lo)` and `eps`, operation for operation as `ln::stage::parts`.
5. **The interval test** in lanes (§3), followed by the shared double-word
   fallback below. The word-for-word test checks all three values
   `(s, lo, eps)`, including each reciprocal-table boundary and its neighbours.

**`ln_1p`:** stage H ([ln.md](ln.md) §7), as `ln::stages::stage_h_parts`
writes it.
1. **The screen** per lane: lanes outside `2^−46 ≤ |x|`, `−1 < x < 2^53`
   (NaN included) go to `ln_1p` past stage H (stage B, then the fallback),
   and compute stage H on the placeholder 1, whose result is discarded.
2. **The split** in lanes: `s0 = 1 + x`, `l = x − (s0 − 1)`.
3. **The index** per lane, from `s0`'s encoding: `u = bits(s0) − OFF`,
   `E = u >> 52` (arithmetic), `i` the next 9 bits; `R[i]·2^−E` as the
   encoding `bits(R[i]) − (E << 52)`; the table loads of `TH`, `TL` and
   `(E·L1, RN(E·L0))`. No gather instruction is used.
4. **The evaluation** in lanes: `hh` (`s0` with its low 10 bits cleared, by a
   mask), `hl = s0 − hh`, `z = (hh·rs − 1) + hl·rs`, the table sums, `l·rs`,
   the polynomial by Estrin's scheme, `s`, Fast2Sum's `e1`, `lo` and `eps`,
   each operation as the scalar stage writes it.
5. **The test** in lanes (§3); lanes it doesn't decide go to `ln_1p` past
   stage H.

### Shared logarithm fallback

When at least two eligible lanes remain, `ln/lanes/fallback.rs` evaluates
the shared degree-nine polynomial and reconstruction in lanes. It uses
`lanes::add_dw`, `add_f64` and `decide_relative`, also used by the small
`expm1` path. Every addition and multiplication follows the scalar order;
only the error term of `two_prod` uses hardware FMA on eligible backends (§2).

`ln` screens special lanes before evaluating the fallback. `ln_1p` tries
scalar stage B, then groups the remaining finite inputs. Its small branch
uses `(x, 0)` directly; its general branch splits `1 + x`, evaluates `ln h`,
and adds `l/h`, including subnormal quotients. Inactive lanes use finite
placeholders. A single pending lane uses scalar completion; rejected
fallback decisions use the scalar Q128 accurate path.

The word tests compare both fallback words and each rounding decision,
including accepted and rejected cases. Separate tests repeat actual
undecided arguments across lanes and mix them with decided and special
arguments. The scalar fallback and public-entry proofs are in `docs/ln.md`;
intermediate-word tests and the cross-target digest check lane equivalence.

## `asin`

`asin_slice` (`asin/lanes.rs`) runs `asin`'s whole fast path in lanes: the
screen (a NaN, `|x| ≥ 1` and `|x| < ASIN_IS_X` are the scalar function's own
results), `Reduced::of` (the complement's `u = (1 − x)/2`, `s = √u`, the
`two_prod` residual and `two_sum`), `series` (the shifter index, the small
series and the 45-segment table branch, both computed on every lane and
selected by whether the index is zero), `Reduced::fast` (`2·series` as
`mul_f64` rounds it, then `π/2 − δ`) and the rounding test at
`EPS = 2^-62(1 + 2^-50)`. Table rows are read a lane at a time, as `ln`'s
are. `√u` is the scalar `sqrt`, per lane, exactly as `Reduced::of` calls it.
A lane the screen or the test doesn't settle calls `asin` itself, from the
start. Every operation is the scalar operation in the scalar order, with
`two_prod` as §2 states, on its domain: the arguments are `s` (at least
`2^-27`), `t_hi` (zero or at least `2^-900`: `docs/asin.md` §4) and `2`.

## `asinh`

`asinh_slice` (`asinh/lanes.rs`) runs `asinh`'s fast path in lanes: the screen
(a NaN, `±0`, `±∞` and `|x|` up to the threshold are the scalar function's own
results), the series below `2^-7`, the logarithm of `x + √(x² + 1)` (the exact
square, the double-word `u`, `√u` and its Newton correction, `v`, then `ln`'s
double-word fast value through the shared fallback of §5 and `RN(v_lo/v_hi)`),
the large form `ln x + ln 2 + 1/(4x²)` from `2^28`, and the rounding test at
`EPS = 2^-63(1 + 2^-50)`. Each region runs only if some live lane is in it and
is selected by mask. `√u` is the scalar `sqrt`, per lane. A lane the screen or
the test doesn't settle calls `asinh` itself.

## `atan2`

`atan2_slice` (`atan2/lanes.rs`) takes paired arguments (`y[i]`, `x[i]`) through
the `Kernel2` form of the framework (`lanes::map2`, the same backend cascade). Each
lane runs `atan2`'s fast path: the screen (NaNs, zeros, infinities, and the pairs
whose larger magnitude is outside `[2^-900, 2^900]` or whose ratio is below `2^-900`
are the scalar function's), the smaller-over-larger ratio scaled by the exact power
of two read from the larger's exponent field, the double-word quotient with
`two_prod`'s residual, `atan t`'s table and series (as `asin`'s, with 64 rows), the
four forms (each only if some lane takes it), and the rounding test at
`EPS = 2^-62(1 + 2^-50)`. A lane the screen or the test doesn't settle calls `atan2`.

## `bivariate_normal`

`BivariateNormal::cdf_slice` and `bivariate_norm_cdf_slice`
(`bivariate_normal/lanes.rs`) take pairs, or triples with a correlation per
lane, through the same backend cascade; the kernel carries per-lane tables, so
it is a function of a context and not a `Kernel2`. The low-correlation node
loop and Genz's high-correlation series run in lanes with the scalar operation
order, on the library's lane `exp` and `norm_cdf` and the scalar `sqrt` per
lane; the closed-form correlations, NaN and saturated pairs, and any lane whose
result is NaN call the scalar evaluator. The argument and the checks are in
[bivariate_normal.md](bivariate_normal.md) section 12.

## 6. Checked by

- **Bit equality on every backend** (`src/lanes/tests.rs`): each kernel
  against its scalar function, on every backend the CPU has, from the widest
  down to the scalar backend, each run through the backend's `vectorize` as the
  library runs it. The corpora:
  - every binary64 in the function's reference fixture (`exp.json`,
    `exp2.json`, `expm1.json`, `ln.json`), arguments and results alike;
  - special values and their neighbours, and every threshold and branch edge
    of [exp.md](exp.md) §1 and [ln.md](ln.md) §7;
  - random encodings; for `exp` the whole domain, `[−30, 0]`, ties of `x/L`
    and every binade near zero; for `ln` every positive encoding, `[0.5, 2)`,
    the neighbourhood of 1 and the subnormals; for `ln_1p` `e^d` for
    `d ∈ [−30, 0]`, `z²/4` for `z ∈ [−6, 6]`, `[−1, 2^60]` log-uniform, every
    magnitude, the neighbourhoods of −1, `2^−7` and `2^53`, and stage H's
    table intervals' edges at every exponent of its range.

  `MORPHIQ_LANE_CASES` sets each random section's size (default 2^18, about
  0.8 to 2.4 million arguments per function); every remainder and lane
  position is covered by slices of every length from 0 to 17 at eight
  offsets.
- **The fast values word for word** (`exp/lanes/tests.rs`,
  `exp2/lanes/tests.rs`, `expm1/lanes/tests.rs`, `ln/lanes/tests.rs`): on the same corpora, every lane the scalar function
  would try its fast path on has the scalar fast value's bits: for `exp`, both
  stages' `(y, l)` on every lane past the screen, stage B's on every lane and
  not only those stage A leaves; for `ln`, `(s, lo, eps)`; for `ln_1p`,
  stage H's `(s, lo, eps)` on every lane it tries. `exp2` checks both stage
  words and decisions; `expm1` checks both subtraction triples and decisions,
  and the small polynomial's two words and decision. Rejected fast tests
  occur in these corpora and are counted. The new slice APIs also run directly
  against their independent reference fixtures with and without SIMD.
  This shows the kernels transcribe the scalar operations, which the final
  results alone could not: a different but accurate sequence would usually
  round alike.
- **Every cascade** (`every_lanes_cascade_returns_the_scalar_bits`): each
  subset of the CPU's lane backends, widest first, forced in turn, then the
  scalar function. It runs on slices of every length from 0 to 17 at eight
  offsets, and on 4,000 arguments of each function's corpus. On AVX-512F
  hosts that is all eight cascades of AVX-512F, AVX2 and SSE2. The
  `simd (avx512, sde)` job runs it.
  The cascade's width tests and counters decide only which backend runs
  which elements, and so speed, never bits. A mutant that skips a backend
  or recomputes elements by the scalar function survives these tests by
  design.
- **The public functions** on the dispatched backend, for every length from 0
  to 17 and a long slice, and their length check.
- **The error-free product** (§2).
- **The determinism digest's `exp_slice`, `exp2_slice`, `expm1_slice`, `ln_slice` and `ln_1p_slice`
  sections** ([determinism.md](determinism.md)), with and without `simd`.

- **No lane operation out of line** (`scripts/check_lane_codegen.sh`, in the
  `simd (avx512, sde)` job): the release library's disassembly has no call
  from a non-test function to an AVX2 or AVX-512F helper, other than the
  store and load at `lanes::cold` and the scalar-only
  `ln::lanes::finish_ln_1p` prefix, which enter and leave the wrapper (§7).
  An out-of-line operation still returns the scalar bits, so only the code
  shows it.

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
evaluation on top: about `2^−16.9` of `exp`'s arguments, 81 of 1,048,576
(`7.72·10^-5`) of `ln`'s mixed positive-encoding/near-one test corpus and, for `ln_1p`, the `2^−8.6` to `2^−16.7` that stage H leaves to stage B
([exp.md](exp.md) §7, [ln.md](ln.md) §7, §9), plus the screened ones. `exp`'s
stage B runs on a chunk only when stage A leaves one of its lanes undecided,
about one argument in 2^7.3.

The cascade adds at most one detection check and one feature-enabled call per
backend. On aarch64 it has one backend, NEON, so the NEON figures below are
unaffected. On x86-64 it lets a slice shorter than the widest chunk, such as
a two-element batch on AVX2 or AVX-512F, run on SSE2's two lanes instead of
the scalar function. Measured on one i9-10920X, a two-element slice beats the
scalar loop for every function, and a one-element slice costs 2.1–2.8 ns
more than a scalar call
([native x86 measurements](../crates/reference/measurements/lanes-x86-i9-10920x-cold-paths/README.md)).

`crates/reference/src/bin/bench-batched.rs` times a loop of the scalar
function against the batched one, as the median over 31 rounds of the time per
element on 4,096 arguments:

```sh
cargo run --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-batched
```

Measured on one Apple M1 Pro (NEON, 2 lanes), `--release`, Rust 1.97.1, with
the 1-minute load average between 2.5 and 2.8 and no other benchmark or build
running; two consecutive runs agreed within 0.1 ns (2026-10-12):

| Function | Arguments | Scalar loop (ns) | Batched, NEON (ns) | Speed-up |
|---|---|---|---|---|
| `exp` | `[−30, 0]` | 3.94 | 2.25 | 1.75× |
| `exp` | `[−745, 709]` | 9.32 | 7.37 | 1.26× |
| `ln` | `[0.5, 2)` | 6.45 | 4.97 | 1.30× |
| `ln` | positive encodings | 6.47 | 4.96 | 1.30× |
| `ln_1p` | `e^d`, `d ∈ [−30, 0]` | 4.53 | 3.37 | 1.35× |
| `ln_1p` | `z²/4`, `z ∈ [−6, 6]` | 4.42 | 3.29 | 1.34× |
| `ln_1p` | `[−1, 2^60]`, log-uniform | 5.46 | 4.22 | 1.29× |

`exp` on its whole domain gains less: the arguments beyond `exp`'s screen
(`|x| ≥ 704`, 3.2% of these), among them every subnormal result, go to `exp`
itself, whose fallback takes its accurate path for the subnormal ones.
`ln_1p`'s scalar loop is now stage H, about 4.5 ns, so batching it gains less
than it did over the double-word path. On log-uniform arguments, the lanes
stage H screens out (`|x|` below `2^−46` or from `2^53`) take stage B or the
fallback, so they gain least.

`asin`, `asinh` and `atan2` on the same Apple M1 Pro, with their findings (a lane
kernel first slower than the scalar loop, the software square root's cost) and what
was not measured, are in
[measurements](../crates/reference/measurements/asin-asinh-atan2-m1pro/README.md).

SSE2, AVX2 and AVX-512F were timed natively on one Intel i9-10920X (Cascade
Lake), each backend alone and through the cascade, for every lane kernel and
workload ([measurements](../crates/reference/measurements/lanes-x86-i9-10920x-cold-paths/README.md)).
For the arguments above, the dispatched batch there takes 3.3 ns (`exp`
`[−30, 0)`), 3.1 ns (`ln` `[0.5, 2)`) and 3.2 ns (`ln_1p` `e^d`), against
6.0, 9.1 and 8.3 ns for the scalar loop
([after #162](../crates/reference/measurements/lanes-x86-i9-10920x-cold-paths/README.md)). Those figures describe that host only. Timing on a
CI runner is not evidence.

**Uncommon paths and lane masks.** Two rules keep a kernel's operations in
lanes, and the native x86 measurements are what found them (#162):

- **An uncommon vector path runs through `lanes::cold`.** That is an
  `#[inline(never)]` function that re-enters `Simd::vectorize`, so the path
  stays out of the common chunk's code but is compiled with the backend's
  features. A function outside that wrapper cannot inline an AVX2 or AVX-512F
  helper. `ln`'s and `ln_1p`'s fallbacks once made 200–300 helper calls per
  chunk that way and ran 2–3× slower than scalar, while SSE2, which is enabled
  for the whole x86-64 target, was unaffected. The hot side passes and
  receives vectors: passing the chunk's arrays kept them in memory and slowed
  `ln_1p`'s common path by about 10%. On AVX2 and AVX-512F, `ln_1p` handles scalar stage B and
  special values before entering the wrapper; only two or more unresolved
  lanes require vector re-entry. NEON and SSE2 already have baseline target
  features, so their scalar prefix remains inside the same cold wrapper.
  Scalar completion helpers borrow one mutable output array; they do not
  return successive array copies. This keeps the output buffer in place
  across stage B, special-value completion and the single unresolved lane.
- **A lane mask is computed in lanes.** That is either a comparison, as in
  `ln`'s screen, or `mask_from`, which delegates to the backend
  `mask_from_bits`: AVX-512F already represents its mask as bits and uses
  them directly; other backends test each lane's bit of a broadcast integer. Storing one word per lane and reloading them as a vector stalls
  store forwarding on every chunk.

Together these took `ln` `[0.5, 2)` from 7.2 to 3.1 ns per argument on the
i9-10920X, `ln` near 1 from 172 to 36 ns, `ln_1p` beyond `2^1020` from 185 to
27 ns, and `expm1` 4–10% faster.

A same-host run of the previous `ln` implementation (commit `e053de4`,
load 2.15) measured 29.81/29.76 ns for the two scalar workloads and
14.86/14.91 ns for their NEON batches. The reciprocal stage therefore
improves scalar throughput about 4.6× and batched throughput about 3.0×.

The exponential slice additions were measured on the same M1 Pro with the
same command and methodology (2026-10-12, Rust 1.97.1). Two consecutive runs,
with no concurrent build or benchmark, gave:

| Function | Arguments | Scalar loop (ns) | Batched, NEON (ns) | Speed-up |
|---|---|---|---|---|
| `exp2` | `[−30, 0]` | 5.05–5.15 | 3.20–3.21 | 1.57–1.61× |
| `exp2` | `[−1075, 1024]` | 9.29–9.32 | 7.28–7.41 | 1.25–1.28× |
| `expm1` | `[−30, 0]` | 7.33–7.51 | 4.45–4.48 | 1.65–1.67× |
| `expm1` | `[−1/32, 1/32]` | 11.13–11.28 | 6.14–6.20 | 1.81–1.82× |
| `expm1` | `[−37.4, 709]` | 8.20–8.21 | 5.15–5.17 | 1.59× |

Before extracting the shared lane evaluators, the same host measured `exp`
batches at 2.32/7.44 ns for its two ranges; afterwards, 2.34–2.35/7.51–7.58 ns.
Wide domains gain less because screened inputs still use scalar fallbacks.
The scalar accurate-path rates remain those measured in [exp2.md](exp2.md)
and [expm1.md](expm1.md); SIMD makes the same decisions per argument. On the
i9-10920X, `exp2` `[−30, 0)` and `expm1` `[−30, 0)` batch at 2.8 and 3.6 ns,
against 8.4 and 11.2 ns scalar
([measurements](../crates/reference/measurements/lanes-x86-i9-10920x-cold-paths/README.md)).

The shared logarithm fallback was measured on the same M1 Pro and toolchain
(2026-10-12), with other builds paused during timing. The benchmark includes
arguments close enough to one to reject `ln`'s first stage, and arguments
above `ln_1p`'s stage-B screen. Two runs of each version gave:

| Function | Arguments | Previous batch, `490a7cf` (ns) | Shared fallback batch (ns) |
|---|---|---|---|
| `ln` | `[0.5, 2)` | 5.02–5.06 | 5.03 |
| `ln` | positive encodings | 5.02–5.05 | 5.02–5.04 |
| `ln` | `1 ± 2^−47` | 51.98–52.27 | 43.41–43.77 |
| `ln_1p` | `[2^1020, MAX]` | 38.16–38.32 | 29.58–29.65 |
| `ln_1p` | `e^d`, `d ∈ [−30, 0]` | 3.40–3.42 | 3.39–3.40 |
| `ln_1p` | `z²/4`, `z ∈ [−6, 6]` | 3.31–3.33 | 3.30 |
| `ln_1p` | `[−1, 2^60]`, log-uniform | 4.43–4.45 | 4.29–4.30 |

The two fallback-heavy batches improve about 1.19× and 1.29×. Their new
scalar-loop timings are 49.29–49.42 ns and 33.72–33.74 ns, respectively.
Ordinary `ln` scalar timing also improves, from 6.52–6.58 ns to
6.01–6.08 ns, after extracting its fallback completion. The dispatch keeps
the decided mask through the common branch and computes the pending mask
only when needed; adding mask work to every batch measurably slowed the
common `ln_1p` workloads. These are local NEON measurements. On the
i9-10920X the dispatched batches take 36.5 ns (`ln` near 1) and 27.3 ns
(`ln_1p` beyond `2^1020`), against 86.9 and 96.8 ns scalar.

The seeded scalar pass-rate tests send 81 of 1,048,576 `ln` inputs past the
reciprocal stage (0.0077%). Exercising the double-word fallbacks directly,
`ln` rejects 1,502 of 1,048,576 decisions (0.1432%) and `ln_1p` rejects
761 of 550,857 (0.1381%). These latter rates describe the fallback itself,
not the fraction of public calls reaching Q128 after the earlier stages.
Lane decisions are identical to those scalar decisions.
