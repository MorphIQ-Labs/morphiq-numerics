# MPFR numerical fuzzing

This independent, unpublished workspace checks strong and fast elementary APIs,
the strong normal APIs and accelerated fast normal APIs against MPFR through
`rug`. Neither MPFR nor the
fuzzer is a dependency of the published crates. The root dependency license
policy stays permissive-only; the separate
oracle graph has exact package/version exceptions in
[`check_fuzz_licenses.sh`](../scripts/check_fuzz_licenses.sh).

## Contracts

`elementary` covers all 14 scalar elementary functions, `sincos` equivalence,
and all fourteen slice wrappers, including the paired sine/cosine output,
with scalar and `simd,std` builds. The oracle
compares exact binary64 bits for correctly rounded results, including signed
zero, subnormals and infinities. NaNs are checked by classification; slice and
`sincos` equivalence compare their exact bits as well.

| Functions | Oracle acceptance |
| --- | --- |
| `exp`, `exp2`, `ln`, `log2`, `sqrt`, `asin`, `asinh` | Correct rounding over their entire domains, including specified exceptional inputs |
| `expm1` | Correct rounding for `abs(x) < 2^-54`; otherwise `(1/2 + 2^-65)` ulp |
| `ln_1p` | Correct rounding for `abs(x) < 2^-54`; otherwise `(1/2 + 2^-70)` ulp |
| `log10` | `(1/2 + 2^-69)` ulp |
| `sin` | Correct rounding for `abs(x) <= 0x1.7137449123ef6p-26` and `2^-24 <= abs(x) <= 2 + 4675/8192`; otherwise `(1/2 + 2^-144)` ulp |
| `cos` | Correct rounding for `abs(x) <= 12867/8192`; otherwise `(1/2 + 2^-144)` ulp |
| `tan` | Correct rounding for `abs(x) <= 0x1.d12ed0af1a27ep-27` and `2^-25 <= abs(x) <= atan(2)`; otherwise `(1/2 + 2^-142)` ulp |
| `atan2` | Correct rounding for special values and tiny ratios below `2^-900`; otherwise `(1/2 + 2^-137)` ulp |

These are the contracts in [exp](../docs/exp.md), [exp2](../docs/exp2.md),
[expm1](../docs/expm1.md), [ln](../docs/ln.md), [log2/log10](../docs/log2.md),
[trig](../docs/sin_cos.md), [sqrt](../docs/sqrt.md), [asin](../docs/asin.md),
[asinh](../docs/asinh.md) and [atan2](../docs/atan2.md). The public oracle cannot
observe internal rounding-test decisions: outside the stated CR domains it
checks the published bound, including results returned by those tests. Existing
internal proof and decision checks remain responsible for that stronger path
invariant.

The separate `fast_elementary` target checks all three fast elementary scalars
and their slice wrappers against [fast.md](../docs/fast.md) and
[fast_ln.md](../docs/fast_ln.md):

| Function | Oracle acceptance |
| --- | --- |
| `fast::elementary::exp` | Relative error at most `2^-51` for `abs(x) < 704` |
| `fast::elementary::exp_coarse` | Relative error at most `2^-38` for `abs(x) < 704` |
| `fast::elementary::ln` | Absolute error at most `2^-53 * abs(ln(x)) + 2^-65` for finite positive `x`; `ln(1) = +0` exactly |

Both exponentials must equal the strong owner's bits outside the accelerated
domain, and return exactly one at either signed zero. Fast ln's special values
must equal the strong owner's bits. These comparisons include NaN payloads;
MPFR independently checks numerical results in addition to these API relations.
Random, double-word and linear-algebra APIs are outside these fuzz targets.

The separate `fast_normal` target checks all three fast normal scalars and
their slice wrappers against [fast.md](../docs/fast.md),
[fast_cdf.md](../docs/fast_cdf.md) and [fast_log_cdf.md](../docs/fast_log_cdf.md):

| Function | Independent MPFR acceptance on the accelerated domain |
| --- | --- |
| `fast::normal::erfcx` | Relative error at most `2^-51` for `-0.5 <= x < 16`, excluding `abs(x) < 2^-33` |
| `fast::normal::norm_cdf` | Absolute error at most `2^-49`, and also relative error at most `2^-48` for negative inputs, on `-22.5 <= x <= -2^-33` or `2^-33 <= x <= 8` |
| `fast::normal::log_norm_cdf` | Absolute error at most `2^-51 * abs(ln(Phi(x))) + 2^-48` on the same accelerated domain as CDF |

Accelerated outputs must be finite normal values with the specified sign and
range. Outside those domains the target requires exact strong-owner bits,
including signed zero and NaN payloads. **This fallback check establishes
delegation only; it does not independently validate the strong normal APIs'
full-domain numerical contracts.** Scalar/slice identity is checked everywhere.

The separate `strong_normal` target independently checks `normal::erfcx`,
`normal::norm_cdf` and `normal::log_norm_cdf` over all binary64 inputs and checks
their slice wrappers bit for bit. It imports no expected library outputs. For
finite, nonsaturating results, the acceptance bound is
`abs(actual - exact) <= abs(exact) * (2^-53 + r) + 2^-1075 + a`:

| Function and domain | `r` | `a` |
| --- | --- | --- |
| erfcx, `x < -1/2`, above overflow | `2^-122` | `0` |
| erfcx, `-1/2 <= x < 16` | `0` | `2^-123` |
| erfcx, `x >= 16` | `2^-223` | `0` |
| CDF, `abs(x) <= 1/2` | `2^-245` | `0` |
| CDF, `x < -1/2` | `2^-114` | `0` |
| CDF, `x > 1/2` | `2^-111` | `0` |
| log-CDF, `abs(x) <= 1/2` | `2^-228` | `0` |
| log-CDF, `abs(x) > 1/2` | `2^-111` | `0` |

These are the published per-domain public-result bounds in
[erfcx.md](../docs/erfcx.md) and [normal.md](../docs/normal.md). Every term is
added with directed MPFR rounding, including the half-minimum-subnormal term
that cannot be represented in binary64. This does not substitute a blanket
correct-rounding assertion for a bounded contract. Signs, ranges, NaN encodings,
exact zero-input identities, overflow, and saturation rounding are checked
separately. Finite erfcx results must remain strictly positive even at `f64::MAX`.
The separate `strong_density` target independently checks `normal::norm_pdf`,
`normal::norm_ccdf`, `normal::norm_cdf_centered` and `normal::log_norm_pdf` over
all binary64 inputs, with the three slice wrappers bit for bit (log-PDF has no
slice). The first three use the compound allowance above with `a = 0`:

| Function and domain | `r` |
| --- | --- |
| PDF, `23 <= abs(x) <= 38.6` | `2^-222` |
| PDF, elsewhere | `2^-236` |
| CCDF, `abs(x) <= 1/2` | `2^-245` |
| CCDF, `x > 1/2` | `2^-114` |
| CCDF, `x < -1/2` | `2^-111` |
| centered CDF, `abs(x) <= 1/2` | `2^-246` |
| centered CDF, `abs(x) > 1/2` | `2^-111` |

Underflow and saturation must round correctly, centered results keep the input's
sign, and NaN encodings and exact zero-input identities are checked separately.
Log-PDF ([log_norm_pdf.md](../docs/log_norm_pdf.md)) must be correctly rounded
for `abs(x) < 2^-27` and `abs(x) > 2^500`, and within `(1/2 + 2^-50)` ulp
elsewhere. Normal pairs and other public modules still require their own
independent fuzz coverage.
The retained `log-pdf-boundaries` packet contains the exact regime-limit and
overflow encodings of both signs; it is a coverage witness, not a known library
defect.

### Normal oracle across extreme tails

Strong and fast targets share the same independent reference module.
For moderate erfcx inputs it encloses `exp(x*x) * erfc(x)` with directed MPFR
operations. For `x >= 64`, that direct formula would eventually exceed MPFR's
exponent range. Instead, the oracle uses the mathematical signed remainder of
[DLMF 7.12.1](https://dlmf.nist.gov/7.12#i):

```text
erfcx(x) = J / (x sqrt(pi))
J = integral_0^infinity exp(-u) exp(-u²/(4x²)) du
S_n = sum_{k=0}^n (-1)^k (2k-1)!! / (2x²)^k
S_63 <= J <= S_64
```

Taylor's signed remainder integrated against `exp(-u)` establishes the two
inequalities. All recurrence operations, sums, pi, square root and division
round outwards. No runtime coefficient table or approximation is imported.
The 64-term work limit is fixed; if the resulting enclosure and up to 8192 bits
cannot decide the bound, the oracle fails explicitly. Overlap tests compare
this integral enclosure to 1024-bit direct MPFR evaluations from 64 through 256.

For negative log-CDF below -8, the oracle encloses
`-x²/2 + ln(erfcx(abs(x)/sqrt(2))/2)`. It never forms an underflowed probability;
the binary64 square is exact at every selected precision and fits MPFR even at
the largest finite input. Positive log-CDF uses `ln_1p(-Phi(-x))` with directed
rounding, retaining the tiny logarithm after the CDF rounds to one.

Conservative screens follow from the definitions independently of the library's
threshold bits: `erfcx(-a) > exp(a²) > 2^1024` at `a >= 32`; Mills' inequality
`Phi(-a) < exp(-a²/2)/(a sqrt(2pi)) < 2^-1100` at `a >= 40`. Since
`-ln(1-q) < 2q` for these tiny positive `q`, CDF and positive log-CDF saturation
are determined without exceeding MPFR's exponent range. Inputs near the actual
overflow and underflow boundaries still go through the independent enclosures.

On the fast accelerated domain, the erfcx reference multiplies directed MPFR enclosures of `exp(x*x)` and
`erfc(x)`; the binary64 square is exact at the oracle's precision. The CDF
reference encloses `abs(x)/sqrt(2)`, reverses the endpoints for decreasing
`erfc`, and halves exactly. Positive inputs use outward-rounded subtraction
from one. The log-CDF reference uses `ln` for nonpositive inputs and `ln_1p` of the negative tail
for positive inputs, with outward rounding. All intermediate ranges stay finite and normal
in MPFR on the accelerated domains. These are mathematical compositions of
black-box MPFR operations, independent of the library's tables and kernels.
The same 256-to-8192-bit refinement and directed error comparisons apply;
both CDF bounds must pass, and no unresolved comparison counts as success.

MPFR evaluates each exact input with rounding down and up, starting at 256 bits
and doubling through 8192. Both endpoints must round to the same binary64 value
before it is used as the correctly rounded reference. This avoids double
rounding at subnormal midpoints. If the tested bounded result differs, directed
MPFR arithmetic must establish its error against `(1/2 + 2^-k) * ulp(exact)`;
the small term is never rounded away in binary64. An interval spanning a binade
boundary is refined. ULP is clamped to `2^-1074` for subnormals. Unresolved
oracle comparisons fail explicitly at the precision limit.

For fast relative and mixed absolute bounds, directed MPFR arithmetic encloses
both the actual error and the allowed error as a function of the exact result.
The maximum possible error must be no greater than the minimum allowance to
pass; the minimum error must exceed the maximum allowance to fail. An ambiguous
comparison refines the enclosure. The absolute ln term is retained at full
precision, including near one; it is not converted to a relative or ULP budget.

The oracle tests plant wrong results, signed-zero errors and bound violations,
and check that a valid non-CR value inside the bound is accepted. The retained
`atan2-subnormal-midpoint` input exercises `atan(3*2^-1074 / 2)`: its result is
just below the midpoint, requiring more than 2000 bits to settle. This is an
oracle regression witness, not a known library defect. Fast negative controls
exercise both sides of the exact relative allowances, the additive ln floor,
uncertain interval comparisons, signed zero at ln(1), incorrect fallback bits
at ±704, and changed NaN payloads. Retained fast inputs cover the adjacent
encodings at ±704 and one; they are boundary witnesses, not known defects.

Fast normal negative controls reject tail-relative violations that satisfy the
absolute CDF budget, wrong signs/ranges, log-CDF budget violations and changed
fallback payloads. Valid non-CR results inside each bound are accepted. The
retained `cdf-lower-tail` input encodes `-22.5`, the accelerated CDF endpoint;
it is a contract-boundary witness, not a known library defect.

Strong normal negative controls reject premature overflow, lost subnormal
values, rounded-away positive log tails, incorrect saturation and changed NaN
payloads. Synthetic boundary tests preserve every term of the compound error
allowance and accept valid non-CR results. The retained `tail-boundaries` packet
contains exact binary64 inputs spanning finite log tails, overflow, and
underflow; it is a coverage witness, not a known library defect.

## Arithmetic target

`arithmetic` checks `eft`, `ulp` and `double_word` against exact MPFR values and
the contracts in [double-word.md](../docs/double-word.md) and
[ulp.md](../docs/ulp.md). At 4400 bits every sum and product it forms is exact,
and quotient bounds are checked by multiplying through.

- `two_sum`, `fast_two_sum` and `two_prod` are exact on their stated domains,
  with the correctly rounded head. Nothing is claimed outside them.
- Each `checked_` operation must admit exactly the operands its published
  hypotheses admit, repeat the unchecked result bit for bit, return a double
  word and meet the table's relative bound. The reason reported on rejection is
  covered by `crates/reference/tests/checked.rs`, not here.
- `exp_split` meets `16u²` on its domain, with its stated value and exponent
  ranges, and returns `None` outside it.
- The ULP utilities match the definitions from the binary64 encoding.

Its corpus format is up to sixteen records of four little-endian encodings. The
retained `product-underflow-edge` input is a product below `2^-969` that rounds
to it; it is a boundary witness, not a known library defect.

## Reductions target

`reductions` checks `reduce`, including `Moments2`, and `log_space` on slices of
up to 64 finite or special values. At 8600 bits the sums, products and squared
sums are exact, so the algebraic bounds are checked without division.

- [reduce.md](../docs/reduce.md): the `sum`, `sum2`, `dot` and `dot2` bounds on
  their stated domains (here with `S <= 2^1019`, and operands at most `2^510`
  for `dot2`); sum-of-squares identity with the dot products; exact `max_abs`;
  empty slices; and the bits of every NaN result.
- [moments.md](../docs/moments.md): each successful readout encloses the exact
  statistic; failed pushes and merges leave the receiver unchanged; merge leaves
  its operand unchanged. Which checked-arithmetic refusals occur is not judged.
- [log_space.md](../docs/log_space.md): special values and the `log_sum_exp` and
  `log_diff_exp` bounds against directed MPFR enclosures; the pair records'
  stated operations and refusals.
- [log_normalize.md](../docs/log_normalize.md): refusals leave the output
  untouched, and the returned radius covers every normalized component. A
  refusal for an unrepresentable component must be near the overflow threshold.

Byte 0 selects reductions, moments or log space; byte 1 selects how the words
form a slice (as given, clustered around the first, or nearly cancelling); byte
2 places the moment split. The retained `nan-payload-order` input reproduces a library defect this target
found: reductions returned different NaN bits across targets and call paths.
The retained `cancelling-log-sum` input has a log-sum
near zero; it is a coverage witness, not a known library defect.

## Structures target

`structures` checks `interval` and `linalg::tridiagonal`.

- [interval.md](../docs/interval.md): every successful operation contains the
  exact image (algebraic endpoints exactly, `ln`, `exp` and `sqrt` against
  directed 512-bit values); `Domain` only for forbidden arguments and `Range`
  only near overflow.
- [tridiagonal.md](../docs/tridiagonal.md), orders up to 12: the sign and
  unpivoted admission conditions; a positive, lower-bounding dominance margin;
  factor, solve, batched and obstacle results bit for bit with the documented
  recurrence evaluated in MPFR; admitted obstacle solves within `2 tau`; residual
  certificates against the exact residual; and the dominance solution-error
  bound against an 8000-bit solve. Whether a dominance or complementarity refusal
  was necessary is not judged.

Byte 0 selects intervals or systems. For a system, byte 1 holds the order and
whether the coefficients are shaped into a dominant or sign-patterned matrix.
The retained `near-overflow-intervals` input is a boundary witness, not a known
library defect.

## Streams and bivariate targets

`streams` checks `random` and `fast::random` over arbitrary words:
SplitMix64 and xoshiro256++ outputs and seeding against the specification in
wider integers; jumps commuting with a step and distributing over exclusive or
(the jump distances are checked in `crates/reference/tests/random.rs`); exact
uniforms; the strong normal pair bit for bit against the specification with
correctly rounded MPFR operations; and the fast pair within `2^-38` of it, with
its zero signs and slice identity ([random.md](../docs/random.md),
[fast_random.md](../docs/fast_random.md)). The retained `octant-extremes` packet
is a boundary witness, not a known library defect. `double-rounding` is an oracle
regression: a product rounded twice there disagreed with the library, which an
independent mpmath evaluation confirmed.

`bivariate` checks `bivariate_normal`: special values, symmetry, saturation,
evaluator and slice identity, the reported bound, and the absolute error against
Plackett's identity integrated from correlation -1 by tanh-sinh quadrature at 128
bits ([bivariate_normal.md](../docs/bivariate_normal.md) §2 and §6). The
reference is refined until successive levels agree to `2^-73`; that convergence
test is numerical evidence, not a proved quadrature error bound, and an
unresolved integral fails. The allowance is section 6's bound rounded up in the
fourth digit, as `absolute_error_bound` returns it. The retained
`high-correlation-peak` input comes from section 3 of that document.

## Run and replay

On Apple Silicon macOS or native x86-64 Linux, with the repository toolchain,
Python 3, a C/C++ compiler and make installed:

```sh
./scripts/install_fuzz.sh
./scripts/check_fuzz.sh 60
```

The installer uses `.cargo/fuzz-version` and `.cargo/fuzz-nightly-version`.
`fuzz/Cargo.lock` pins `rug`, its bundled GMP/MPFR provider, and libFuzzer. Cargo
checks and replay use `--locked`. cargo-fuzz 0.13.2 has no `--locked` option, so
its build runs offline after the locked checks, and the gate rejects any lockfile
change. AddressSanitizer and coverage instrumentation are enabled for fuzz runs.

Each run replays the versioned strong elementary inputs and fast inputs from
`fast.json`, `fast_ln.json` and `fast_log_cdf.json`, plus strong normal inputs
from `erfcx.json` and `normal.json`, then mutates each target for the
requested number of seconds **per target and feature mode** (twenty campaigns).
Target names after the duration run only those targets, and
`./scripts/check_fuzz.sh --list` prints them.
Expected fixture outputs are not imported. The seed encoder adds both signs of
every binary64 binade boundary and its adjacent encodings, NaN payloads,
infinities, subnormal edges, and strong slice lengths 0 through 16. Fast seeds
include lengths 0 through 65 with both all-regular and mixed packets, ±704 and
its neighbors, cancellation around one and the fast fixtures' reduction cases.
This reaches the fixed 16/32/64-length paths and remainders. The fixture sources
retain the provenance of worst-case and reduction-boundary inputs.
Fast normal seeds include all accelerated-domain endpoints and adjacent
encodings, both signs, far tails, and lengths 0 through 65 in regular and mixed
packets. Strong normal seeds add the documented overflow, underflow and
saturation boundaries with three neighbors on either side and lengths 0 through
65. Existing elementary and fast corpus meanings are unchanged.

The `elementary` corpus format is one selector byte modulo 14, followed by up to sixteen
pairs of little-endian `u64` input encodings. IDs follow the table's source order
in `Operation::ALL`: exp, exp2, expm1, ln, ln_1p, log2, log10, sin, cos, tan,
sqrt, asin, asinh, atan2. Unary functions ignore the second word; atan2 calls
`atan2(first, second)`. Incomplete trailing pairs are ignored.

`fast_elementary` has its own selector namespace: modulo 3 selects exp,
exp_coarse or ln, followed by up to 65 pairs in the same binary layout (the
second word is unused). Keeping targets separate preserves every strong corpus
input's meaning, including mutated selector bytes above 13. Replay requires an
explicit target; corpus and regression directories are separated by target.

`fast_normal` and `strong_normal` each use their own selector namespace: modulo 3 for erfcx, CDF and log-CDF, respectively, followed
by up to 65 pairs in that same format (the second word is unused).
`strong_density` uses modulo 4 for PDF, CCDF, centered CDF and log-PDF, in the
same format.

Generated seeds, evolving corpora, failure artifacts and logs live under
`target/fuzz/`. CI runs 60 seconds per target and mode in the existing required Linux and
macOS test jobs. The weekly/manual workflow runs 1800 seconds per target and mode on both
hosts, one job per target and host (an hour of mutation each, with a two-hour job
limit for preparation and replay). Artifacts are retained for 14 days, including on
failure. A passing
campaign is sampled evidence, not an exhaustive proof or a performance result.

Replay a failure without nightly instrumentation:

```sh
cargo run --release --locked --manifest-path fuzz/Cargo.toml --features simd \
  --bin replay -- fast_elementary target/fuzz/artifacts/fast_elementary/simd/crash-HASH
```

Minimize it with the pinned cargo-fuzz tool, diagnose whether it is an oracle
or library defect, fix the owning component, and commit the minimized binary
under `fuzz/regressions/TARGET/` with a named regression test and its explanation. The
gate replays every retained input in both feature modes. Never turn a discovered
violation into a weaker tolerance or a discarded input.

Oracle API documentation: [rug Float](https://docs.rs/rug/1.30.0/rug/struct.Float.html).
Fuzzer usage: [Rust Fuzz Book](https://rust-fuzz.github.io/book/cargo-fuzz.html).
No external numerical implementation source is used by this harness.

## Deterministic normal boundary sweeps

[`sweeps/normal.json`](sweeps/normal.json) declares 30 finite binary64 windows
for strong erfcx, CDF and log-CDF. They surround the documented overflow,
underflow and saturation thresholds, central/tail region joins, selected
binade boundaries, signed zeros and erfcx's largest positive input. These are
explicitly selected windows, not all internal rounding-test transitions or the
whole binary64 domain. Each row gives a stable name, operation, inclusive first
and last encodings, a smoke anchor, and the source of its boundary.

The enumerator visits every integer encoding between the endpoints exactly
once, in packets of up to 65 lanes. On the negative side, increasing encoding
means decreasing numerical value; both endpoints still belong to the window.
Windows have one sign, contain only finite values, and cannot overlap for the
same function. Zero and largest-finite windows are clipped to their finite sign
domain. Every other window spans 2048 encodings on each side of its anchor.
One invocation is limited to 1,048,576 inputs and rejects malformed windows.

The full plan contains **112,670 inputs per feature mode**, or **225,340 checks
per host** across scalar and `simd,std` builds. Every input uses the same
contract-aware MPFR oracle and scalar/slice bit comparison as `strong_normal`.
Correct rounding is required where established; bounded-result domains retain
their published bounds. The sweep does not inspect or infer internal path
coverage from sampled public results. Other functions and exhaustive f32
analogue coverage are outside this plan.

```sh
# NEW_DIRECTORY must not already exist; all attempts remain separate.
python3 scripts/check_normal_sweeps.py target/normal-sweeps/my-run
# PR smoke: at most five encodings per window, explicitly partial coverage.
python3 scripts/check_normal_sweeps.py target/normal-sweeps/my-smoke --profile smoke
```

The runner builds the unpublished `normal-sweep` binary with the pinned stable
toolchain and locked oracle dependencies; no nightly or sanitizer is needed for
deterministic enumeration. The weekly/manual `normal-sweeps.yml` workflow runs
the full plan on native Linux x86-64 and macOS ARM. Existing required PR test
jobs execute the smoke profile and runner controls on both hosts. Smoke success
does not establish a completed full-window campaign.

Each attempt retains its manifest, revision, working-tree status, manifest and
oracle-lock hashes, toolchain, host, feature modes, expected count, and exact
completed ranges in `coverage.json`. Build and per-window logs are retained
alongside it. A clean working tree identifies the recorded source revision;
dirty-tree runs are explicitly identified and are not clean-revision evidence.
The top-level status becomes `passed` only after both modes finish and the
reported count equals the declared count. A timeout or interruption leaves a
failed job and an incomplete/failed receipt; completed windows remain visible.

Oracle failures retain a `.packet` in the existing `strong_normal` format and
propagate failure. Completed counts exclude the entire failed window. Replay a
retained packet using its recorded feature mode:

```sh
cargo run --release --locked --manifest-path fuzz/Cargo.toml --no-default-features \
  --features simd --bin replay -- strong_normal target/normal-sweeps/my-run/simd/WINDOW.packet
```

Artifacts, including failures and partial coverage, are uploaded for 14 days.
Exhaustiveness applies only to completed declared windows at the recorded
source and settings; it is neither a whole-domain proof nor native performance
evidence.
