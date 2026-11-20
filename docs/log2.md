# `log2` and `log10`: radix-2 and radix-10 logarithms

`morphiq_numerics::elementary::{log2, log10}` (`crates/morphiq-numerics/src/log2/`)
follow this derivation. Both use [ln.md](ln.md)'s exact reduction and its
certified fast and accurate paths, then scale by `1/ln 2` or `1/ln 10`. Only
the scaling is new, and its error is certified here.

- `log2(x)` is `log2 x` rounded to nearest, ties to even, for every binary64
  `x`. `log2(2^n) = n` exactly.
- `log10(x)` is correctly rounded whenever its rounding test decides, and
  otherwise within `(1/2 + 2^−69)` ulp. `log10(10^n) = n` exactly for
  `0 ≤ n ≤ 22`.

## Sources

- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: Property 4,
  Table 7 and §5.2.
- **[ln]** [ln.md](ln.md): the reduction `x = 2^E·y`, `ln y = −ln R[i] + ln(1 + z)`,
  the fast and accurate paths, and the rounding test.

## 1. Specification

| Input | Result |
|---|---|
| NaN, `x < 0`, `−∞` | NaN |
| `±0` | `−∞` |
| `+∞` | `+∞` |
| `1` | `+0` |
| otherwise | §3–§5 |

`generators/log2_log10_reference.py` gives the reference fixture
`crates/reference/fixtures/log2_log10.json`.

## 2. Accuracy needed

- **`log2`:** [LM] Property 4. An approximation within mantissa distance `2^−109`
  rounds correctly, over the whole range. Relative error below `2^−110` suffices.
- **`log10`:** [LM] gives no worst cases, so §5 states the proved bound.

## 3. `log2`'s fast path

`log2 x = E + w`, with `w = (ln y)/ln 2` and `|w| ≤ 0.5002`.
1. `S = ln y` as a double-word: [ln] §4 steps 1–5, the table term plus
   `ln(1 + z)`. It is within `2^−64` of `ln y` relatively (*certified*:
   `formal/ln/fast_a.g` and `fast_b.g`, which cover `E = 0`).
2. `W = S.mul(C)`, with `C = 1/ln 2` as a double-word. `C`'s relative error is
   below `2^−110.1` (*generated*), and `mul`'s is below `5u²` [DW].
3. `Y = W` when `E = 0`, and otherwise `Y = E.add(W)`: `E` is exact, and
   `add`'s error is `3u²/(1 − 4u)`.

`Y` is within `2^−63` of `log2 x` (*certified*: `formal/log2/fast_log2.g`). For
`E ≠ 0` the certificate uses `|w/(E + w)| ≤ 1.0007`, enclosed in interval
arithmetic over [ln]'s reduced range at `|E| = 1`. The ratio only shrinks as
`|E|` grows.

[ln] §5's rounding test then decides, with `ε₁ = 2^−63`. An accepted strict
comparison places the error interval inside one rounding cell; no
midpoint-distance hypothesis is needed for this fast decision.

**Powers of two:** `x = 2^n` gives `y = 1`, `R[0] = 1` and `z = 0`, so `S = 0`,
and `Y = n` exactly on both paths.

## 4. `log2`'s accurate path

`ln y` in `Q128`, as [ln] §6 computes it without the `E·ln 2` term. It is within
`2^−123` relatively (*certified*: `formal/ln/accurate_sum_a.g` and `_b.g`).
1. Multiply by `1/ln 2` in `Q128`: the constant's error is below `2^−131.2`
   (*generated*), and the product is truncated.
2. Add `E`, which converts exactly, where `E ≠ 0`. The addition errs by at most
   `2^−126·max(|E|, |w|)`.

The total is within `2^−122` relatively (*certified*:
`formal/log2/accurate_log2.g`, proves `2^−122.9`), against `2^−110` needed, so
`log2` is correctly rounded.

## 5. `log10`

- **Fast:** [ln]'s full fast result, within `2^−64` of `ln x`, times `1/ln 10` as
  a double-word. `1/ln 10`'s relative error is below `2^−109.8` (*generated*),
  and `mul`'s below `5u²`. The result is within `2^−63` (*certified*:
  `formal/log2/fast_log10.g`).
- **Rounding test:** [ln] §5's. `log10 x` is irrational unless `x = 10^n`, an
  integer, so it is never a breakpoint.
- **Accurate:** [ln]'s accurate result, within `2^−123`, times `1/ln 10` in
  `Q128`. The result is within `2^−122` (*certified*:
  `formal/log2/accurate_log10.g`, proves `2^−122.9`).

**The bound.** When the test passes, the result is `RN(log10 x)`. Otherwise it
is within `(1/2 + 2^−69)` ulp. It's correctly rounded unless `log10 x` lies
within mantissa distance `2^−121` of a breakpoint, which no published search
excludes.

**Powers of ten:** for `x = 10^n`, `0 ≤ n ≤ 22`, `log10 x = n` is representable.
Both paths err by less than half an ulp of `n`, so both return `n` exactly.

## 6. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/radix_constants.py` | `1/ln 2` and `1/ln 10` as double-words and in `Q128`, with their errors (`src/log2/tables.rs`) |
| `formal/ln/LogRadixConstants.v` | generated binary64 and Q128 encodings, normalized significands and independent CoqInterval proofs of both reciprocal-log residuals |
| `formal/ln/LogRadixFast.v`, `LogRadixGrid.v`, `LogRadixScale.v` | executable fast-path operations, fixed-grid bounds excluding underflow in radix scaling, and the actual double-word multiplication error including zero products |
| `formal/ln/LogRadixFastBound.v`, `LogRadixReconstruct.v` | composed `2^-63` relative bounds for both fast values, including exponent cancellation for `log2` |
| `formal/ln/LogRadixDecision.v`, `LogRadixEntry.v` | successful fast decisions round the exact logarithm correctly; public screens, decisions and accurate fallbacks compose to each function's contract, with [LM]'s midpoint-distance premise explicit for `log2` |
| `formal/ln/LogRadixAccurate.v` | executable Q128 scaling and exponent reconstruction, with the shared `ln` accurate theorem discharging the input error bounds |
| `formal/ln/LogRadixRounding.v` | finite, single-round binary64 conversion of both accurate paths; `log2` correct rounding under [LM]'s explicit midpoint-distance hypothesis; exact representable results for either radix |
| `formal/ln/LogRadixUlp.v` | final `log10` error within `(1/2 + 2^-69)` ULP of the exact result, including binade crossings |
| `generators/radix_certificates.py` | writes the four certificates below; the ratio bound is enclosed with `mpmath.iv` |
| `formal/log2/fast_log2.g`, `accurate_log2.g` | `log2`'s paths: `2^−63` and `2^−122` |
| `formal/log2/fast_log10.g`, `accurate_log10.g` | `log10`'s paths: `2^−63` and `2^−122` |
| `generators/log2_log10_reference.py` | the fixture: [LM] Table 7 and its §5.2 siblings, exact powers, special values, random arguments, and 1,200 values to 192 bits per function |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

The accurate reconstruction now has a Coq transcription. `log2_acc_bound`
proves its unrounded result within `2^-122` relatively of `ln(x)/ln(2)` for
every finite positive binary64 input, including the zero intermediate at
`x = 1` and exact-power reductions. `log10_acc_bound` proves the same bound
against `ln(x)/ln(10)` for finite positive `x != 1`; the public entry screens
one before evaluating this path.

These proofs establish the constant residuals independently with CoqInterval,
using a common `2^-127` bound. Q128 multiplication then contributes at most
`5 * 2^-125` relative error after scaling an input with the shared logarithm's
`2^-123` bound. For `log2`, the reduced logarithm divided by `ln(2)` has magnitude
at most `0.51`; a nonzero integer exponent limits cancellation enough to keep
the final Q128 addition within `2^-122`. No tighter sampled constant estimate
is needed for this reconstruction proof.

The fast-path composition uses the executable shared `ln` evaluations and
independently checked double-word reciprocal residuals bounded by `2^-109`.
Their inputs and intermediate results lie on the binary grid `2^-623`, and
both words of either normalized reciprocal lie on `2^-109`. The nonzero
products therefore have magnitude at least `2^-732`, which discharges both
the exact-product and cross-product underflow conditions. The multiplication
proof covers zero logarithms explicitly as well as nonzero products.
`radix_scale_accuracy` combines the shared `2^-64` logarithm error with these
constants and multiplication to give `9 * 2^-67` relative error. For `log2`,
the reduced logarithm's magnitude is at most `0.51`; the integer exponent
therefore bounds cancellation, and the final addition stays within `2^-63`.
These proofs establish the fast bounds directly, without assuming the tighter
constant estimates used by the separately checked Gappa certificates.

The theorem names above enter the kernel axiom audit and source binding. The
extracted accurate paths are compared with the Rust Q128 sign, exponent and
significand, before binary64 rounding, on independent reference-fixture inputs,
all representable powers of two, table-boundary neighbors and exponent extremes.
`LogRadixRounding.v` connects those unrounded bounds to the actual
`Q128::to_f64` conversion. For positive finite `x != 1`, either exact radix
logarithm has magnitude between `2^-57` and `1600`; the approximation and its
rounded output are therefore finite and nonzero. `log2_accurate_correct`
establishes correct rounding with [LM] Property 4's `2^-109` mantissa-distance
hypothesis explicit in its signature. For `log10`, `log10_accurate_bounded`
establishes one rounding of a value within `2^-122` relatively of the exact
logarithm, without introducing a hard-case hypothesis. The representable-result
theorems establish exact return values for either radix without that hypothesis.
`LogRadixUlp.log10_accurate_ulp` translates the relative reconstruction bound
into the final `(1/2 + 2^-69)` ULP bound, where ULP is measured at the exact real
result. If the approximation crosses the upper edge of that result's binade,
it still rounds to the edge exactly; the proof therefore does not double the
rounding allowance when the spacing changes. Negative results follow by the
symmetry of round-to-nearest-even.

The extraction corpus compares the fast double-word components and decision
results, the Q128 intermediates and their final binary64 encodings, and both
public entries with Rust. It includes entry-only special-value inputs as well
as the finite positive reduction corpus. Separate forced-accurate-path tests compare final
results with the independent oracle fixture, including inputs the public entry
normally handles on the fast path. Those comparisons test correspondence and
sampled accuracy; they do not replace the real-number error proofs.
`LogRadixDecision.v` uses the radix logarithm's `2^-57` lower magnitude bound
to discharge the rounding test's guards. `LogRadixEntry.v` combines that
decision with the accurate fallback and special-value screens, preserves NaN
inputs, and establishes exact representable results without a midpoint-distance
premise. Its regular `log2` theorem keeps [LM]'s premise explicit; its regular
`log10` theorem gives the final ULP bound on either return path.

`elementary::log2_slice` and `log10_slice` preserve their scalar functions'
bits. With `simd`, `src/log2/lanes.rs` reuses the shared logarithm lane reduction
and polynomial. It scales the same double-word values by the same normalized
reciprocal pairs; `log2` adds the integer exponent only where it is nonzero.
Special inputs are replaced by `2` before vector evaluation and completed by
the scalar entry. Undecided lanes also use that entry. Every evaluated product
therefore meets the grid and magnitude conditions above; the backend's exact
FMA product error may replace Dekker only under the shared [lane contract](lanes.md).
Word-by-word and decision comparisons check this scalar/lane correspondence;
the real-number bounds remain the scalar theorems, with unchanged qualifications.

The binding `formal/log2/binding.sha256` covers this document, the constants,
the certificates and the source.

**Checked by:**
- `crates/reference/tests/log2_log10.rs`: 4,029 `log2` and 4,034 `log10` cases,
  bit for bit. A `log10` mismatch would be an argument inside §5's window. It's
  reported, not waived.
- `src/log2/tests.rs`:
  - every unrounded result within its bound, against the 192-bit values;
  - both accurate paths after binary64 conversion against the independent
    rounded fixture, including hard cases and exact powers;
  - each fast path against its accurate path on 2^20 arguments. Measured, both
    send `2^−9.4` of them to the accurate path, against the analytic `2^−9`.
- `src/log2/lanes/tests.rs`: both fast words and acceptance decisions, including
  accepted, rejected and screened lanes, on each available backend. The shared
  lane suite checks final results, backend cascades and slice remainders.
- `crates/reference/tests/log2_log10.rs` also checks both slice APIs against
  the independent fixtures and scalar bits, including short slices and offsets.
- The determinism digest's scalar and slice `log2` and `log10` sections on every target.
