# Scaled complementary error function

`normal::erfcx(x)` evaluates `F(x) = exp(x²) erfc(x)`;
`normal::erfcx_slice` evaluates the same function on a slice. The latter
preserves scalar result bits through NEON, SSE2, AVX2+FMA and AVX-512F.

No whole-domain correct-rounding or final error bound is claimed for this
implementation. The component certificates below cover table, reciprocal,
tail and reflection arithmetic, conditional on their stated hypotheses.
They do not establish an
end-to-end guarantee. Issue #34 tracks the remaining assurance work.

## Definition and special values

For real x, substituting `t = x + u` in the defining erfc integral gives

```
F(x) = (2 / sqrt(pi)) integral_0^infinity exp(-u² - 2xu) du.
F'(x) = 2x F(x) - 2 / sqrt(pi).
F(-x) = 2 exp(x²) - F(x).
```

The integral is positive and strictly decreasing. Finite positive inputs
have positive results, including when the rounded result is subnormal.
NaNs retain their encodings, `F(+infinity) = +0`, `F(-infinity) = +infinity`,
and both signed zeros give one.

The boundary encodings used by the implementation are:

| Boundary | Encoding |
|---|---|
| Greatest input overflowing to positive infinity | `c03aa0f4d2e063cf` |
| Least negative input in the interval rounding to one | `bc9c5bf891b4ef69` |
| Greatest positive input rounding to one | `3c8c5bf891b4ef6b` |
| Least positive input with a subnormal result | `7fc20dd750429b6e` |

The adjacent finite input above the overflow boundary rounds to
`1.7976931348622484e308`; it does **not** round to `f64::MAX`.
The fixture generator checks each boundary and three neighbors on each side
at 600 and 1000 bits. High-precision dyadics are rounded once, in integer
arithmetic, on the binary64 grid; converting first to a 53-bit normal number
would permit double rounding at underflow.

## Scalar kernels

* **Table (`-1/2 <= x < 16`).** There are 177 intervals: centers at `k/32`
  below one, then 32 intervals per binade up to 16. Reduction gives an exact
  residual `h = x-c`. Degree-nine polynomials have three double-word
  coefficients followed by seven binary64 coefficients. An 18-bit split of
  h and truncated 35-bit and 17-bit leading coefficients make the principal
  products exact without FMA. Compensated additions assemble the result.
  The table occupies 18,408 bytes.
* **Middle positive tail (`16 <= x < 512`).** A corrected reciprocal and its
  double-word square feed `C y (1-t/2+t²P(t))`, where `C = 1/sqrt(pi)`,
  `y = 1/x`, and `t = y²`. Both words of t enter the t² correction.
* **Large positive tail (`x >= 512`).** A double-word quotient `C/x` is
  corrected by `-t/2 + 3t²/4 - 15t³/8`. Above `1e270`, x is scaled by
  `2^-600` before forming the quotient. The correction's squared reciprocal
  rounds to zero throughout this scaled domain; computing it is unnecessary.
* **Negative reflection (`x < -1/2`).** The square is exact as `two_prod(x,x)`.
  Its low word joins the reduction of the shared 512-entry exponential
  stage B. The stage's result is normalized before the erfcx rounding test.
  The reflected positive value is subtracted before exponent scaling. Above
  exponent 104 that subtraction is omitted, subject to the reflection bound.

The current fast-path tests use a provisional relative guard of `2^-66`.
A rejection evaluates the Q256 path. The arithmetic certificates fit within
this guard, but applying them to the binary64 entry points still requires
discharging their hypotheses. The guard is not an end-to-end error proof.

For a subnormal output, the leading candidate is scaled first. It is then
mapped back exactly to the unscaled domain, where the binary64 subnormal
spacing is `2^-474`, since the scale is `2^-600`. The residual plus its guard
must lie strictly within half that spacing. If the residual points beyond
the initial candidate's half-gap, its adjacent neighbor is checked first;
the interval test still decides acceptance. A test on the normal result
followed by subnormal scaling would be insufficient.

## Accurate arithmetic and error units

Q256 evaluation uses the ODE coefficient recurrence at table centers, the
alternating asymptotic series in the positive tail, and a Q256 exponential
and reflection for negative inputs. Constants are generated independently
at 600 and 1000 bits and must agree after rounding to 256 bits.

A relative approximation bound is not an ulp bound. For a positive normal
value z, `z / ulp(z)` is between `2^52` and `2^53`; therefore relative error
epsilon corresponds to as much as `2^53 epsilon` ulp before final rounding.
The final rounding and binade/subnormal boundaries must also be accounted
for. No accuracy claim in this document is inferred from sampled errors.

## Arithmetic certificates and their hypotheses

The certificates in `formal/erfcx/` establish the following conditional
statements. Their Coq translations check the algebraic rewriting hints as
lemmas; an unchecked algebraic identity is not accepted as a proof.

| Component | Certified bound | Assumptions still needed at the entry |
|---|---|---|
| `T*.g` | Relative table evaluation error `2^-67` against the polynomial | Exact reduction, split products, coefficient differences and Fast2Sum calls |
| `reciprocal.g` | Relative error `2^-98` for corrected `1/x`, `16 <= x <= 512` | Discharged by `ErfcxReciprocal.reciprocal_ieee` |
| `middle_square*.g` | Absolute error `2^-102` against `1/x²` | Discharged by `ErfcxSquare.reciprocal_square_ieee` |
| `middle_polynomial.g`, `middle_mvt.g` | Evaluation error `0x1.5p-68`; sensitivity error `2^-101` | Exact EFTs and halvings; bounds on the square's words |
| `dw_product.g` | Relative multiplication error `2^-100` | Exact TwoProd/Fast2Sum, bounded low words, normal or exact-zero roundings |
| `middle_composition.g` | Relative error `2^-67` | The preceding components and approximation bounds below |
| `tail_quotient.g` | Relative error `2^-101` against the stored constant divided by x | Exact EFTs and commutation of quotient/residual roundings with binade scaling |
| `tail_square.g`, `tail_polynomial.g`, `tail_composition.g` | Relative reconstructed tail error `2^-67` | Normalized quotient model, first-omitted-term bound, and the stated relative/absolute rounding bounds |
| `tail_scaled.g` | Relative error `2^-99` when omitting the correction above `1e270` | Quotient theorem and `1/(2x²) < 2^-1794` |
| `reflection_reduction.g` | Absolute reduction error `2^-92` | Integer index, exact differences and shifter, `s < 710`, `abs(se) <= 2^-44` |
| `reflection_stage.g` | Absolute exponential-stage error `0x1.a2p-71` before scaling | Adapted reduction plus the shared polynomial and table hypotheses |
| `reflection_composition.g` | Relative reflected error `2^-67` | Table/exponential bounds, exact EFTs and power-of-two scaling |
| `reflection_omitted.g` | Relative error `2^-69` after omitting the positive term | Exponential bound, `0 <= erfcx(-x) <= 1`, exponent greater than 104 |

For the middle tail, the generated polynomial approximates the finite
asymptotic correction with relative error below `2^-59`. Its magnitude is
at most `3/4`: the finite alternating series has decreasing terms because
each successive magnitude ratio is at most `63/512 < 1`. Multiplication by
`t² <= 2^-16`, together with the first-omitted-term bound `PREM < 2^-125`
for the correction polynomial, gives absolute error below `2^-74` for
`1-t/2+t²P(t)`. The generated double-word `1/sqrt(pi)` has relative error
below `2^-110`. Generator replay checks these three budgets using exact
decimal rationals.

For the large tail, the first omitted term after the cubic is
`105 t^4 / 16`, bounded by `7 * 2^-72` when `t <= 2^-18`. The squared
reciprocal model permits a half-subnormal absolute rounding error. The
reconstruction also permits absolute rounding errors divided by the leading
quotient, bounded by `2^-170`; this covers gradual underflow rather than
assuming every tail operation is normal.

The reflection reduction appends `se` after computing the shared stage's
residual. Its additional rounding changes the certified reduction budget
from `2^-93` to `2^-92`; the shared evaluation's `0x1.a2p-71` budget still
holds. Also, erfcx permits squares up to 710, while the existing exp entry
proof covers arguments below 704. Its entry proof therefore cannot simply
be reused unchanged. When the positive reflection term is omitted, the
simple uniform bound on that term relative to the exponential is `2^-105`;
the former `2^-110` comment was too strong near exponent 105.

The reciprocal and square entry theorems start from a finite binary64
input in `[16, 512]`. They prove that every intermediate is finite, that
TwoProd and the Sterbenz subtraction are exact, and that scaling the high
reciprocal by two is exact. The composed theorem bounds the actual two-word
square against `1/x²` by `2^-102`, including the low word. Both transcriptions
are extracted and cross-checked against the Rust operations on exponent
boundaries, adjacent values and reproducible random inputs.

The remaining components do not yet prove their binary64 entry hypotheses, the
Q256 remainder and arithmetic error, the special-value thresholds or the
public rounding tests. Source binding identifies the implementation being
analyzed; it does not discharge a missing mathematical hypothesis.

## SIMD operation order

Each region has a lane transcription of its scalar floating-point sequence.
Homogeneous chunks return directly from their region kernel. Mixed chunks
mask inactive lanes to benign inputs before table indexing or division;
regions with one active lane use the scalar function. Two-lane mixed chunks
use scalar evaluation, avoiding two partially occupied vector evaluations.
Rejected lanes use Q256. A final partial chunk follows the existing backend
cascade down to the scalar function.

Only error terms in `two_prod` use hardware FMA. In the table region all
products follow the scalar multiply/add sequence. In the tail and reflection
regions, the operands of `two_prod` satisfy the shared exact-product domain;
scaled reciprocals keep large inputs away from Dekker splitter overflow.

## Reproducible artifacts

* `generators/erfcx/tables.sollya`: Sollya 8.0 `fpminimax` and `supnorm`,
  400-bit working precision. All coefficients originate here.
* `generators/erfcx_constants.py`: fast and Q256 table replay.
* `generators/erfcx_reference.py`: independent mpmath witnesses, including
  binade edges, interval boundaries, thresholds, and both tails.
* `formal/erfcx/T*.g`: 177 Gappa table-evaluation certificates. They prove
  relative evaluation error at most `2^-67` against each polynomial, given
  the stated shifter, exact-product and error-free-addition hypotheses.
* `formal/erfcx/[a-z]*.g`: 16 arithmetic component certificates for the
  reciprocal, tail and reflection paths. Four are generated by
  `generators/erfcx/tail_certificates.py` from the current erfcx constants
  and shared exponential certificate; the others contain exact mathematical
  constants and stated error budgets.
* `scripts/check_erfcx_certificates.sh`: Sollya replay and component checks.
* `bench-erfcx`: scalar throughput, SIMD throughput and scalar dependency
  latency, 31 alternating rounds, all samples emitted as CSV. No allocation
  occurs inside an evaluated kernel or timed repetition.

## Local performance evidence

Apple M1 Pro, macOS 27.0.1, Rust 1.97.1, release profile with
`codegen-units=1`, `simd,std`. Two runs of 31 alternating rounds gave these
median ranges, in nanoseconds per argument:

| Inputs | Scalar throughput | NEON throughput | Scalar dependency latency |
|---|---:|---:|---:|
| Table region | 9.69–9.77 | 5.61–5.62 | 28.42–28.63 |
| `[0,6)` | 10.96–11.03 | 6.38–6.39 | 30.69–30.77 |
| `[16,512)` | 15.09–15.57 | 5.67–5.87 | 39.73–40.54 |
| `[512,4608)` | 8.52–8.65 | 3.57–3.68 | 28.50–29.06 |
| `[-26.6,-0.5)` | 15.95–16.45 | 14.34–14.69 | 39.78–40.78 |
| Subnormal outputs | 13.96–14.31 | 5.61–5.81 | 32.49–33.22 |
| Interleaved regions | 12.42–12.84 | 12.67–13.12 | 34.57–35.16 |

The shared host was not idle: one-minute load averages were 3.83 and 5.13
at the run boundaries. This task's proof and certificate processes were
paused during timing; unrelated host activity, frequency and power settings
were not controlled. These are preliminary same-host observations and
establish no native x86 performance claim. Mixed-region two-lane dispatch
adds about 2% here; homogeneous regions benefit from vector evaluation.
[Raw rounds, process timing and source hashes](../crates/reference/measurements/erfcx-m1pro/)
retain every sample and the environment record.

With the current guard, separately instrumented uniform samples rejected
196/1,048,576 table inputs, 199/1,048,576 middle-tail inputs,
182/1,048,576 large-tail inputs in `[512,4608)`, and 177/1,048,576 negative
inputs. These rates exclude screened inputs and are workload-specific.

## Mathematical sources and provenance

[DLMF §7.7](https://dlmf.nist.gov/7.7), particularly equation 7.7.6,
provides Gaussian integral representations. The integral and ODE above
follow by substitution and differentiation.
[DLMF §7.12(i)](https://dlmf.nist.gov/7.12.i) supplies the erfc asymptotic
series and the first-omitted-term remainder bound for positive real inputs.
Only mathematical identities are used.

The algorithms and generators originate in this repository's
`research/erfcx` work at `be3a40d`. Its provenance record identifies the
MIT-licensed CORE-MATH erfc source consulted for ideas; no implementation or
coefficients from it were copied. The current adaptation consults that
research and this repository's kernels, plus the DLMF mathematical pages.
MPFR is used externally as a test oracle and is not a library dependency.
