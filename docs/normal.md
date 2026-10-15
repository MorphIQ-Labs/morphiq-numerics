# Standard-normal density and distribution

`normal` exports five scalar functions and their matching `_slice` functions:

| Function | Exact real target |
|---|---|
| `norm_pdf(x)` | `φ(x) = exp(-x²/2) / sqrt(2π)` |
| `norm_cdf(x)` | `Φ(x) = 1/2 + integral_0^x φ(t) dt` |
| `norm_ccdf(x)` | `Φ(-x)` |
| `norm_cdf_centered(x)` | `integral_0^x φ(t) dt` |
| `log_norm_cdf(x)` | `ln(Φ(x))` |

The centered function retains small differences from one half. The CCDF
retains small upper-tail probabilities. Log-CDF retains negative-tail
information after the probability itself would underflow, and small negative
logarithms after the CDF itself would round to one.

The probability identities follow by substituting `t=x/sqrt(2)` in the
[error-function definitions, DLMF §7.2](https://dlmf.nist.gov/7.2).

## Numerical contract

A fast result is returned only when its computed error bound fits one
binary64 rounding cell. Ordinary compositions compare the rounded interval
endpoints; the negative far tail tests the distance to the nearer midpoint.
The accepted result is correctly rounded,
nearest with ties to even. Otherwise the original binary64 argument enters
an integer-significand Q256 composition. No whole-domain correct-rounding
claim is made: there is no established worst-case separation result for these
compositions in this repository.

For a finite input whose result does not overflow, the returned value
has the form `f(x)*(1+d)+a`, with the uniform bounds
`abs(d) <= 2^-53 + 2^-111` and `abs(a) <= 2^-1075`.
The absolute term includes gradual underflow. Tighter fallback bounds are:

| Composition | Relative error before final rounding | Bound on `abs(d)` after rounding |
|---|---|---|
| PDF, regular Q256 path | `2^-237` | `2^-53 + 2^-236` |
| Centered CDF, `abs(x) <= 1/2` | `2^-247` | `2^-53 + 2^-246` |
| CDF, `abs(x) <= 1/2` | `2^-246` | `2^-53 + 2^-245` |
| Negative CDF tail, or reflected CCDF tail | `2^-115` | `2^-53 + 2^-114` |
| Outer CDF and centered CDF complements | `2^-112` | `2^-53 + 2^-111` |
| Log-CDF, `abs(x) <= 1/2` | `2^-229` | `2^-53 + 2^-228` |
| Positive and negative outer log-CDF | `2^-112` | `2^-53 + 2^-111` |

`NormalPublicEntry.normal_public_contract` and
`normal_ccdf_public_contract` compose the actual scalar dispatch, fast
acceptance, Q256 fallback, saturation and nonfinite cases.

Every row has the additional absolute term `abs(a) <= 2^-1075`. The far-tail
Q256 composition has the tighter pre-rounding bound `2^-222` for
`23 <= abs(x) <= 38.6`. Tiny PDF inputs and the saturation screens have
separate rounding proofs.

NaN encodings are returned unchanged. Both signed zeros give the same PDF,
CDF and CCDF values; centered CDF preserves the zero sign, and log-CDF gives
correctly rounded `-ln(2)`.

| Input | PDF | CDF | CCDF | Centered CDF | Log-CDF |
|---|---|---|---|---|---|
| `-infinity` | `+0` | `+0` | `1` | `-1/2` | `-infinity` |
| `+infinity` | `+0` | `1` | `+0` | `+1/2` | `-0` |

Underflowed centered results retain the input sign; underflowed log-CDF
results are negative zero. Slice functions require equal input and output
lengths, accept empty slices, and return exactly the scalar bits.

## Generated constants and boundaries

`generators/normal_constants.py` generates the double-word and Q256 constants,
the degree-12 fast central coefficients, degree-40 accurate central
coefficients and saturation encodings. Independent 600- and 1000-bit
calculations must agree. The constant and threshold certificates check the
encoded dyadics against their mathematical definitions.

| Least nonnegative input reaching the screen | Encoding |
|---|---|
| PDF rounds to zero | `40434a429ac2a6bc` |
| Negative CDF tail rounds to zero; positive log-CDF rounds to `-0` | `40433e21dc3f3bd8` |
| CDF rounds to one | `402095b059d67c4d` |
| Centered CDF rounds to one half | `4020bfafe7a91e68` |
| Magnitude at which negative log-CDF overflows | `5ff6a09e667f3bcd` |

The thresholds follow from half-ulp midpoint equations, with adjacent-input
checks and monotonicity. PDF uses `φ(x)=2^-1075`; CDF-to-one uses
`Φ(-x)=2^-54`; centered-to-half uses `Φ(-x)=2^-55`. The logarithmic underflow
screen separately bounds `-ln(1-q)` at the tail-zero neighbors. Negative
log-CDF overflow includes its logarithmic correction rather than deciding
from a rounded binary64 square.

## Fast compositions

For `abs(x) <= 37`, the Gaussian factor retains both words of `-x²/2`,
evaluates the shared double-word exponential, and carries its binary scale
separately. Density multiplies the generated `1/sqrt(2π)` double word before
scaling. For `abs(x) < 2^-33`, the density rounds directly to its generated
high word.

On `abs(x) <= 1/2`, the centered integral is

```
φ(0) x sum_n>=0 (-x²/2)^n / (n! (2n+1)).
```

This is the [erf power series, DLMF 7.6.1](https://dlmf.nist.gov/7.6.E1),
with the same change of variable. The fast degree-12 polynomial uses double-word coefficients and products in
the low degrees and binary64 arithmetic in the small high-degree tail.
Below `2^-33` it uses the linear term. Non-PDF inputs below `2^-450` enter
Q256 so the double-word cross products stay inside their proved domain.
CDF adds one half in double-word arithmetic. Central log-CDF evaluates
`ln(h) + l/h`, including the division rounding and logarithmic remainder.

For positive `a > 1/2`, the tail is

```
q = Φ(-a) = exp(-a²/2) erfcx(a/sqrt(2)) / 2.
```

Argument reduction retains the low word of `a/sqrt(2)`. With
`F(z)=erfcx(z)`, its correction uses
`F'(z)=2z F(z)-2/sqrt(π)` and a bounded second-order remainder.
The derivative follows from the product rule and the
[erf derivative, DLMF 7.10.1](https://dlmf.nist.gov/7.10.E1). The final
scaling proof includes underflow of the trailing word. CDF and centered CDF
form their complements in double-word arithmetic.

Negative log-CDF uses `-a²/2 + ln(F(a/sqrt(2))) - ln(2)` directly.
Positive log-CDF uses the existing `ln_1p` stage on `-q.hi`, corrected by
`-q.lo/(1-q.hi)`. When `q.hi < 2^-54`, it instead evaluates
`-q.hi - q.lo - q.hi²/2`; its proof includes underflow of the square.

The ordinary guard is `RN(abs(high)*2^-64)`; the log-CDF guard is
`RN(abs(high)*2^-62)`. The proofs account for guard rounding, both rounded
low-word endpoints and the final additions. `NormalFastDispatch.v` joins the
actual branch comparisons to the component acceptance theorems and the
common Gaussian targets.

### Negative far tail

For `x < -37`, write `a = -x` and `u = 1/a²`. The normalized Mills integral
`J` from the positive erfcx derivation gives

```text
ln Φ(-a) = -a²/2 - ln(a) - ln(2π)/2 + ln J(2u).
```

`NormalLogMillsIdentity.v` proves this identity. For `37 < a < 2^45`,
the square is exact in double-word arithmetic. The existing double-word
logarithm supplies `ln(a)`, and a degree-eight polynomial supplies `-ln J(2u)`.
Its coefficients follow by equating coefficients in `S' = (ln S)' S`, where
`S(u) = sum (-1)^n (2n-1)!! u^n` is the Mills asymptotic series.
`generators/normal_constants.py` derives them with exact rational arithmetic;
`generators/normal_log_tail.py` emits their proof encodings and evaluation
certificate. No external approximation coefficients are used.

The positive-real [erfc asymptotic remainder, DLMF 7.12.1](https://dlmf.nist.gov/7.12.i),
is bounded by the first omitted term. `NormalLogTailApprox.v` instantiates
the existing improper-integral remainder theorem and bounds the logarithmic
remainder. Sollya independently certifies the logarithmic polynomial fit.
Gappa includes reciprocal rounding, the squared reciprocal, rounded
coefficients, and every Horner multiplication and addition.
`NormalLogTailPolynomial.v` connects that certificate to the binary64
operations: the correction's absolute error is at most `2^-60`.
`NormalLogTailModerate.v` composes the logarithm, constant, correction and
exact square, proving relative error at most `2^-67` before the rounding test.

For `2^45 <= a < LOG_OVERFLOW`, first form `r = a * 2^-480` exactly, then
the exact double-word product `r * (-r/2)`. The logarithmic correction has
magnitude at most 1028, already proved in `NormalLogOverflow.v`; omitting it
in this scaled candidate remains within relative error `2^-67`.
`NormalLogTailSquare.v` proves the product's error-free-transform domain,
including its smallest scaled operands. `NormalLogTailHuge.v` and
`NormalLogTailScale.v` prove that the accepted high word can be multiplied
by `2^480` twice, exactly, without overflow or double rounding.

Both branches use the existing nearest-midpoint test with guard `2^-66`.
An undecided input still enters the original Q256 composition. PDF,
negative CDF, positive CCDF and positive log-CDF retain finite unsaturated bands beyond
37; those bands currently use Q256. Centered CDF and the positive CDF are
already saturated there.

## Accurate compositions

Q256 evaluates the same identities from the original input. The central
integral uses generated degree-40 coefficients. Extended erfcx lookup
repairs a predecessor-cell crossing caused by a rounded lookup argument and
caps the table lookup immediately below 16; larger arguments use the proved
asymptotic kernel.

The normalized logarithm uses the atanh series
([DLMF 4.6.4](https://dlmf.nist.gov/4.6.E4)) with at most 100 terms.
The log-complement series ([DLMF 4.6.1](https://dlmf.nist.gov/4.6.E1))
uses at most 299 terms. Their proofs include the
actual early stopping conditions, generated reciprocals, accumulated
rounding and final conversion to binary64. Large negative log-CDF uses the
integer exponent of Q256, avoiding an overflowing binary64 square.

## SIMD and validation

The `simd` feature evaluates the same operation sequence per lane through
NEON, SSE2, AVX2+FMA and AVX-512F. Hardware FMA is restricted to the existing
proved error-free product. Saturated homogeneous vectors skip polynomial
work. Inactive lanes are replaced by safe arguments; rejected or inactive
lanes use the scalar path. Short or mixed two-lane batches can use scalar
evaluation when vector setup would not amortize.

Negative far-tail lanes use their own mask and both tail branches above.
A mixed batch keeps the ordinary lanes on their vector kernel; only rejected
far-tail lanes enter Q256. Every backend uses the scalar sequence, including
the reciprocal and the two exact scaling multiplications.

`generators/normal_reference.py` produces independent mpmath witnesses,
including threshold neighbors, hard rounding cases, subnormals, signed zeros
and payload NaNs. Tests compare result bits and both intermediate SIMD
words. Extracted Coq models compare reduction words, Q256 significands,
guards, decisions and entry-point outputs with Rust. Public scalar and slice
results also enter the cross-target determinism digest.

The ignored `normal_local_performance` benchmark measures scalar and SIMD
paths on the same host and reports fallback counts for central, ordinary,
tail, underflow, overflow and mixed workloads. Select a workload with
`MORPHIQ_NORMAL_BENCH_WORKLOAD` and a length from 1 to 1024 with
`MORPHIQ_NORMAL_BENCH_LENGTH`. The dependent scalar chain reports serialized
latency including lookup/index overhead, alongside an identity-chain overhead
measurement. The chain's data-dependent inputs differ from the uniform
throughput corpus, whose accurate-path count is reported separately.
The kernels allocate no memory: the library does not import `alloc`, and
benchmark buffers are allocated before timing. Timings are evidence for that
host and workload, never CI speed assertions.

Native Apple M1 Pro measurements, raw repetitions, source hashes and
reproduction commands are in
[`measurements/normal-m1pro`](../crates/reference/measurements/normal-m1pro/README.md).
The public scalar wrappers and their shared dispatch helpers expose their
fixed operation to consumer optimization with `#[inline]`; the
[separate consumer comparison](../crates/reference/measurements/normal-m1pro/consumer-inlining/README.md)
records the effect across the crate boundary.
