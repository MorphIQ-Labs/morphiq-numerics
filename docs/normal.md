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

A fast result is returned only when its computed error interval has identical
binary64 endpoint encodings. The accepted result is correctly rounded,
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
calculations must agree. `ln sqrt(2π)` is generated as a double word for the
density's first stage only; the accurate paths don't use it. The constant and threshold certificates check the
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

## The density's first stage

For `2^-33 <= abs(x) <= 37`, the density first tries a lean stage that
decides about 99.2% of arguments (measured over 12 million uniform arguments
on six ranges). It writes

```
φ(x) = exp(-x²/2 - ln sqrt(2π)),
```

forms `h + l = -x²/2` exactly (`two_prod`), subtracts the generated
`ln sqrt(2π)` double word with a TwoSum on the high words and one rounded
addition of the low words, and evaluates exp's stage A at the resulting
double-word argument `s + se` ([exp.md](exp.md) §5a). `|s| < 704` and
`|se| <= 2^-42`. The argument is within `2^-95` of `-x²/2 - ln sqrt(2π)`:
the low words' two roundings (`2^-97`, `2^-96`) and the constant's
certified `2^-105`. Stage A's result is then within
`23·2^-65 + 2^-92` of `φ(x)/2^k`, and the rounding test of
[exp.md](exp.md) §7 takes `E = 1.75·2^-61`, which covers that and the
test's own `2^-63`. A result it returns is `RN(φ(x))`
(`NormalDensityFirst.normal_density_first_ok`); every other argument
continues to the fast composition below, and the public model
(`NormalPublicModel.normal_regular64`) tries the stages in the code's
order.

Because both stages return only `RN(φ(x))` when they return, the first
stage changes no result. It removes the double-word exponential's stage B
and the double-word multiplication by `1/sqrt(2π)` from the common path.

## The CDF family's tail first stage

For `1/2 < abs(x) <= 36`, CDF, CCDF (through CDF at `-x`) and the centered
CDF first try a lean stage on the tail `q = Φ(-a)`, `a = abs(x)`, written as

```
q = exp(-a²/2) erfcx(a/sqrt(2)) / 2.
```

`exp(-a²/2)` comes from exp's stage A at the exact double word `-a²/2`
([exp.md](exp.md) §5a) instead of stage B. The fast scaled erfcx below is
multiplied in by one exact `two_prod` of the high words and binary64 cross
terms, without a double-word product or renormalizing additions, and the
`1/2` joins the power-of-two scale. The words `qh + ql` are within
`33·2^-64` of `q` relatively (`NormalTailFirst.normal_tail_first_parts_ok`):
stage A's `23·2^-65`, erfcx's `2^-66`, the cross terms' roundings and the
scaling. CDF for `x < 0` tests `qh + ql` directly. CDF for `x > 0` and the
centered CDF form `1 - q` and `±(1/2 - q)` with an exact Fast2Sum and one
rounded subtraction. Each test takes the guard `RN(qh·2^-58)`, and the
complements add `2^-100` to cover the test's own roundings near one. The
test's scale follows `qh`'s binade, so the first stage is limited to
`abs(x) <= 36`, where `q >= 2^-960`. A result it returns is the correctly
rounded target (`NormalTailFirst.normal_tail_first_ok`); between 96% and
99.6% of tail arguments are decided (12 million uniform arguments over three
ranges), and the rest continue to the fast composition below.

## The CDF family's central first stage

For `2^-33 <= abs(x) <= 1/2`, CDF, CCDF and the centered CDF first try a
lean stage on `C(x) = Φ(x) - 1/2`, written with the central series of the
fast composition below as

```
C(x) = φ(0)·x·(1 + E(x²)),   E(z) = c1·z + z²·(c2 + z·(c3 + z·T(z))),
```

where `T` is the fast composition's degree-8 tail polynomial. Only three
quantities are carried as double words: the exact square `zh + zl = x²`
(`two_prod`), `c1·x²` (`e1h` by an exact `two_prod` of `c1`'s high word and
`zh`, `e1l` gathering its error and the cross terms) and `φ(0)·x`
(`dh` exact by `two_prod`, `dl` its error plus the constant's low word
times `x`). The rest of `E` (`e2`, at most `0.0016`) is binary64: Gappa
certifies `|e1h + e1l + e2 - E(x²)| <= 2^-60` absolutely
(`formal/normal/center_first.g`). The product `dh·e1h` is exact
(`two_prod`), the remaining cross terms are summed in binary64, and two
Fast2Sums renormalize. The words `ch + cl` are within `3.2·2^-60` of `C(x)`
relatively (`NormalCenterFirst.normal_center_first_parts_ok`): the
certificate's `2^-60`, the roundings of the remainder and the dropped
`dl·(e1l + e2)` (about `1.9·2^-60`), and the series' own truncation.

The centered CDF tests `ch + cl` directly. CDF adds `1/2` with an exact
Fast2Sum (`abs(ch) <= 0.21`) and one rounded addition of the low words.
Both take the guard `RN(abs(ch)·2^-58)`. A result it returns is the
correctly rounded target (`NormalCenterFirst.normal_center_first_ok`);
about 99.1% of CDF and 95.5% of centered-CDF arguments are decided (16
million uniform arguments over four ranges), and the rest continue to the
fast composition below.

The NEON, SSE2, AVX2 and AVX-512 kernels evaluate the same central-stage
words and endpoint test. A homogeneous eligible chunk returns early only
when every lane is decided. Otherwise the existing composition and scalar
completion own the whole chunk. This keeps partial first-stage vectors out
of the fallback path and preserves the tiny-input dispatch. Lane tests
compare both words and every acceptance decision with the scalar stage
before checking public results.

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
