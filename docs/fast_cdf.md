# Bounded normal CDF

`fast::normal::norm_cdf(x)` approximates `Φ(x) = erfc(-x/√2)/2`, the
standard-normal distribution function, for the exact binary64 input.
`norm_cdf_slice(x, out)` returns the same bits elementwise through the
NEON/SSE2/AVX2/AVX-512 cascade when SIMD is enabled. The strong
`normal::norm_cdf` and every other existing API are unchanged.

## Numerical decision and consumer purpose

On the accelerated domain `2^-33 <= abs(x) <= 8`, writing `Y` for the returned
value and `u = 2^-53`,

```
abs(Y - Φ(x)) <= 2^-49 = 16u,      and for x < 0 also
abs(Y - Φ(x)) <= 2^-48 * Φ(x) = 32u * Φ(x),
```

including every rounding. `Y` is finite and normal, in `[2^-58, 1]`. Outside
the domain the strong owner supplies its result and special-value semantics:
`Φ(±0) = 1/2` correctly rounded, the tails beyond eight, infinities and NaN
payloads. Correct rounding and faithful rounding are not the fast contract; the
fast and strong results may differ.

The consumer is Risk's default pricing tier: Black–Scholes `N(d1)`, `N(d2)`
and their compositions, scalar and in batches. The absolute bound is the
existing contract, kept unchanged. The relative lower-tail bound is new: an
out-of-the-money leg's price is a small probability times a notional, so its
error budget is relative. QuantLib, the canonical reference for the use case,
evaluates `Φ` with an absolute-accuracy erf whose lower tail is relatively
coarse (observed below); this bound is far tighter than that reference needs.
Accuracy beyond it buys the consumer nothing, so the selection is by cost
within it.

| Region / output | Bound | Special values / determinism | Cost and comparator | Justification |
| --- | --- | --- | --- | --- |
| `y = RN(abs(x)/√2) <= 15/32` (`abs(x) <~ 0.663`) | `16u` absolute; `32u` relative for `x < 0` (proved `3u` absolute) | finite normal in `[29/128, 25/32]`; scalar and slice bit-identical | degree-8 polynomial in `y²`, Estrin, no division, no transcendental | `FastCdf.fast_cdf_body_ok` |
| `15/32 < y`, `abs(x) <= 8` | `16u` absolute; `32u` relative for `x < 0` | finite normal; bit-identical | one exact exponent split, the bounded cubic `exp`, one 8/9 rational, one division | `FastCdf.fast_cdf_lower_ok`, `fast_cdf_outer_ok` |
| `abs(x) < 2^-33`, `abs(x) > 8`, non-finite | strong owner's contract | strong owner's bits | strong dispatch | `fast_cdf_fallback_contract`, `fast_cdf_nonfinite`, `fast_cdf_zeros` |

## Derivation

With `a = abs(x)` and the generated nearest binary64 `INV_SQRT2_HIGH` of
`1/√2`, both branches start from `y = RN(a * INV_SQRT2_HIGH)`; the body uses
the signed `RN(x * INV_SQRT2_HIGH)`, whose magnitude is `y`.

**Body (`y <= 15/32`).** `Φ(x) - 1/2 = erf(x/√2)/2`. A relative minimax
polynomial `P` of degree 8 in `s = y²` approximates `erf(y)/y` on
`0 <= y <= 15/32` (`generators/fast_cdf_constants.py`, Remez at 200 bits,
mpmath). The kernel returns

```
s = RN(y*y), s2 = RN(s*s), s4 = RN(s2*s2)
p = Estrin(P; s, s2, s4)                     # pairs, then s2, then s4
Y = RN(0.5 + RN(0.5 * RN(RN(x*INV_SQRT2_HIGH) * p)))
```

`fast_cdf_body.g` bounds the arithmetic against the exact polynomial at the
rounded `y` by `2u` absolute. `FastCdfBody.cdf_body_approx` bounds
`abs(y*P(y²)/2 - ∫_0^y exp(-t²)dt/√π) <= 2^-55 * abs(y)`, through the degree-12
Taylor sum and its integrated remainder; the observed fit error of `P/2` is
`2^-56.86`. The argument's rounding contributes at most
`3u * abs(x)/√2 / √π`, since `exp(-t²) <= 1`. The total is under `3u`.

**Tails (`y > 15/32`).** `Φ(-a) = exp(-a²/2) * erfcx(a/√2) / 2`. The exponent
is split exactly: `(p, e) = two_prod(-0.5*a, a)` gives `p = RN(-a²/2)` and
`p + e = -a²/2`, by Dekker's product or, where the build has it, a fused
multiply-add, which return the same bits on this domain
([lanes.md](lanes.md) §2). Then `exp(-a²/2) = exp(p) * (1 + e)` to within
`e² <= 2^-96`, and the correction joins the rational, off the exponential's
dependency chain:

```
E = cubic_exp(p)                                 # relative 4u
r = RN(N(y) / D(y))                              # Estrin, degrees 8 and 9
lower = RN(RN(0.5*E) * RN(r + RN(r*e)))
Y = lower if x < 0 else RN(1 - lower)
```

`N/D` is a relative minimax fit of erfcx on `[15/32, 91/16]`; the upper end is
the erfcx Taylor centre at or above `RN(8/√2)`. Its proof is an ODE comparison:
erfcx solves `f' = 2t f - 2/√π`. For `R = N/D`, the residual
`ρ = R' - 2tR + 2/√π` is bounded by interval enclosures (`FastCdfResidual`, `abs(ρ) <= 2^-53`).
Integrating `(R - erfcx) exp(-t²)` from the anchor, where `R` is within `2^-56`
relative of the existing certified erfcx Taylor centre (`FastCdfAnchor`),
gives the relative bound `2^-56 + 2^-53 √π/2 < 1.012u` (`FastCdfOde`,
`FastCdfApprox`). `fast_cdf_tail.g` bounds the evaluation by `17u` relative and
the denominator by `[1, 2^30]`.

The remaining terms are relative: the argument rounding
`abs(y - a/√2) <= 2u * a/√2` (`fast_cdf_argument_tight`) moves erfcx by at
most `11/4 * 2u` relative, because `abs(erfcx'(c)) * y <= 11/4 * erfcx(y)`
there (`cdf_erfcx_relative_argument`, from the existing derivative bounds and
`erfcx(1) >= 0.42`); `exp` contributes `4u`; the three final roundings `2u`
plus terms below `2^-90`. Composed exactly in `FastCdf.fast_cdf_lower_ok`,
the lower tail's relative error is below `29.6u <= 32u`, and `lower <= 0.41`.
The complement's rounding adds `u/2`, so both signs stay within `16u`
absolute.

## Checked by

- `formal/fast/FastCdf.v` and the `FastCdf*` files it imports, bound to the
  sources in `formal/binding.sha256` and audited in `formal/audit/KernelAudit.v`.
  The extracted entry `FastCdf.fast_cdf_entry64` is cross-checked against the
  Rust entry on the internal corpus (`fast_normal` lines), including the body
  edge `a = 0x1.536948017480fp-1` and its neighbours.
- `generators/fast_cdf_constants.py` writes the Rust tables, the Coq constants,
  the residual and anchor proofs and both certificates, and is replayed by
  `scripts/check_generators.sh`.
- `generators/fast_reference.py` writes independent 600- and 1000-bit oracle
  intervals (`crates/reference/fixtures/fast.json`) on the strong fixture's
  arguments, the body edge of both signs and a negative-tail sweep;
  `crates/reference/tests/fast.rs` decides both bounds in exact integer
  arithmetic including the oracle's enclosure.
- The fast tests compare scalar and slice bits on mixed packets, remainders and
  the body edge; the determinism digest covers `fast::norm_cdf` and its slice.

Observed on 30,438 mpmath references in the domain (`fast::norm_cdf`, default
and `x86-64-v3` builds, same bits): body 2 ULP, lower tail 7 ULP, upper 2 ULP,
absolute `2u`, relative `7.3u` for `x < 0`. These are observations, not the
contract.

## Cost acceptance

Comparators: the previous `fast::norm_cdf` (centre Taylor polynomial, erfcx
table outside `abs(x) <= 1`), QuantLib's `CumulativeNormalDistribution`,
Risk's Cody-rational `norm_cdf` and SLEEF's AVX-512 erfc as a diagnostic.
Accuracy of those comparators against the same references: previous fast
body 12, lower 17, upper 1 ULP; Risk body 4, tails 6 ULP; QuantLib body 2 ULP but
lower tail about `2e-7` relative (`8.4e8` ULP).

Native evidence follows [the benchmark methodology](../scripts/bench_fast/README.md)
with `scripts/bench_fast/x86/prepare-cdf.py`: paired runs, ten processes by two
rounds, one-sided 95% upper time ratio at most one in every required cell, CPU
isolated, both builds `-C target-cpu=x86-64-v3` (performance is qualified on
FMA builds). Fifty required cells cover pricing, body, lower, upper and wide
banks; dependent latency, scalar throughput and slices of 1, 2, 4, 8, 13, 52,
53 and 4096.

On an Intel Core i9-10920X (Cascade Lake, AVX-512), Linux, rustc 1.97.1, both
wrappers built with `--features simd,std` and `-C target-cpu=x86-64-v3`
against the previous `fast::norm_cdf`, all 50 required cells pass:

| Cell group | Time ratio (candidate / previous) | Worst one-sided 95% upper |
| --- | --- | --- |
| Dependent latency, five banks | 0.79–0.89 | 0.89 |
| Scalar throughput, five banks | 0.70–0.94 | 0.95 |
| Slices of 1–4 | 0.67–0.87 | 0.92 |
| Slices of 8–4096 | 0.29–0.87 | 0.88 |

Diagnostics: a mixed bank with fallbacks 0.58; SLEEF's AVX-512 erfc-based CDF
on 4096 pricing values 0.27; the unchanged strong `norm_cdf` control
1.002–1.006, the noise floor of the paired protocol. These are native
measurements on that host only. Native ARM qualification is not yet run; the
corresponding claims are unestablished.
