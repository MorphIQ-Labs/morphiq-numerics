# `exp2`: correctly rounded radix-2 exponential

`morphiq_numerics::elementary::exp2` (`crates/morphiq-numerics/src/exp2/`)
follows this derivation. It reduces `x` to `exp`'s reduced argument, then runs
[exp.md](exp.md)'s fast path, rounding test and accurate path unchanged. Only
the reduction is new, and its error is certified here (§3).

`exp2(x)` returns `2^x` rounded to nearest, ties to even, for every binary64
`x`, subnormal results included. `2^n` is exact for every integer `n` where it
is representable.

## Sources

- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: Property 3 and
  Table 6.
- **[exp]** [exp.md](exp.md): the table `2^(j/128)`, the fast path, the rounding
  test and the `Q128` accurate path.

## 1. Specification

| Input | Result | Why |
|---|---|---|
| NaN | NaN | |
| `x ≥ 1024` | `+∞` | the least `x` whose result rounds to `+∞` (*generated*) |
| `x ≤ −1075` | `+0` | the greatest `x` whose result rounds to `+0` (*generated*) |
| `x` between `−0x1.71547652b82fep−54` and `0x1.71547652b82fdp−53` | `1` | `2^x` rounds to 1 there (*generated*) |
| otherwise | `RN(2^x)` | §2–§4 |

`generators/exp2_reference.py` derives the thresholds by bisection with the
interval oracle. Its fixture `crates/reference/fixtures/exp2.json` is the test
reference.

**Accuracy needed.** [LM] Property 3: an approximation within mantissa
distance `2^−113` of `2^x` rounds correctly, over the whole range. Relative
error below `2^−114` suffices ([LM] footnote 10).

## 2. Reduction

`n = RN_int(128·x)`, computed as `(128·x + S) − S` with `S = 1.5·2^52`.
`128·x` is exact, and `|n| ≤ 137,600`. Then:
- `j = n mod 128` and `k = (n − j)/128`;
- `r = x − n/128`, so `|r| ≤ 1/256`.

`r` is exact: `n/128` is exact, and for `n ≠ 0` the subtraction is exact by
Sterbenz's lemma, since `x` and `n/128` are within a factor of 2. For `n = 0`,
`r = x`. So `2^x = 2^k · 2^(j/128) · e^(r·ln 2)`, with `|r·ln 2| ≤ 0.0027076`.
That's within [exp] §3's range for its reduced argument, `|r| ≤ 0.0027077`.

## 3. Fast path

`r·ln 2` as a double-word:
```
(p, e) = two_prod(r, LN2_HI)           exact
(r_hi, r_lo) = two_sum(p, RN(e + RN(r·LN2_LO)))
```
- `LN2_HI` is `RN(ln 2)`, and `LN2_LO = RN(ln 2 − LN2_HI)`. Together they're
  within `2^−109.9` of `ln 2` relatively (*generated*:
  `generators/radix_constants.py`).
- The error against the exact `r·ln 2` is below `2^−113` (*certified*:
  `formal/exp2/reduction.g`, proves `2^−114.57`). That's [exp]'s reduction
  budget.
- `|r_lo| ≤ 2^−62`.
- `two_prod`'s domain holds: `r` is `0` or at least `2^−59` in magnitude (it is
  a multiple of `ulp(x)` once `|x| ≥ 2^−7`, and `x` itself when smaller).

Then [exp] §4's fast path at `(r_hi, r_lo)` and `j` gives `Y`, within
`ε₁ = 2^−69` of `2^(j/128 + r)` (`formal/exp/fast.g`). [exp] §5's rounding test
returns `y_hi·2^k` for `k ≥ −1021`.

## 4. Accurate path

`r·ln 2` in `Q128`: `r` converts exactly, and the product with `ln 2` (*generated*,
relative error below `2^−129.4`) is truncated. So its absolute error is below
`2^−126·|r| ≤ 2^−134`. Then [exp] §6's series, table product and scaling give
`2^x`.
- The series and product contribute below `2^−124`, as in [exp].
- The argument's error, `2^−134`, contributes below `2^−133.9`.

The total relative error is below `2^−123.9`, against `2^−114` needed (§1), so
rounding once rounds `2^x` correctly. `2^n` for an integer `n` gives `r = 0`,
`j = 0` and an exact result on both paths.

## 5. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/radix_constants.py` | `LN2_HI`, `LN2_LO`, `ln 2` in `Q128`, with their errors (`src/exp2/tables.rs`) |
| `generators/radix_certificates.py` | writes `formal/exp2/reduction.g` from those errors |
| `formal/exp2/reduction.g` (Gappa 1.4.1) | the reduction, within `2^−113` |
| `generators/exp2_reference.py` | the fixture: [LM] Table 6, thresholds, integers, special values, random arguments, and 1,200 values to 192 bits |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

The binding `formal/exp2/binding.sha256` covers this document, the constants,
the certificate and the source.

**Checked by:**
- `crates/reference/tests/exp2.rs`: all 4,049 fixture cases, bit for bit.
- `src/exp2/tests.rs`:
  - every unrounded result within its bound, against the 192-bit values;
  - the fast path against the accurate path on 2^20 arguments. Measured, it
    sends `2^−15` of them to the accurate path, as `exp` does.
- The determinism digest's `exp2` section on every target.
