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

[ln] §5's rounding test then decides, with `ε₁ = 2^−63`. The proof needs
`log2 x` not to be a breakpoint. It is irrational unless `x = 2^n`, and then it
is the integer `n`, which is representable.

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
| `generators/radix_certificates.py` | writes the four certificates below; the ratio bound is enclosed with `mpmath.iv` |
| `formal/log2/fast_log2.g`, `accurate_log2.g` | `log2`'s paths: `2^−63` and `2^−122` |
| `formal/log2/fast_log10.g`, `accurate_log10.g` | `log10`'s paths: `2^−63` and `2^−122` |
| `generators/log2_log10_reference.py` | the fixture: [LM] Table 7 and its §5.2 siblings, exact powers, special values, random arguments, and 1,200 values to 192 bits per function |

The binding `formal/log2/binding.sha256` covers this document, the constants,
the certificates and the source.

**Checked by:**
- `crates/reference/tests/log2_log10.rs`: 4,029 `log2` and 4,034 `log10` cases,
  bit for bit. A `log10` mismatch would be an argument inside §5's window. It's
  reported, not waived.
- `src/log2/tests.rs`:
  - every unrounded result within its bound, against the 192-bit values;
  - each fast path against its accurate path on 2^20 arguments. Measured, both
    send `2^−9.4` of them to the accurate path, against the analytic `2^−9`.
- The determinism digest's `log2` and `log10` sections on every target.
