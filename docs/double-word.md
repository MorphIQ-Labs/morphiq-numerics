# Error-free transforms and double-word arithmetic

`morphiq_numerics::eft` provides the rounded sum or product of two binary64
numbers together with its exact rounding error. `morphiq_numerics::double_word`
builds an unevaluated sum of two binary64 numbers on those transforms, with
proved relative error bounds. Later functions' accurate paths are built from
these.

Every algorithm here is fully specified by its source, operation by operation.
The code follows the cited statement line for line, and nothing in it is a design
choice of this crate. `u = 2^−53` is the unit roundoff and `RN` is
round-to-nearest, ties-to-even.

## Sources

- T. J. Dekker, "A floating-point technique for extending the available
  precision", *Numerische Mathematik* 18, 1971: the splitting (§6, (6.1)–(6.3)),
  and Veltkamp's exact product (end of §5).
- M. Joldes, J.-M. Muller, V. Popescu, "Tight and rigorous error bounds for
  basic building blocks of double-word arithmetic", *ACM TOMS* 44(2), 2017:
  Fast2Sum and 2Sum (Algorithms 1 and 2), and the double-word algorithms.
- J.-M. Muller, L. Rideau, "Formalization of double-word arithmetic, and
  comments on …", *ACM TOMS* 48(1), 2022: Coq proofs of every bound, and the
  improved bound for the double-word product.

## Error-free transforms

| Function | Algorithm | Exact when |
|---|---|---|
| `two_sum(a, b)` | 2Sum (Knuth, Møller): Joldes et al. Algorithm 2 | `\|a\|, \|b\| ≤ 2^1020` |
| `fast_two_sum(a, b)` | Fast2Sum (Dekker): Joldes et al. Algorithm 1 | `\|a\|, \|b\| ≤ 2^1021`, and `a = 0`, `e_a ≥ e_b`, or `\|a\| ≥ \|b\|` |
| `two_prod(a, b)` | Veltkamp's product on Dekker's splitting | the domain below |

Each returns `(r, e)` with `r` the rounded result and `r + e` the exact sum or
product.

Addition can't underflow inexactly: every sum of two binary64 numbers is a
multiple of `2^−1074`, so a subnormal sum is exact. So 2Sum and Fast2Sum need
only magnitude limits, which exclude overflow.

### `two_prod` without a fused multiply-add

`core` has no fused multiply-add, so the product's error is computed by
splitting.
- **The split** (Dekker (6.1), with `c = 2^27 + 1` from (6.2)): `p = RN(x·c)`,
  `q = RN(x − p)`, `head = RN(q + p)`, `tail = x − head`. The head carries at
  most 26 significant bits and the tail at most 26 (Dekker (5.5)–(5.7)).
- **The product** (Veltkamp, as Dekker states it at the end of §5): `p = RN(a·b)`,
  `e = (((a_h·b_h − p) + a_h·b_t) + a_t·b_h) + a_t·b_t`. The first word is
  `RN(a·b)`, which double-word arithmetic requires. Dekker's own `mul12` doesn't
  guarantee that.

**Domain.** `two_prod(a, b)` is exact when `a · b = 0` or
`|a · b| ≥ 2^−969`, and `|a| ≤ 2^e_a`, `|b| ≤ 2^e_b` for some
`e_a, e_b ≤ 994` with `e_a + e_b ≤ 1020`, which excludes overflow.

- **Underflow:** machine-checked. This is Flocq's `Dekker` theorem (Boldo's
  formalization, `Flocq.Pff.Pff2Flocq`), whose algorithm is exactly this one:
  the same split with `s = 53 − ⌊53/2⌋ = 27`, the same rounded partial products,
  and the same summation order. It is instantiated for binary64 (radix 2,
  precision 53, minimum exponent −1074) with ties-to-even in
  `formal/two-prod/TwoProdBinary64.v`. Its hypothesis
  `|a · b| ≥ 2^(emin + 2·prec − 1) = 2^−969` covers subnormal operands.
- **Overflow:** machine-checked in Flocq's IEEE 754 model (`two_prod_ieee`,
  `formal/binary64/IEEE64Eft.v`). The split's operand times `2^27 + 1` is at
  most `2^(e + 29)`, and its head, the operand rounded to 26 bits, is at most
  `2^e`. So the partial products and their sums are at most
  `10·2^(e_a + e_b) < 2^1024`.

These conditions are sufficient, not necessary: `2^−969` is the theorem's
hypothesis, not the boundary of exactness. Outside the domain, exactness is
neither claimed nor ruled out; `two_prod` returns what the arithmetic produces.
In particular, an earlier hand derivation of this domain included products in
`[2^−970, 2^−969)` and excluded subnormal operands. No proof covers that range, so
it isn't claimed. The proved domain admits subnormal operands, so they are
covered.

## Double-word numbers

A double-word number is an unevaluated sum `hi + lo` of binary64 numbers with
`hi = RN(hi + lo)` (Joldes et al. Definition 1.4). The type admits only such
pairs:
- `from_parts` checks the condition;
- `sum` and `product` produce exact ones;
- every operation returns one.

| Operation | Algorithm | Relative error bound (Muller–Rideau Table 1) |
|---|---|---|
| `add_f64` | DWPlusFP, Joldes et al. Algorithm 4 | `2u²` |
| `add`, `sub` | AccurateDWPlusDW, Algorithm 6 | `3u² + 13u³` (asymptotically optimal, M–R Property 2.1) |
| `mul_f64` | DWTimesFP1, Algorithm 7 | `1.5u² + 4u³` |
| `mul` | DWTimesDW1, Algorithm 10 | `5u²/(1 + u)² < 5u²` under ties-to-even (M–R Theorem 2.6; 7u² in the 2017 paper) |
| `div_f64` | DWDivFP3, Algorithm 15 | `3u²` |
| `div` | DWDivDW2, Algorithm 17 (same results as Algorithm 16) | `15u² + 56u³` |

`sub` is `add` of the exact negation. The FMA-based variants (Algorithms 9, 11,
12 and 18) aren't used, since `core` has no fused multiply-add, and Algorithm 5
(the "sloppy" sum) has no relative bound.

**Domain.** Each bound is for a nonzero exact result; it says nothing when the
exact result is zero.

- **`add_f64`, `add`, `sub`:** every word at most `2^1018` in magnitude for
  `add_f64`, `2^1016` for `add` and `sub`. The bounds are proved in binary64
  itself, with gradual underflow, so subnormal words, intermediates and results
  are covered. The magnitude limit excludes overflow.
- **`mul_f64`, `mul`:** proved in binary64, with gradual underflow, when:
  - the leading words' product (`x_hi · y`, or `x_hi · y_hi`) is zero or at
    least `2^−969` in magnitude, which is `two_prod`'s domain;
  - every product of a leading and a trailing word (`x_lo · y`, or
    `x_hi · y_lo` and `x_lo · y_hi`) is zero or at least `2^−1022`;
  - every word is at most `2^508` in magnitude, which excludes overflow.

  Every nonzero word between `2^−484` and `2^484` in magnitude meets all of
  these.
- **`div_f64`, `div`:** proved in binary64, with gradual underflow, when for
  some `L, H ≥ 0` with `2L + 2H ≤ 917`, every nonzero word `w` of `x` and `y`
  has `2^−L ≤ |w| < 2^H`, and the divisor's leading word is nonzero. For
  example, every nonzero word between `2^−229` and `2^229` in magnitude. The
  same limits exclude overflow.

**Why the additive operations can't underflow wrongly.** Every rounding in 2Sum,
Fast2Sum, `add_f64` and `add` rounds a sum or difference of two binary64 numbers.
Above `2^−1022` binary64 rounds such a value as the unbounded model does. Below
it, the exact value is a multiple of `2^−1074` and so a binary64 number, which
both models return unchanged. So the binary64 computation is the unbounded one,
step by step.

**Why the divisions can't underflow wrongly.** Each rounds two quotients,
`x_hi / y` and `d / y`, where `d` is the remainder. The first is at least
`2^(−L−H)` unless zero. The remainder is a sum of words and of products of
words, each a multiple of `2^(−2L−H−105)`, and rounding keeps a multiple of a
power of two a multiple of it. So a nonzero remainder is at least that power,
and `d / y` is at least `2^(−2L−2H−105) ≥ 2^−1022`. The differences the
algorithms round, `x_hi − π_hi` and its successor, are exact
(`xhmpih_exact`, `div_error_FLX`, `Algo15_P`).

**Why no operation overflows.** Flocq's IEEE 754 model (`IEEE754.Binary`) has
overflow, infinities and NaNs. Its `Bplus`, `Bminus`, `Bmult` and `Bdiv` return
the binary64-model rounding, and a finite value, whenever that rounding is below
`2^1024` in magnitude. A bound `|v| ≤ k·2^e`, with `k·2^e` representable, survives
each rounding, so bounds propagate through every operation:
- sums add their operands' bounds, and products multiply them;
- a quotient by a divisor at least `2^−L` is at most `2^L` times its dividend's
  bound;
- the split's head is its operand rounded to 26 bits (Flocq's `Veltkamp`), so it
  is no larger than the operand's power-of-two bound.

On the domains above every bound stays below `2^1024`. For example, `add`'s
largest is `232·2^1016`. So no operation overflows, and each algorithm returns
its binary64-model value.

## Checked operations

Each operation above, and the exact constructors `sum` and `product`, has a
`checked_` form returning `Result<DoubleWord, CheckError>`. It returns the
unchecked operation's result, bit for bit, exactly when the operands satisfy
the hypotheses of that operation's IEEE 754 theorem. For such operands the
theorem proves the result finite, a double-word number, and within the bound in
the table.

| Checked | Theorem | Hypotheses checked |
|---|---|---|
| `checked_sum(a, b)` | `two_sum_ieee` | `\|a\|, \|b\| ≤ 2^1020`; the result is exact |
| `checked_product(a, b)` | `two_prod_ieee` | some `−537 ≤ e_a, e_b ≤ 994` with `e_a + e_b ≤ 1020` bound `\|a\|`, `\|b\|`; `a·b = 0` or `\|a·b\| ≥ 2^−969`; the result is exact |
| `checked_add_f64` | `add_f64_ieee` | every word `≤ 2^1018` |
| `checked_add`, `checked_sub` | `add_ieee`, `sub_ieee` | every word `≤ 2^1016`; the exact result nonzero |
| `checked_mul_f64` | `mul_f64_ieee` | every word `≤ 2^508`; `x_hi·y` zero or `≥ 2^−969`; `x_lo·y` zero or `≥ 2^−1022` |
| `checked_mul` | `mul_ieee` | every word `≤ 2^508`; `x_hi·y_hi` zero or `≥ 2^−969`; `x_hi·y_lo` and `x_lo·y_hi` each zero or `≥ 2^−1022` |
| `checked_div_f64`, `checked_div` | `div_f64_ieee`, `div_ieee` | a nonzero divisor; some `L, H ≥ 0` with `2L + 2H ≤ 917` put every nonzero word in `[2^−L, 2^H)` |

**Decided exactly.**
- Magnitudes are compared with powers of two, which is exact.
- A product's condition is decided on the significands in integer arithmetic,
  never through the rounded product: a product just below `2^−969` can round to
  it.
- The existential conditions reduce to their least instances, since each is
  monotone. The least exponents bounding `|a|` and `|b|` decide `product`'s,
  and the least `L` and `H` covering the nonzero words decide the quotients'.

**What an error means** (`CheckError`):
- `InvalidOperand`: a word is infinite or NaN, or `hi ≠ RN(hi + lo)`. The input
  isn't a double-word number.
- `DivisionByZero`: the divisor is zero.
- `OutsideProvenDomain(h)`: the operands are valid, but hypothesis `h` fails, so
  the bound isn't proved for them. The hypotheses are sufficient, not
  necessary: accuracy isn't ruled out, only not proved, and the unchecked
  operation still returns what the arithmetic produces.
  - `Magnitude` is the overflow guard.
  - `ProductUnderflow` is the product conditions.
  - `QuotientRange` is the quotients' exponent span.
  - `ZeroResult` is described next.

**Zero results.** The bounds are relative, so they say nothing when the exact
result is zero. That happens exactly when:
- for `add` and `sub`, one operand is the other's negation, word for word, since a
  value has one double-word representation, `hi = RN(value)`;
- for `add_f64`, `x_lo = 0` and `x_hi = −y`;
- for the products, a leading word is zero;
- for the quotients, the dividend's leading word is zero.

The checked operation decides that exactly. It then admits the result only if
it is zero, so a zero result is verified directly rather than claimed.

**Bound to the proofs.** `crates/reference/tests/checked.rs` reads the theorem
statements in `formal/binary64/` and fails if one no longer states a constant or
predicate the checks use. It also tests the checks themselves:
- against an independent oracle: each hypothesis written as the Coq statement
  writes it, in exact rational arithmetic, with the existential conditions
  searched;
- at every boundary, with the representable values on either side;
- with a product whose rounding reaches `2^−969` while the exact product stays
  below it.

**Cost.** Checking adds a few nanoseconds per operation. Measured informally on
one Apple M1 Pro core, best of seven runs over 2·10^6 operands, it took
`add` from 1.7 to 4.7 ns, `mul` from 2.0 to 9.2 ns and `div` from 3.4 to 11.4 ns.
The checks allocate nothing and are `no_std`.

## Exponential

`DoubleWord::exp_split(x)` returns `(value, n)` with `exp(x) ≈ value · 2^n`
for a double-word `x = hi + lo` with `|hi| < 1455`. Otherwise, NaNs and
infinities included, it returns `None`. `value` is a double-word number in
`[0.9996, 2.0008)` and `n` an integer in `[-2100, 2099]`. The scale stays with
the caller, so `value · 2^n` may lie outside binary64's range.

**Bound.** `|value · 2^n - exp(x)| <= 16u² · exp(x)` on the whole domain, that
is relative `2^-102`. `DwExp.dwexp_ok` (`formal/fast/DwExp.v`) proves it for the
kernel's IEEE 754 transcription, and `DwExp.dwexp_none` proves the `None`
cases. The proof composes the error to under `12u²`. The worst error observed
over the 22,030 independent 600-bit references
(`generators/double_word_exp_reference.py`) is `4u²`.

**Derivation.** With `ℓ = ln(2)/1024`:

1. **Index.** `n = RN(RN(hi · INV) + S) - S`, with `INV = RN(1024/ln 2)` and
   `S = 1.5 · 2^52`. That is an integer within `1/2 + 10^-9` of `hi/ℓ`, with
   `|n| <= 2149501`. The table index is `j = n mod 1024` and the binary
   exponent `floor(n / 1024)`.
2. **Reduction.** A three-part Cody–Waite split `ℓ ≈ L1 + L2 + L3`, generated
   by `generators/fast_exp_constants.py`. `L1` and `L2` have 31 significant
   bits, so `n·L1` and `n·L2` are exact, and `|L1 + L2 + L3 - ℓ| <= 2^-128`.
   With `(q_hi, q_lo) = two_prod(n, L3)`, four `add_f64` steps give
   `r = (((x ⊕ -n·L1) ⊕ -n·L2) ⊕ -q_lo) ⊕ -q_hi`. Each step's output is a
   proved double word. `|r - (x - n·ℓ)| <= 0.52u²`, almost all of it the
   split's `|n| · 2^-128`, and `|x - n·ℓ| <= 0.000338451`.
3. **Polynomial.** `exp(r)` by double-word Horner evaluation of the degree-7
   Taylor polynomial, starting from `1/7!`. Each step is one `mul` by `r`,
   then `add_f64` of the coefficient's low word (zero for `1/0!`, `1/1!` and
   `1/2!`, so skipped) and of its high word. The coefficients are double-word
   roundings of `1/k!`, within `2^-105` relative. The evaluation is within
   `2.0042u²` of the polynomial, and the polynomial within `0.4u²` of
   `exp(r)`.
4. **Reconstruction.** `value = T_j ⊗ v`, where `T_j` is the double-word table
   entry `exp(j·ℓ)` shared with the bounded `exp`. The reflective certificate in
   `FastExpTables` checks its 1024 entries against `exp` within `2^-104`. A
   second check, `DwExp.dwx_tab_check`, shows each entry is a normalized double
   word whose low word is zero or at least `10^-300`.

**Guards.** They keep every operation inside its proved domain, and each one
is part of the proof:
- below `|hi| < 2^-60` the result is `1 ⊕ x` with `n = 0`, within `2u² + x²`;
- a reduced argument below `10^-247` returns `T_j` itself, since `exp(r) = 1`
  within `2^-820`;
- a trailing word of `r` below `10^-300`, or of a Horner value below
  `10^-60`, is dropped, which moves the result by less than `2^-990` and
  `2^-187` relative.

With them every product of a leading and a trailing word is zero or normal, as
the multiplication bound requires. The error budget, relative to `exp(x)`:

| Source | Bound |
|---|---|
| Table entry | `4u²` (certified) |
| Final product | `5u²` |
| Horner evaluation, truncation and reduction | `2.94u²` |
| Total, with cross terms (proved) | under `12u²` |
| Published | `16u²` |

**Products.** Every multiplication is DWTimesDW1 and every exact product is
`two_prod`'s, operation for operation. Only the source of the exact product
varies with the target (ADR 0002). It is a hardware fused multiply-add in
builds that target one, and one runtime dispatch per call into an FMA-enabled
body on x86-64 with `simd` and `std`. Elsewhere it is Dekker's algorithm. On
`two_prod`'s proved domain they return the same words. The unit tests compare
all three on 100,000 inputs, and `scripts/check_fma.sh` requires the FMA
build's cross-check corpus to be identical.

## Machine-checked proofs

`scripts/check_formal.sh` (the `formal (coq)` CI job) checks these, on Coq 8.15.2
with Flocq 3.4.3 and math-comp ssreflect 1.14.0, in an image pinned by digest
(`.cargo/coq-image`, with the libraries' versions in `.cargo/coq-packages`).

**What is machine-checked:**
- **The double-word bounds.** `formal/double-word` is Muller and Rideau's Coq
  development, vendored under its MIT license, which builds with no admitted
  goal. It proves each bound in the table above in Flocq's unbounded-exponent
  model.
  - **Two patches.** As distributed, the multiplicative theorems assumed an
    exact product for *all real* arguments, which is false, and that an
    uninterpreted axiom `TwoProd` equals `Fast2Mult`, which can't be proved.
    So they applied to nothing. The premise now covers binary64 arguments only,
    the only case the proofs use, and `TwoProd` is defined as `Fast2Mult`.
    `PROVENANCE.md` there records both patches.
  - **Instances.** `formal/binary64/Instances.v` instantiates the four
    multiplicative theorems at precision 53, ties-to-even, with every premise
    discharged. The exact product is `fast2mult_exact`, from Flocq's
    `mult_error_FLX`. They are `mul_f64_bound`, `mul_bound`, `div_f64_bound`
    and `div_bound`.
- **The additive bounds in binary64.** `formal/binary64/Binary64Add.v` defines
  `two_sum`, `fast_two_sum`, `add_f64`, `add` and `sub` in Flocq's binary64
  model (precision 53, minimum exponent −1074, ties-to-even, gradual
  underflow). It proves each equal, step by step, to its unbounded-model
  counterpart on binary64 inputs. So the vendored bounds hold in binary64:
  - `add_f64_bound`: `2u²`;
  - `add_bound` and `sub_bound`: `3u²/(1 − 4u)`, which is at most
    `3u² + 13u³`.
- **The multiplicative bounds in binary64.** `formal/binary64/Binary64Mul.v`
  defines `two_prod`, `mul_f64` and `mul` as the Rust computes them in the
  binary64 model, and proves them equal, step by step, to the unbounded-model
  algorithms on the domain above:
  - each product rounds alike in both models when it is zero or at least
    `2^−1022`;
  - on its domain, Dekker's `two_prod` returns `RN(a·b)` and the exact error
    (`two_prod_exact`), which is what `Fast2Mult` returns in the unbounded
    model.

  So the instances' bounds hold in binary64: `mul_f64_bound`, `3/2·u² + 4u³`,
  and `mul_bound`, `< 5u²`.
- **The division bounds in binary64.** `formal/binary64/Binary64Div.v` proves
  `div_f64` and `div`, as the Rust computes them, equal step by step to the
  unbounded-model algorithms on the domain above. It uses the granularity
  lemmas of `formal/binary64/Grid.v` for the remainder's quotient. So
  `div_f64_bound` (`3u²`) and `div_bound` (`15u² + 56u³`) hold in binary64.
- **No overflow, in IEEE 754 arithmetic.** `formal/binary64/IEEE64*.v` define
  every algorithm with Flocq's IEEE 754 binary64 operations (`b64_plus`,
  `b64_minus`, `b64_mult`, `b64_div` at round-to-nearest-even), operation for
  operation as the Rust writes it, and prove that on the domains above every
  result is finite and equal to the binary64-model value, so the bounds hold:
  - `add_f64_ieee`, `add_ieee`, `sub_ieee` (`IEEE64Add.v`);
  - `mul_f64_ieee`, `mul_ieee` (`IEEE64Mul.v`);
  - `div_f64_ieee`, `div_ieee` (`IEEE64Div.v`);
  - `two_sum_ieee`, `fast_two_sum_ieee`, `two_prod_ieee` (`IEEE64Eft.v`).
- **`two_prod`'s exactness.** `formal/two-prod/TwoProdBinary64.v` proves
  `two_prod_exact`: for binary64 with ties-to-even, `a · b = p + e` on the
  domain above.
- **The axiom audit.** The gate requires the global axioms of every relied-on
  theorem (`formal/audit/Audit.v`) to be exactly `formal/axioms.expected`: Coq's
  four classical-reals axioms.
- **The exponential.** `formal/fast/DwExp.v` transcribes `exp_split` in IEEE
  754 arithmetic and proves `dwexp_ok`, the `16u²` bound with the value's and
  the exponent's ranges, and `dwexp_none`, from the bounds above and
  `FastExpTables`. The kernel audit (`formal/audit/KernelAudit.v`) checks their
  axioms.
- **The binding.** `formal/binding.sha256` binds the proofs to `eft.rs`,
  `double_word.rs`, the checked operations' hypotheses
  (`double_word/checked.rs`) and the exponential (`double_word/exp.rs` and its
  generated `exp_tables.rs`) by hash. Editing any of them, or a proof, fails the
  lane until the proofs are rerun and the manifest is updated with them.

**What is assumed:** Rust's `f64` arithmetic is IEEE 754 binary64 with
round-to-nearest-even, without fused multiply-add contraction, as the language
specifies. The determinism digest checks bit-identical results on every
supported target.

**What is cross-checked, not proved: the transcription.** Each Rust function is
meant to be its Coq definition operation for operation. Where the paper proves an
operation exact, the unbounded-model definition leaves it unrounded and the Rust
rounds it; the binary64 and IEEE 754 definitions round it as the Rust does, and
the proofs show that gives the same value. The IEEE 754 definitions are
extracted to OCaml (`formal/extraction`), and the gate runs them on a corpus the
Rust library writes (`crosscheck-corpus` in `crates/reference`), requiring
identical bits for every result; any NaN matches any NaN, since IEEE 754 leaves
NaN payloads to the implementation. The corpus has 4,000 cases per function,
covering the proved domains, subnormals, signed zeros and overflow. For
`exp_split` it has 8,000, mostly inside its domain, plus NaN, the infinities
and the domain's edges.
- **It can fail:** a reassociated sum in `mul`, `add`, `div_f64` or `div`
  changes between 56 and 410 of the corpus's results. Reordering `two_prod`'s
  middle partial products changes none, correctly: on its domain every partial
  sum is exact.
- **It isn't a proof:** a transcription error that changes no corpus result
  would pass.

| Rust | Coq definition | Theorem |
|---|---|---|
| `add_f64` | `DWPlusFP` (`DWPlus.v`); `add_f64` (`Binary64Add.v`) | `DWPlusFP_bound`, `2u²`; in binary64, `add_f64_bound`; in IEEE 754, `add_f64_ieee` |
| `add`, `sub` | `AccurateDWPlusDW` (`DWPlus.v`); `add`, `sub` (`Binary64Add.v`) | `DWPlusDW_relerr_bound`, `3u²/(1 − 4u)`; in binary64, `add_bound`, `sub_bound`; in IEEE 754, `add_ieee`, `sub_ieee` |
| `mul_f64` | `DWTimesFP` (`DWTimesFP.v`) | `DWTimesFP_correct`, `3/2·u² + 4u³`; instance `mul_f64_bound`; in binary64, `Binary64Mul.mul_f64_bound`; in IEEE 754, `mul_f64_ieee` |
| `mul` | `DWTimesDW1` (`DWTimesDW.v`) | `DWTimesDW1_correct_even`, `< 5u²` under ties-to-even; instance `mul_bound`; in binary64, `Binary64Mul.mul_bound`; in IEEE 754, `mul_ieee` |
| `div_f64` | `DWDivFP3` (`DWDivFP.v`) | `DWDFP3_correct`, `3u²` (`dh`, `dt` exact); instance `div_f64_bound`; in binary64, `Binary64Div.div_f64_bound`; in IEEE 754, `div_f64_ieee` |
| `div` | `DWDivDW2` (`DWDivDW.v`) | `DWDDW_correct`, `15u² + 56u³` (`pih` exact); instance `div_bound`; in binary64, `Binary64Div.div_bound`; in IEEE 754, `div_ieee` |
| `two_prod` | `Dekker` (Flocq), via `TwoProdBinary64.v`; `two_prod64` (`IEEE64Mul.v`) | `two_prod_exact`; in IEEE 754, `two_prod_ieee` |
| `two_sum` | `TwoSum` (`DWPlus.v`); `two_sum64` (`IEEE64Add.v`) | `TwoSum_correct`; in IEEE 754, `two_sum_ieee` |
| `fast_two_sum` | `Fast2Sum` (`F2SumFLX.v`); `fast_two_sum64` (`IEEE64Add.v`) | `F2Sum_correct_abs`, `F2Sum_correct_cexp`; in IEEE 754, `fast_two_sum_ieee` |
| `exp_split` | `dwexp64` (`DwExp.v`) | `dwexp_ok`, `16u²`; `dwexp_none` |

## Checked by

The oracle is exact integer arithmetic (`num-bigint` in the unpublished
`crates/reference`), decoding each binary64 from its bits. It shares no
arithmetic with the library.
- **2Sum:** 200,000 pairs with exponent gaps up to ±60, both orders; plus the
  subnormal range and zero.
- **Fast2Sum:** 200,000 pairs with `e_a ≥ e_b`.
- **2Prod:**
  - 200,000 normal pairs across the whole domain;
  - every edge of the domain (exponent sums `−969` and `1018`, magnitudes up
    to `2^994`), with all-ones and power-of-two significands;
  - subnormal operands, which the proved domain admits;
  - a split tie;
  - zeros.
- **Each double-word operation:** 100,000 random double-word operands, checked
  against its bound with the bound's denominator cleared, and checked to return
  a double-word number.
- **The products at the top of their domain:** 100,000 cases with words just
  below `2^508`, checked finite and within bound.
- **The multiplicative operations at the bottom of their domain:** 100,000
  cases with leading-word products from `2^−969` and trailing-word products from
  `2^−1022`, including the `2^−969` edge.
- **The divisions across their domain:** 99,999 cases at three corners,
  `(L, H) = (458, 0)`, `(229, 229)` and `(0, 458)`.
- **The additive operations at both ends of their domain:**
  - 100,000 cases at the bottom of the range, with subnormal trailing words,
    subnormal `y`, and sums that cancel into the subnormal range;
  - 100,000 cases with words just below `2^1018` (`add_f64`) and `2^1016`
    (`add`, `sub`), checked finite and within bound.
- **Published worst cases:**
  - DWPlusFP reaches above `1.99u²` on Joldes et al.'s example after Theorem 2.2.
  - AccurateDWPlusDW reaches above `2.99u²` on Muller and Rideau's Property 2.1.
    No random sample approaches that, so it shows the code is the published
    algorithm, not merely within its bound.
- **Oracle self-check:** a test confirms the oracle sees inexact sums and
  products, so each check can fail.
