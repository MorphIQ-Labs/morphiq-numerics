# Numerical mutation gate

Run from the repository root on Linux or macOS:

```sh
cargo install --locked cargo-mutants --version "$(cat .cargo/mutants-version)"
python3 -m unittest scripts.test_numerical_mutations
python3 scripts/check_numerical_mutations.py target/numerical-mutations
```

Choose a fresh output directory on each run. The gate preserves logs, an
inventory and a JSON receipt there, including failures. It copies tracked and
nonignored untracked files into a temporary source tree, applies one patch at a
time there, and removes that tree on exit. The checkout is never mutated.

The required Ubuntu x86-64 and macOS ARM test jobs run the same command, in
both scalar and `simd,std` configurations, using an output directory in
`runner.temp` named for the workflow run and attempt. Receipts and builds stay
outside the restored Cargo cache, and artifact uploads select that attempt's
receipts and logs. This checks numerical behavior,
not native performance. A successful receipt has fourteen numerical rejections
(seven faults in two configurations) and two equivalent-control passes, each
preceded by a passing baseline. It does not claim a whole-crate mutation score.

## Fault catalog

`catalog.json` names each fault, its derivation, its production-source patch
and the exact test that must reject it. These faults follow the arithmetic
contracts:

| Fault | Required observation |
| --- | --- |
| Drop 2Sum's residual | Exact integer addition no longer equals the two components |
| Reverse Q128's rounding comparison | A neighboring binary64 value is nearer |
| Decrement exp's reconstruction exponent bias | Independent MPFR fixture bits differ |
| Discard Q128's addition carry | The significand is no longer normalized |
| Reduce the splitter's shift from 27 to 26 | Exact integer multiplication differs from the two components |
| Subtract ln's rounding uncertainty | A midpoint-crossing interval is incorrectly accepted |
| Skip the obstacle sweep's complementarity check | A two-sided contact set is reported solved |

Compilation failure, timeout, signal termination, zero or ignored tests, a
different failing test and an unrelated panic do not count as kills. The named
test must run alone, return Cargo's test-failure status and report the catalog's
numerical assertion. The runner's negative controls exercise these distinctions.
Each test invocation has a five-minute limit; a timeout fails the gate and kills
the owned process group before cleanup. Unappliable patches fail explicitly.

When a mutant survives, inspect the numerical contract and add an independent
oracle witness if a test is missing. Do not remove faults to improve the score.
Equivalent controls require an explicit arithmetic justification, remain in the
catalog and receipts, and never count as numerical kills. Runtime source is
unchanged by this gate; the production implementation and its proofs remain the
reference.

The split-precision fault exposed a missing witness: for `x = 3/2 + 2^-26`, a
27-bit head's exact square is `9/4 + 3*2^-26 + 2^-52`, requiring 54 significant
bits. If splitting keeps all of `x` in the head, its rounded square loses the
last term and the zero tail cannot restore it. The reference test checks the
midpoint, its adjacent binary64 values, signs and exponent scales using exact
integer arithmetic. The older split-tie square near one does not expose this
fault because its square stays in the lower binade.

## Inventory floor

The pinned `cargo-mutants --no-config --list --json --all-features` inventory
covers both published crates. `inventory-floor.json` requires at least 10,595
syntactic candidates in `morphiq-numerics` and 308 in `morphiq-numerics-arch`,
with individual floors for all 74 inventoried files. Growth elsewhere cannot
hide a missing file. Raw inventory and counts are retained with each run.

This is a discovery floor, not an assertion that all 10,903 candidates are
executed or killed. The tool does not expand macros; generated lane bodies are
not covered by this count. The catalog, oracle tests, lane checks and formal
mutation gates provide distinct evidence. A tool upgrade, file move or genuine
simplification may require a reviewed floor update; never regenerate floors
automatically in CI or lower them merely to pass a failed gate.

## Splitter control

`splitter-minus-one` retains the original candidate `2^27 + 1 -> 2^27` as an
equivalent control. It survived the assigned split-tie test and the broader
exact-product tests. Survival alone does not establish equivalence. The
arithmetic argument is below; the control must pass its exact-product test and
is recorded separately from the seven faults.

On the existing split domain, `|x| <= 2^994`, multiplying a binary64 `x` by
`2^27` is exact and finite. Let `P = 2^27*x`. The replacement computes
`head = P - RN(P - x)`; this last subtraction is exact by Sterbenz's lemma.
It gives `x` rounded to 26 significant bits, the same head established for
the original splitter in [the double-word derivation](../../docs/double-word.md).
To see this for positive `x`:

1. If `x` has at most 26 significant bits, `P-x` has at most 53 and is exactly
   representable, including for subnormal `x`. Thus `head=x`.
2. Otherwise write `x=M*2^(e-52)`, with integer `2^52 <= M < 2^53`, and put
   `G=2^(e-25)`. Here `e >= -1048`, so `G/2` is representable even at the
   bottom of the domain. `P=M*G`. When `P-x >= 2^(e+27)`, rounding `P-x` uses
   spacing `G`. Subtracting this rounded value from `P` rounds `x` to spacing
   `G`, i.e. 26 significant bits. At a halfway case, `M` is a multiple of
   `2^26` and is even, so translation by `M` preserves the ties-to-even choice.
3. In the remaining lower-binade strip, `x < 2^e/(1-2^-27)`. Binary64 spacing
   implies `x <= 2^e*(1+2^-27)`: the next representable value already exceeds
   that strip. Rounding `P-x` now uses spacing `G/2`. Its distance from
   `P-2^e` is at most `G/4`; at equality the latter has an even grid index.
   Consequently `head=2^e`, also the 26-bit rounded value of `x`.

Negation gives the same result for negative inputs by rounding symmetry; both
sequences also produce the same head and tail at signed zero. With identical
heads, the subsequent `x-head` tails and all product operations are identical.
The original fault hypothesis confused a sufficient choice of splitter with a
necessary one. Reducing its shift to 26, in contrast, violates the required
head precision and is retained as a numerical fault with the witness above.
