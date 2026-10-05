# Determinism digest

Every function returns the same bits on every target. The digest makes that
claim checkable: one SHA-256 over the output bits of every public function on a
fixed corpus, compared with the value committed in
`crates/reference/determinism.sha256`.

## The corpus

`crates/reference/src/determinism.rs` builds the corpus from integers only (a
seeded xorshift and literal bit patterns), so the inputs are identical
everywhere. Each section is labelled in the hash, so an output can't move between
functions unnoticed.

| Section | Inputs | Outputs hashed |
|---|---|---|
| `ulp` | NaN, ±0, ±∞, ±max finite, every binade's least and greatest encoding, 20,000 random encodings | `ulp`, `ordered_bits`, and `ulps_between` of neighbours |
| `eft` | 20,000 pairs with exponents in `[−500, 500]` | `two_sum`, `fast_two_sum` (larger operand first), `two_prod` |
| `double_word` | 20,000 triples of double-word and binary64 operands | every double-word operation, and `DoubleWord::product` |
| `random` | four seeds | 4,096 words of each stream, both uniforms of each SplitMix64 word, and a word after `jump` and after `long_jump` |

## Where it is checked

The test `every_output_matches_the_committed_digest` runs in the `test` job on
x86-64 Linux, aarch64 Linux, aarch64 macOS and x86-64 Windows.

Not yet checked: musl, `wasm32` and a `no_std` embedded target, which the plan
also lists. Each needs a CI job of its own, added as a required check in the
same change.

## Changing it

A change that alters any output fails the test, which prints the new digest.
- **If the change is wrong,** fix the change.
- **If it is deliberate** (a function corrected, or the corpus extended), update
  `crates/reference/determinism.sha256` in the same pull request and give the
  reason there. The new value must then pass on every target, which is the
  determinism claim itself.
