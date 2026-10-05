# Determinism digest

Every function returns the same bits on every target. The digest makes that
claim checkable: one SHA-256 over the output bits of every public function on a
fixed corpus, compared with the value committed in
`crates/reference/determinism.sha256`.

## The corpus

`crates/digest/src/lib.rs` builds the corpus from integers only (a
seeded xorshift and literal bit patterns), so the inputs are identical
everywhere. Each section is labelled in the hash, so an output can't move between
functions unnoticed.

| Section | Inputs | Outputs hashed |
|---|---|---|
| `ulp` | NaN, ±0, ±∞, ±max finite, every binade's least and greatest encoding, 20,000 random encodings | `ulp`, `ordered_bits`, and `ulps_between` of neighbours |
| `eft` | 20,000 pairs with exponents in `[−500, 500]` | `two_sum`, `fast_two_sum` (larger operand first), `two_prod` |
| `double_word` | 20,000 triples of double-word and binary64 operands | every double-word operation, and `DoubleWord::product` |
| `reduce` | slices of every length from 0 to 32, exponents in `[−100, 100]`, mixed signs; one slice holding a NaN | `sum`, `sum2`, `dot`, `dot2`, `sum_squares`, `sum_squares2`, `max_abs` |
| `random` | four seeds | 4,096 words of each stream, both uniforms of each SplitMix64 word, and a word after `jump` and after `long_jump` |

## Where it is checked

The test `every_output_matches_the_committed_digest` runs:
- in the `test` job on x86-64 Linux, aarch64 Linux, aarch64 macOS and x86-64
  Windows;
- in the `digest` job:
  - on x86-64 Linux with musl (`x86_64-unknown-linux-musl`);
  - on WebAssembly (`wasm32-wasip1`, under the wasmtime pinned in
    `.cargo/wasmtime-version` and checked against `.cargo/wasmtime-sha256`);
  - on bare metal (`thumbv7em-none-eabihf`), from reset on QEMU's `mps2-an386`
    Cortex-M4F. That FPU is single-precision only, so every binary64 operation
    there runs in the compiler's software floating point: a different arithmetic
    path that must still give the same bits.

The corpus lives in the `no_std`, allocation-free `crates/digest`, so every
target computes the same one. `crates/digest-embedded` runs it on bare metal,
printing over semihosting and exiting with the comparison's status.

`scripts/check_digest_target.sh TARGET` runs the same check locally.

## Changing it

A change that alters any output fails the test, which prints the new digest.
- **If the change is wrong,** fix the change.
- **If it is deliberate** (a function corrected, or the corpus extended), update
  `crates/reference/determinism.sha256` in the same pull request and give the
  reason there. The new value must then pass on every target, which is the
  determinism claim itself.
