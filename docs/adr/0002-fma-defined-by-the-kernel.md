# Fused multiply-add is defined by the kernel

## Decision

A kernel's specified operation sequence may contain explicit fused
multiply-adds. IEEE 754 requires a fused multiply-add to be correctly rounded,
so each one returns the same bits on every conforming target, and the library
keeps its promise of identical results everywhere. What varies by target is
only how the operation executes:

- **Hardware** where the build or the processor provides it: always on
  aarch64; at compile time in builds that target FMA (for example
  x86-64-v3); and on generic x86-64 with the `std` feature, through one
  runtime dispatch per kernel body into an FMA-enabled monomorphization, as
  the bounded `ln` already does for its residual.
- **A proved, correctly rounded software FMA** everywhere else: `no_std`
  embedded targets, wasm32 and x86-64 processors without FMA. It is slower
  there, and the slowdown is stated for each kernel that adopts FMA. It never
  calls `f64::mul_add` or any platform library.

Implicit contraction stays forbidden: a fused multiply-add appears only where
the kernel's derivation names it, and every other operation keeps its separate
rounding. A kernel must never have different operation sequences, and so
different results, on different targets.

## Why

The FMA-free rule kept target independence simple, but a growing set of
measured costs comes from it:

- The fast `exp`'s shortest proved chain is nine dependent operations, about
  5% behind glibc's FMA-based sequence on dependent latency on an i9-10920X.
  The coarse variant at relative `2^-38` exists partly to buy back that chain.
- A table-driven double-word exponential for Risk's implied-volatility path
  cuts the IV cells by 11–12% with fused products, but only 3–4% with Dekker's
  FMA-free product (#266).
- The scalar fast `ln` built with static FMA is at glibc parity (1.02), while
  its runtime-dispatch build is 1.25 of glibc. The difference is the per-call
  dispatch cost, not the arithmetic (#265, #260).

Fused multiply-add is deterministic; only using it on some targets and not
others is not. Defining it in the kernel removes that ambiguity rather than
the operation.

## Consequences

- An existing kernel moves to an FMA sequence only through a new derivation:
  certificates and Coq proofs over the new sequence, independent fixtures, a
  deliberate determinism-digest update, and measurement on a hardware-FMA host
  and on a host without it. The FMA-free sequence is not kept as a second
  result.
- The software FMA is delivered and proved with the first kernel that needs it.
  Boldo and Melquiond's emulation through rounding to odd is formally proved
  in Flocq, which the proofs already use.
- `scripts/check_fma.sh` keeps requiring byte-identical cross-check corpora
  between FMA and non-FMA builds. With FMA defined by the kernel, those builds
  differ in execution, never in specified operations.
- Clippy keeps denying `f64::mul_add`. Hardware FMA comes through
  `morphiq-numerics-arch` and the software fallback through this crate.
- Consumers on x86-64 who build for x86-64-v3 avoid the runtime dispatch
  entirely. Every aarch64 build, including the macOS reference host, gets
  hardware FMA without it.
- Adoption is kernel by kernel, where a profile shows the gain. The first
  candidates are the double-word exponential (#266) and the fast `exp`
  dependency chain (#260). This is not a crate-wide rewrite.
