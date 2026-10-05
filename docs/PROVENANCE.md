# Source provenance policy

Everything in this repository is distributed under MIT OR Apache-2.0. That is
only possible if every algorithm, constant and coefficient here is ours to
license. This policy applies to every change, from the first commit. A change
that doesn't follow it is a defect, however well it tests.

## What may be used

- **Mathematical definitions and published mathematics:** identities,
  series, continued fractions, error analyses, theorems and worst-case
  results, cited to the paper or book. An idea or a mathematical fact isn't an
  implementation.
- **Values we generate:** coefficients, constants and tables produced by a
  generator in `generators/` from the mathematical definition. They must use
  pinned tools (Sollya, mpmath) at a recorded precision, and CI must reproduce
  them.
- **Test oracles:** tools used as black boxes, such as MPFR through `rug` and
  mpmath, in test and tooling crates that are never published. Their outputs
  check our results; their source isn't read to write ours.
- **Published worst-case data:** hardest-to-round arguments from the
  literature, recorded with their citation and used as test inputs and as
  inputs to bound arguments.

## What may not be used

- **Code, coefficient tables or implementation structure taken from another
  implementation.** That includes libm (glibc, musl, FreeBSD/fdlibm,
  Apple), CORE-MATH, CRlibm, SLEEF, Cephes, Netlib SPECFUN (Cody), StatLib
  (AS241), QD and Boost. Permissively licensed code is no exception: adopting
  one needs its own recorded rights review and a decision in this file.
- **Renaming, reordering or re-deriving an adapted algorithm** to present it
  as new. Citing a paper doesn't cancel having consulted an implementation.
- **Code from MorphIQ Labs' private repositories** (for example FerroRisk's
  numerics) without a provenance audit. Our own history isn't proof of
  independent origin; FerroRisk's normal kernels follow Cody and AS241.

## Recording

Each derivation document in `docs/` names the mathematics it uses (with
citations) and the generator that produced its constants. If a contributor
consulted any implementation while working on a function, the pull request
says which one, which version, and what was read. That function's derivation
then has to show it didn't take that implementation's structure, or the
function is redone by someone who didn't read it.

## Third-party notices

Published dependencies of the library crate: none. The test and tooling crates'
licenses are checked by `cargo-deny` against the allowlist in `deny.toml`. MPFR
(LGPL) is a test-only oracle in an unpublished crate and is never distributed
with the library.
