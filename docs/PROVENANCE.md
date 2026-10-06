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
- **Code from MorphIQ Labs' other repositories** without a provenance audit.
  Our own history isn't proof of independent origin.

## AI-assisted contributions

A language model trained on public code may have seen any of the implementations
listed above, and nobody can say which, which version, or what it retained. A
model-assisted change therefore can't make the disclosure that [Recording](#recording)
requires. Its rule depends on how much of the result the published mathematics
determines.

**May be model-assisted**, with the disclosure below:
- derivation documents, which cite only published mathematics;
- generators, test oracles and fixtures, proofs and certificates (Sollya, Gappa,
  Coq, Lean), gates, CI and documentation;
- library code for a **fully specified algorithm**, one whose cited source states
  it operation by operation, so that the code adds nothing but names, types and
  layout. Examples: the error-free transforms and published double-word
  algorithms, and integer generators defined bit for bit by their papers. The
  pull request cites the section of the source that determines each operation.

**May be model-assisted only from a complete derivation**: library code for any
function whose implementation involves design choices the mathematics leaves
open. These include:
- argument reduction schemes;
- table sizes and polynomial or rational degrees;
- the fast path's working precision;
- the rounding test;
- the structure of the accurate path.

The elementary functions, the normal family and the special functions are all in
this class. Their library code is written from the function's derivation
document, by a person or a model. A model may write it only once that document
fixes every choice above and its certificates bound every error, so that the
code follows the document step for step; the pull request cites the section
that determines each step, as for a fully specified algorithm. (Until
2026-10-05 this class had to be written by a person; the maintainer extended it
then, with the similarity gate below still required before the first such
function lands.)

**During the work,** a model must not be given, or retrieve, the source of any
implementation listed under [What may not be used](#what-may-not-be-used).

**The pull request discloses:**
- the tool and model used;
- which files are model-assisted;
- that no implementation was consulted during the work;
- for model-assisted library code, the source sections that determine it.

**Similarity gate.** Before the first function with open design choices lands, CI
gains a gate comparing the library's source, token by token, against the
implementations listed above. The comparison is mechanical, so nobody reads
them. The gate runs on every pull request from then on, whoever wrote the
change.

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
