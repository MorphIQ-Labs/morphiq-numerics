# Source provenance policy

Everything in this repository is distributed under MIT OR Apache-2.0. Code may
come from anywhere, provided it lives in this repository, where it can be
modified, and can be distributed under those terms. This policy applies to
every change. A change that doesn't follow it is a defect, however well it
tests.

## What may be used

- **Mathematical definitions and published mathematics:** identities,
  series, continued fractions, error analyses, theorems and worst-case
  results, cited to the paper or book.
- **Values we generate:** coefficients, constants and tables produced by a
  generator in `generators/` from the mathematical definition. They must use
  pinned tools (Sollya, mpmath) at a recorded precision, and CI must reproduce
  them.
- **Third-party code under a compatible license,** vendored into this
  repository. A compatible license lets the code ship inside an MIT OR
  Apache-2.0 crate with no condition beyond keeping its notices: MIT,
  BSD-2-Clause, BSD-3-Clause, ISC, Zlib, Apache-2.0 and BSL-1.0, and the Sun
  notice of fdlibm-derived code.
  - Examples: musl, FreeBSD's msun (fdlibm), CORE-MATH, SLEEF, QD and
    Boost.Math, each under its own license.
  - It is recorded as [Recording](#recording) describes, its notices travel
    with it, and it then meets the same standards as code written here: a
    document stating what it computes and its error bound, and the tests and
    evidence that support them. Correct rounding is claimed only where shown.
- **Test oracles:** tools used as black boxes, such as MPFR through `rug` and
  mpmath, in test and tooling crates that are never published.
- **Published worst-case data:** hardest-to-round arguments from the
  literature, recorded with their citation and used as test inputs and as
  inputs to bound arguments.

## What may not be used

- **Code under a copyleft license:** GPL, LGPL, AGPL, MPL, EPL, APSL and the
  like. Distributing it would bind this crate and its users to those terms.
  Examples: glibc and CRlibm (LGPL), Apple's Libm (APSL).
- **Code with no license or unclear terms,** such as Cephes, until its terms
  are recorded and shown compatible. Netlib SPECFUN (Cody) and StatLib (AS241)
  need that record too before any use.
- **A disguised copy of either:** renamed, reordered or re-derived. It is the
  same code.
- **Code from MorphIQ Labs' other repositories** whose own origin fails this
  policy. Code we wrote ourselves is fine; an in-house kernel derived from
  Cephes is not.

## AI-assisted contributions

A model may write any part of this repository, library code included. The
work meets the same standards as any other change: derivation documents for
the functions, generated constants, certificates for the bounds, and tests.

**During the work,** a model must not be given, or retrieve, the source of a
copyleft or unclear-license implementation, so it can't reproduce it.
Compatible source may be given to it; whatever it takes from that source is
third-party code, recorded and noticed as below.

**The pull request discloses:**
- the tool and model used;
- which files are model-assisted;
- which implementations, if any, were consulted, and what was taken from each.

## Recording

- **Derivations.** Each derivation document in `docs/` names the mathematics it
  uses, with citations, and the generator that produced its constants.
- **Vendored code.** `THIRD_PARTY_NOTICES.md`, shipped with the library crate,
  records for each source:
  - the project and its exact version (tag or commit);
  - where it was obtained, and the SHA-256 of what was taken;
  - its license, with the license text and the copyright notices;
  - the files here derived from it, and how they were changed.

  The derived files also keep the original's notices in their headers.
- **Consultation.** A contributor who consulted a copyleft or unclear-license
  implementation while working on a function says so in the pull request: which
  one, which version, and what was read. That function's code is then written
  by someone who didn't read it.

## Third-party notices

No third-party code is vendored yet, so `THIRD_PARTY_NOTICES.md` doesn't exist.
The first vendored source adds it, and the repository-hygiene gate's license
check extends to it then.

Published dependencies of the library crate: none. The test and tooling crates'
licenses are checked by `cargo-deny` against the allowlist in `deny.toml`. MPFR
(LGPL) is a test-only oracle in an unpublished crate and is never distributed
with the library.
