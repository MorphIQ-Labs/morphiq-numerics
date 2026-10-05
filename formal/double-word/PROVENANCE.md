# Provenance of `formal/double-word`

The Coq development accompanying J.-M. Muller and L. Rideau, "Formalization of
double-word arithmetic, and comments on 'Tight and rigorous error bounds for basic
building blocks of double-word arithmetic'", *ACM TOMS* 48(1), 2022. It proves the
error bounds of Joldes, Muller and Popescu (*ACM TOMS* 44(2), 2017), with the
improvements of the 2022 paper.

| | |
|---|---|
| Source | `http://www-sop.inria.fr/members/Laurence.Rideau/DW_arithmetic-submitted_paper_release.zip`, the URL the paper gives (a gzipped tar archive despite the name) |
| Archive SHA-256 | `786ae0b8c0bb53c6df4ea9004a8722f04a7b329993aa6e068ebdd708bec498f7` |
| Retrieved | 2026-10-05 |
| License | MIT, copyright 2020 Jean-Michel Muller and Laurence Rideau (`LICENSE`, unchanged) |
| Changes | None: every file is as distributed |
| Checked with | Coq 8.15.2, Flocq 3.4.3, math-comp ssreflect 1.14.0 (`scripts/check_formal.sh`) |

The development is used as a proof artifact only; no library code is derived from
it. `docs/double-word.md` maps each theorem to the library function it covers.
