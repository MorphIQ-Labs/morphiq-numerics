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
| Changes | Two, both below; every other line is as distributed |
| Checked with | Coq 8.15.2, Flocq 3.4.3, math-comp ssreflect 1.14.0 (`scripts/check_formal.sh`) |

The development is used as a proof artifact only; no library code is derived from
it. `docs/double-word.md` maps each theorem to the library function it covers.

## Changes

Two premises of the distributed multiplicative theorems couldn't be met, which
made those theorems vacuous: they held, but applied to nothing.

1. **The exact-product premise quantified over all reals.** `F2Mult_correct`
   (`DWTimesFP.v`) and `Fast2Mult_correct` (`DWTimesDW.v`,
   `DWTimesDW_original.v`, `DWDivFP.v`, `DWDivDW.v`) asserted
   `a · b = RN(a · b) + RN(a · b − RN(a · b))` for every real `a` and `b`. That is
   false: at `b = 1`, `a = 1 + 2^−200 + 2^−400` it gives `1 + 2^−200`. It is true
   for binary64 `a` and `b`, which is the only case the proofs use. Each premise
   now carries `format a -> format b ->`. Its uses supply the two format facts
   (`DWTimesFP.v` twice, `DWDivFP.v` twice); `DWDivDW.v`'s `DWTimesFP_0_r` no
   longer uses it.
2. **`TwoProd` was a global axiom.** `DWTimesFP.v` declared
   `Parameter TwoProd : R -> R -> R * R` and the theorems assumed
   `TwoProd = Fast2Mult`, which nothing could prove about an uninterpreted
   constant. `TwoProd` is now `Fast2Mult` behind an opaque proof
   (`TwoProd_exists`), so it doesn't unfold in the proofs, as before, and
   `TwoProd_Fast2Mult` proves the equation. The other files refer to it
   through a local notation `TwoProd := (TwoProd p choice)`.

No proof step changed otherwise, and no bound changed.
`formal/binary64/Instances.v` instantiates the four multiplicative theorems at
precision 53 with every premise discharged, and the axiom audit covers them.
