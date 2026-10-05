Formalisation in Coq of the paper "Tight and rigourous error bounds for basic building blocks of double-word arithmetic" https://hal.inria.fr/hal-01351529v3 by M. Joldes , JM Muller and V. Popescu

The proofs in this development contain improvements in bounds as described in paper 'Formalization of double-word arithmetic, and comments on "Tight and rigourous error bounds for basic building blocks of double-word arithmetic".

To find a correspondance between theorems of the paper and formal proofs, readers should look for the name of algorithms in the sources.  for instance, Algorithm DWTimesDW3 appears in a comment in file DWTimesDW, just before a lemma statement that gives the formally proved bound for this algorithm.


# building

If `opam` is installed on your machine, you simply need to execute the following command

<code>
opam switch create sandbox ocaml-base-compiler.4.09.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ./coq-double-double-arithmetic.opam
eval $(opam env)
</code>

Compilation can take a few tens of minutes.

Then you will be able to use the development in Coq by a session of the
following form:

<code>
Require Import Reals ZArith Flocq.
From Flocq Require Import Core Relative Sterbenz Operations
   Plus_error Mult_error.
From Double Require Import DWPlus DWDivDW DWDivFP DWTimesDW DWTimesFP.

(* Correctness of the algorithm named DWTimesDW3 in the paper
   as confirmed by a comment in the file DWTimesDW.  *)
Check DWTimesDW12_correct.
</code>
