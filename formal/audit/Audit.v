(** The axiom audit: every theorem the library relies on, and what it assumes.
    Section hypotheses (an exact product, the precision bound, the double-word
    inputs) are arguments of these theorems, not axioms; only global axioms are
    listed. scripts/check_formal.sh requires them to be exactly
    formal/axioms.expected:
    - Coq's classical reals: [sig_not_dec], [sig_forall_dec],
      [functional_extensionality_dep], [classic].
    - [TwoProd] (DWTimesFP.v), which the vendored development declares with
      [Parameter] inside a section, making it a global axiom. It is an
      uninterpreted constant of the inhabited type [R -> R -> R * R], so it
      can't make the logic inconsistent, and every theorem that uses it
      also assumes [TwoProd = Fast2Mult]: in effect it is a parameter. *)

From Double Require Import DWPlus DWTimesFP DWTimesDW DWDivFP DWDivDW.
Require Import TwoProdBinary64.
From Binary64 Require Binary64Add.

Print Assumptions DWPlusFP_correct.
Print Assumptions DWPlusDW_relerr_bound.
Print Assumptions DWTimesFP_correct.
Print Assumptions DWTimesDW1_correct_even.
Print Assumptions DWDFP3_correct.
Print Assumptions DWDDW_correct.
Print Assumptions two_prod_exact.
Print Assumptions Binary64Add.add_f64_bound.
Print Assumptions Binary64Add.add_bound.
Print Assumptions Binary64Add.sub_bound.
