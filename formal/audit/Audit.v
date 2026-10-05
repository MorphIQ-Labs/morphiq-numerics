(** The axiom audit: every theorem the library relies on, and what it assumes.
    Section hypotheses (an exact 2Prod, the precision bound, the double-word
    inputs) are arguments of these theorems, not axioms; only global axioms are
    listed. scripts/check_formal.sh requires them to be among
    formal/axioms.expected. *)

From Double Require Import DWPlus DWTimesFP DWTimesDW DWDivFP DWDivDW.
Require Import TwoProdBinary64.

Print Assumptions DWPlusFP_correct.
Print Assumptions DWPlusDW_relerr_bound.
Print Assumptions DWTimesFP_correct.
Print Assumptions DWTimesDW1_correct_even.
Print Assumptions DWDFP3_correct.
Print Assumptions DWDDW_correct.
Print Assumptions two_prod_exact.
