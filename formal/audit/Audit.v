(** The axiom audit: every theorem the library relies on, and what it assumes.
    Section hypotheses (an exact product, the precision bound, the double-word
    inputs) are arguments of these theorems, not axioms; only global axioms are
    listed. scripts/check_formal.sh requires them to be exactly
    formal/axioms.expected, Coq's classical reals. The vendored multiplicative
    theorems are audited with their premises open; their instances in
    formal/binary64/Instances.v discharge every premise. *)

From Double Require Import DWPlus DWTimesFP DWTimesDW DWDivFP DWDivDW.
Require Import TwoProdBinary64.
From Binary64 Require Binary64Add Instances Binary64Mul Binary64Div.
From Binary64 Require IEEE64Add IEEE64Mul IEEE64Div IEEE64Eft IEEE64Sqrt.
From Binary64 Require Isqrt SqrtAlgorithm.

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
Print Assumptions Instances.mul_f64_bound.
Print Assumptions Instances.mul_bound.
Print Assumptions Instances.div_f64_bound.
Print Assumptions Instances.div_bound.
Print Assumptions Binary64Mul.mul_f64_bound.
Print Assumptions Binary64Mul.mul_bound.
Print Assumptions Binary64Div.div_f64_bound.
Print Assumptions Binary64Div.div_bound.
Print Assumptions IEEE64Add.add_f64_ieee.
Print Assumptions IEEE64Add.add_ieee.
Print Assumptions IEEE64Add.sub_ieee.
Print Assumptions IEEE64Mul.mul_f64_ieee.
Print Assumptions IEEE64Mul.mul_ieee.
Print Assumptions IEEE64Div.div_f64_ieee.
Print Assumptions IEEE64Div.div_ieee.
Print Assumptions IEEE64Eft.two_sum_ieee.
Print Assumptions IEEE64Eft.fast_two_sum_ieee.
Print Assumptions IEEE64Sqrt.sqrt_ieee.
Print Assumptions Isqrt.isqrt_correct.
Print Assumptions SqrtAlgorithm.sqrt_rs_ieee.
Print Assumptions IEEE64Eft.two_prod_ieee.
