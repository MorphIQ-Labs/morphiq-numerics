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
From Binary64 Require Isqrt SqrtAlgorithm RoundingTest RoundingConstant.
From Q Require Q128 Q256.

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
Print Assumptions RoundingTest.decide_with_ok.
Print Assumptions RoundingTest.decide_scaled_ok.
Print Assumptions RoundingConstant.const_test_real.
Print Assumptions RoundingConstant.decide_const_ok.
Print Assumptions Q128.mul_value.
Print Assumptions Q128.add_ok.
Print Assumptions Q128.to_f64_ok.
Print Assumptions Q128.from_f64_ok.
Print Assumptions Q128.neg_ok.
Print Assumptions Q128.mul_pow2_ok.
Print Assumptions Q256.mul_value.
Print Assumptions Q256.add_ok.
Print Assumptions Q256.to_f64_ok.
Print Assumptions Q256.from_f64_ok.
Print Assumptions Q256.from_limbs_ok.
Print Assumptions Q256.neg_ok.
Print Assumptions IEEE64Eft.two_prod_ieee.

From Binary64 Require FiniteInterval.
Print Assumptions FiniteInterval.neighbour_enclosure.
Print Assumptions FiniteInterval.monotone_enclosure.
Print Assumptions FiniteInterval.add_enclosure.
Print Assumptions FiniteInterval.sub_enclosure.
Print Assumptions FiniteInterval.negate_enclosure.
Print Assumptions FiniteInterval.product_corners.
Print Assumptions FiniteInterval.reciprocal_enclosure.
Print Assumptions FiniteInterval.nonnegative_clamp.
Print Assumptions FiniteInterval.abs_positive.
Print Assumptions FiniteInterval.abs_negative.
Print Assumptions FiniteInterval.abs_crossing.
Print Assumptions FiniteInterval.max_enclosure.
Print Assumptions FiniteInterval.square_enclosure.
Print Assumptions FiniteInterval.exp_enclosure.
Print Assumptions FiniteInterval.sqrt_enclosure.
Print Assumptions FiniteInterval.ln_enclosure.

From Binary64 Require Tridiagonal.
Print Assumptions Tridiagonal.margin_step.
Print Assumptions Tridiagonal.dominant_row.
Print Assumptions Tridiagonal.finite_abs_max.
Print Assumptions Tridiagonal.tridiagonal_error_bound.
Print Assumptions Tridiagonal.tridiagonal_zero_kernel.
Print Assumptions Tridiagonal.rounded_error_bound.

Print Assumptions Tridiagonal.sign_rounded_zero.
Print Assumptions Tridiagonal.sign_rounded_monotone.
Print Assumptions Tridiagonal.sign_rounded_nonnegative.
Print Assumptions Tridiagonal.sign_rounded_nonpositive.
Print Assumptions Tridiagonal.sign_normalized_product.
Print Assumptions Tridiagonal.sign_rounded_pivot_step.
Print Assumptions Tridiagonal.sign_exact_pivots_positive.
Print Assumptions Tridiagonal.sign_finite_pivots_positive.
Print Assumptions Tridiagonal.sign_continuants_positive.
