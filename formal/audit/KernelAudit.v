(** The axiom audit of the kernels' proofs. They apply the Gappa certificates'
    theorems, which scripts/check_formal.sh builds from the certificates where
    it checks them, so they are audited after those, here; the script requires
    their global axioms to be among formal/axioms.expected and, for the
    constants CoqInterval proves, formal/axioms.int63.expected. *)

Require ExpTables ExpReduction ExpFast ExpAccurate ExpSmall LnTables LnTableCheck LnReduction LnAccurate.
Require TableCheck ExpStageTables ExpStageReduction ExpStageA ExpStageB.
Require Ln1pTables Ln1pApprox Ln1pReduction Ln1pTest Ln1pStageH Ln1pStageB Ln1pScreen Ln1p.

Print Assumptions ExpTables.exp_l_split.
Print Assumptions ExpTables.exp_poly_approx.
Print Assumptions ExpTables.exp_table_ok.
Print Assumptions ExpTables.exp_tq_table_ok.
Print Assumptions ExpTables.exp_recip_table_ok.
Print Assumptions ExpReduction.reduce_ok.
Print Assumptions ExpFast.fast_ok.
Print Assumptions ExpFast.exp_fast_ok.
Print Assumptions ExpAccurate.accurate_bound.
Print Assumptions ExpAccurate.accurate_ok.
Print Assumptions ExpAccurate.exp_accurate_ok.
Print Assumptions ExpSmall.small_parts_ok.
Print Assumptions ExpSmall.exp_small_ok.
Print Assumptions TableCheck.table_check_ok.
Print Assumptions ExpStageTables.st_inv_close.
Print Assumptions ExpStageTables.st_l_split.
Print Assumptions ExpStageTables.st_l_split_d.
Print Assumptions ExpStageTables.st_poly_approx.
Print Assumptions ExpStageTables.st_t_ok.
Print Assumptions ExpStageReduction.stage_of_ok.
Print Assumptions ExpStageReduction.stage_a_r_ok.
Print Assumptions ExpStageReduction.stage_b_r_ok.
Print Assumptions ExpStageA.stage_a_value_ok.
Print Assumptions ExpStageA.exp_stage_a_ok.
Print Assumptions ExpStageB.stage_b_value_ok.
Print Assumptions ExpStageB.exp_stage_b_ok.
Print Assumptions ExpStageB.screen_ok.
Print Assumptions ExpStageB.exp_stages_ok.
Print Assumptions LnTables.ln_r_table_ok.
Print Assumptions LnReduction.reduce_ok.
Print Assumptions LnReduction.z_ok.
Print Assumptions LnReduction.z_exact_ok.
Print Assumptions LnTableCheck.neg_ln_r_q_ok.
Print Assumptions LnTableCheck.ln2_q_ok.
Print Assumptions LnTableCheck.recip_q_ok.
Print Assumptions LnTableCheck.ratios_ok.
Print Assumptions LnTableCheck.ln_r_one.
Print Assumptions LnAccurate.series_ok.
Print Assumptions LnAccurate.acc_value_ok.
Print Assumptions LnAccurate.ln_acc_ok.
Print Assumptions LnAccurate.ln_accurate_ok.
Print Assumptions LnAccurate.ln_1p_acc_ok.
Print Assumptions LnAccurate.rounds_as.
Print Assumptions Ln1pTables.st_rt_check.
Print Assumptions Ln1pTables.st_l_check.
Print Assumptions Ln1pApprox.h_approx.
Print Assumptions Ln1pApprox.b_approx.
Print Assumptions Ln1pReduction.split_ok.
Print Assumptions Ln1pReduction.reduce_ok.
Print Assumptions Ln1pTest.decide_ok.
Print Assumptions Ln1pStageH.stage_h_ok.
Print Assumptions Ln1pStageB.stage_b_ok.
Print Assumptions Ln1p.ln_1p_stage_h_bits.
Print Assumptions Ln1p.ln_1p_stage_b_bits.
Print Assumptions Ln1pScreen.h_screen_ok.
Print Assumptions Ln1pScreen.b_screen_ok.
Print Assumptions Ln1p.ln_1p_stages_ok.

Require LnStage.
Print Assumptions LnStage.ln_stage_ok.
Print Assumptions LnStage.ln_stage_accurate_value.

Require Exp2Stages Expm1Stages.
Print Assumptions Exp2Stages.exp2_stages_ok.
Print Assumptions Expm1Stages.expm1_stages_ok.

Require Exp2FallbackReduction Exp2FallbackAccurate.
Print Assumptions Exp2FallbackReduction.exp2_fallback_reduce_ok.
Print Assumptions Exp2FallbackAccurate.exp2_qproduct_ok.
Print Assumptions Exp2FallbackAccurate.exp2_fallback_accurate_bound.

Require Exp2Range Exp2FallbackProduct Exp2FallbackFast Exp2Fallback Exp2Thresholds Exp2.
Print Assumptions ExpFast.fast_reduced_ok.
Print Assumptions ExpFast.fast_decide_scaled_ok.
Print Assumptions Exp2Range.exp2_below_overflow.
Print Assumptions Exp2FallbackProduct.exp2_dwproduct_ok.
Print Assumptions Exp2FallbackFast.exp2_fallback_fast_ok.
Print Assumptions Exp2Fallback.exp2_accurate_round_ok.
Print Assumptions Exp2Fallback.exp2_fallback_ok.
Print Assumptions Exp2Thresholds.exp2_round_one.
Print Assumptions Exp2Thresholds.exp2_underflow.
Print Assumptions Exp2.exp2_entry_finite.
Print Assumptions Exp2.exp2_entry_nan.
Print Assumptions Exp2.exp2_entry_infinities.
Print Assumptions Exp2.exp2_entry_zero.
Print Assumptions Exp2.exp2_entry_positive.
Print Assumptions Exp2.exp2_entry_signed_zeros.

Require Expm1GeneralReduction Expm1GeneralBounds Expm1GeneralScale Expm1GeneralSum Expm1GeneralSubtract Expm1GeneralFast Expm1GeneralAccurate.
Print Assumptions ExpFast.fast_reduced_grid_ok.
Print Assumptions Binary64.RoundingTest.decide_with_bounded_ok.
Print Assumptions Expm1GeneralReduction.em_reduce_ok.
Print Assumptions Expm1GeneralBounds.em_ratio_bounds.
Print Assumptions Expm1GeneralScale.em_scale_exact.
Print Assumptions Expm1GeneralSum.em_two_sum_large.
Print Assumptions Expm1GeneralSubtract.em_subtract_fast_ok.
Print Assumptions Expm1GeneralFast.em_general_fast_bound.
Print Assumptions Expm1GeneralFast.em_general_fast_ok.
Print Assumptions Expm1GeneralAccurate.em_general_accurate_bound.
Print Assumptions Expm1GeneralAccurate.em_general_accurate_round.

Require Expm1Series Expm1SmallAdd Expm1SmallSquare Expm1SmallApprox Expm1SmallFast Expm1SmallAccurate Expm1Thresholds Expm1.
Print Assumptions Expm1Series.exp_taylor_bound.
Print Assumptions Expm1SmallAdd.em_add_scalar_left.
Print Assumptions Expm1SmallSquare.em_half_square_ok.
Print Assumptions Expm1SmallApprox.em_small_polynomial_bound.
Print Assumptions Expm1SmallFast.em_small_fast_bound.
Print Assumptions Expm1SmallFast.em_small_fast_ok.
Print Assumptions Expm1SmallAccurate.em_small_accurate_bound.
Print Assumptions Expm1SmallAccurate.em_small_accurate_round.
Print Assumptions Expm1Thresholds.em_tiny_round.
Print Assumptions Expm1Thresholds.em_overflow_screen.
Print Assumptions Expm1Thresholds.em_minus_one_round.
Print Assumptions Expm1.expm1_entry_finite.
Print Assumptions Expm1.expm1_entry_nan.
Print Assumptions Expm1.expm1_entry_infinities.
Print Assumptions Expm1.expm1_entry_signed_zeros.

Require LnFastAdd LnFastApprox LnFastTableCheck LnFastKernel LnFastZero LnFastY LnFastValue.
Require Ln1pFastGeneral Ln1pFast LnFastDecision LnEntryLemmas LnEntry.
Print Assumptions LnFastAdd.lf_add_normalized.
Print Assumptions LnFastApprox.lf_polynomial_bound.
Print Assumptions LnFastTableCheck.lf_table_all.
Print Assumptions LnFastTableCheck.lf_ln2_error.
Print Assumptions LnFastKernel.lf_polynomial_ok.
Print Assumptions LnFastZero.lf_polynomial_zero.
Print Assumptions LnFastY.lf_ln_y_ok.
Print Assumptions LnFastValue.lf_ln_fast_value_ok.
Print Assumptions Ln1pFastGeneral.lf_ln1p_general_ok.
Print Assumptions Ln1pFast.lf_ln1p_fast_value_ok.
Print Assumptions LnFastDecision.lf_ln_fast_ok.
Print Assumptions LnFastDecision.lf_ln1p_fast_ok.
Print Assumptions LnEntryLemmas.lf_tiny_round.
Print Assumptions LnEntry.ln_entry_regular.
Print Assumptions LnEntry.ln1p_entry_regular.
Print Assumptions LnEntry.ln_entry_specials.
Print Assumptions LnEntry.ln1p_entry_specials.
Print Assumptions LnEntry.ln_entry_nan.
Print Assumptions LnEntry.ln1p_entry_nan.
Print Assumptions LnEntry.ln_entry_negative.
Print Assumptions LnEntry.ln1p_entry_below_domain.

Require ErfcxReciprocal.
Print Assumptions ErfcxReciprocal.reciprocal_ieee.

Require ErfcxSquare.
Print Assumptions ErfcxSquare.square_ieee.
Print Assumptions ErfcxSquare.reciprocal_square_ieee.

Require ErfcxMiddlePolynomial.
Print Assumptions ErfcxMiddlePolynomial.poly_ieee.
Print Assumptions ErfcxMiddlePolynomial.correction_ieee.
Print Assumptions ErfcxMiddlePolynomial.reciprocal_correction_ieee.

Require ErfcxProduct.
Print Assumptions ErfcxProduct.product_ieee.

Require ErfcxMiddleValue.
Print Assumptions ErfcxMiddleValue.middle_with_pi_ieee.

Require ErfcxQuotient ErfcxQuotientScale.
Print Assumptions ErfcxQuotient.quotient_ieee.
Print Assumptions ErfcxQuotient.normalized_quotient_ieee.
Print Assumptions ErfcxQuotientScale.scale_input_ieee.
Print Assumptions ErfcxQuotientScale.scaled_quotient_ieee.

Require ErfcxRounding ErfcxTailCorrection ErfcxTailValue.
Print Assumptions ErfcxRounding.rounding_decomposition.
Print Assumptions ErfcxTailCorrection.tail_correction_ieee.
Print Assumptions ErfcxTailValue.tail_reconstruct_ieee.
Print Assumptions ErfcxTailValue.tail_with_pi_ieee.
Print Assumptions ErfcxTailValue.scaled_tail_with_pi_ieee.

Require ErfcxTableSplit.
Print Assumptions ErfcxTableSplit.table_split_ieee.
Print Assumptions ErfcxTableSplit.table_square_ieee.

Require ErfcxTableCoefficient ErfcxTableProducts.
Print Assumptions ErfcxTableCoefficient.coefficient_check_ok.
Print Assumptions ErfcxTableProducts.table_leading_value_ieee.

Require ErfcxConstants.
Print Assumptions ErfcxConstants.cs_split_bound.

Require ErfcxTableReduction.
Print Assumptions ErfcxTableReduction.table_uniform_ieee.
Print Assumptions ErfcxTableReduction.table_binade_ieee.
Print Assumptions ErfcxTableReduction.table_reduce_ieee.

Require ErfcxTableEvaluation ErfcxTableEntry.
Print Assumptions ErfcxTableCoefficient.word_range_check_ok.
Print Assumptions ErfcxTableCoefficient.coefficient_size_check_ok.
Print Assumptions ErfcxTableEvaluation.horner_ieee.
Print Assumptions ErfcxTableEvaluation.table_rest_ieee.
Print Assumptions ErfcxTableEvaluation.table_sum_ieee.
Print Assumptions ErfcxTableEntry.table_eval_ieee.

Require ErfcxTableBound.
Print Assumptions ErfcxTableBound.table_evaluation_error.

Print Assumptions ExpStageReduction.stage_of_extended_ok.
Print Assumptions ExpStageReduction.stage_b_r_model.
Print Assumptions ExpStageB.stage_b_at_extended_ok.
Require ErfcxReflectionSquare ErfcxReflectionReduction ErfcxReflectionExp.
Print Assumptions ErfcxReflectionSquare.reflection_square_ieee.
Print Assumptions ErfcxReflectionReduction.reflection_reduced_ieee.
Print Assumptions ErfcxReflectionReduction.reflection_reduce_ieee.
Print Assumptions ErfcxReflectionExp.reflection_exp_ieee.
Print Assumptions ErfcxReflectionExp.reflection_square_exp_ieee.
Print Assumptions ErfcxReflectionExp.reflection_dispatch_range.

Require ErfcxReflectionScale ErfcxReflectionSubtract.
Print Assumptions ErfcxReflectionScale.reflection_scaled_word_ieee.
Print Assumptions ErfcxReflectionSubtract.reflection_subtract_ieee.

Require ErfcxReflectionValue.
Print Assumptions ErfcxReflectionExp.reflection_exp_ideal_range.
Print Assumptions ErfcxReflectionValue.reflection_value_ieee.

Require ErfcxDecision ErfcxReflectionOverflow ErfcxReflectionFast.
Print Assumptions ErfcxDecision.erfcx_decide_ieee.
Print Assumptions ErfcxDecision.erfcx_decide_scaled_normal_ieee.
Print Assumptions ErfcxReflectionOverflow.reflection_finite_magnitude.
Print Assumptions ErfcxReflectionOverflow.reflection_overflow_magnitude.
Print Assumptions ErfcxReflectionFast.reflection_fast_ieee.

Require ErfcxMiddleFast ErfcxTailFast.
Print Assumptions ErfcxProduct.product_normalized_ieee.
Print Assumptions ErfcxMiddleValue.middle_normalized_ieee.
Print Assumptions ErfcxTailValue.tail_reconstruct_normalized_ieee.
Print Assumptions ErfcxTailValue.tail_normalized_ieee.
Print Assumptions ErfcxMiddleFast.middle_fast_ieee.
Print Assumptions ErfcxTailFast.tail_unscaled_fast_ieee.

Require ErfcxSubnormal ErfcxSubnormalBits ErfcxSubnormalCandidate ErfcxSubnormalValue ErfcxSubnormalFast.
Print Assumptions ErfcxQuotient.normalized_quotient_words_ieee.
Print Assumptions ErfcxSubnormal.binary64_round_absolute.
Print Assumptions ErfcxSubnormal.subnormal_accept_ieee.
Print Assumptions ErfcxSubnormalBits.small_bits_value.
Print Assumptions ErfcxSubnormalBits.small_positive_encoding.
Print Assumptions ErfcxSubnormalCandidate.subnormal_candidate_ieee.
Print Assumptions ErfcxSubnormalCandidate.subnormal_fast_ieee.
Print Assumptions ErfcxSubnormalValue.subnormal_value_words_ieee.
Print Assumptions ErfcxSubnormalFast.tail_subnormal_fast_ieee.

Require ErfcxScaledWords ErfcxSubnormalBoundary ErfcxScaledFast.
Print Assumptions ErfcxScaledWords.scaled_quotient_words_ieee.
Print Assumptions ErfcxSubnormalBoundary.erfcx_normal_tail_lower.
Print Assumptions ErfcxScaledFast.tail_scaled_normal_fast_ieee.
Print Assumptions ErfcxScaledFast.tail_scaled_fast_ieee.

Require ErfcxTableFast.
Print Assumptions ErfcxTableEvaluation.table_sum_normalized_ieee.
Print Assumptions ErfcxTableEntry.table_polynomial_normalized_ieee.
Print Assumptions ErfcxTableEntry.table_eval_normalized_ieee.
Print Assumptions ErfcxTableFast.table_composed_error.
Print Assumptions ErfcxTableFast.table_fast_ieee.

Require ErfcxExpRemainder ErfcxMoments ErfcxTailIntegral ErfcxScaledAnalytic.
Print Assumptions ErfcxExpRemainder.exp_negative_taylor_remainder.
Print Assumptions ErfcxMoments.exponential_moment_integral_limit.
Print Assumptions ErfcxTailIntegral.tail_integral_limit.
Print Assumptions ErfcxTailIntegral.tail_integral_correction.
Print Assumptions ErfcxScaledAnalytic.scaled_tail_analytic_correction.
Print Assumptions ErfcxScaledAnalytic.tail_scaled_fast_analytic_ieee.

Require ErfcxAsymptotic ErfcxCubicAnalytic.
Print Assumptions ErfcxAsymptotic.moment_series_integral_limit.
Print Assumptions ErfcxAsymptotic.tail_integrand_signed_remainder.
Print Assumptions ErfcxAsymptotic.tail_integral_asymptotic.
Print Assumptions ErfcxCubicAnalytic.tail_cubic_remainder.
Print Assumptions ErfcxCubicAnalytic.tail_unscaled_fast_analytic_ieee.

Require ErfcxFactorial ErfcxMiddleApprox ErfcxMiddleRemainder ErfcxMiddleAnalytic.
Print Assumptions ErfcxFactorial.factorial_real_integer.
Print Assumptions ErfcxMiddleApprox.middle_polynomial_approx.
Print Assumptions ErfcxMiddleRemainder.middle_asymptotic_remainder.
Print Assumptions ErfcxMiddleAnalytic.middle_integral_contract.
Print Assumptions ErfcxMiddleAnalytic.middle_fast_analytic_ieee.

Require ErfcxAccurateReciprocal.
Print Assumptions ErfcxAccurateReciprocal.binary64_round_large_reciprocal.
Print Assumptions ErfcxAccurateReciprocal.accurate_reciprocal_seed_ieee.

From Q Require Q256Real.
Require ErfcxAccurateSeries.
Print Assumptions Q256Real.new_valid.
Print Assumptions Q256Real.from_f64_valid.
Print Assumptions Q256Real.neg_any.
Print Assumptions Q256Real.add_any.
Print Assumptions Q256Real.mul_any.
Print Assumptions Q256Real.mul_relative.
Print Assumptions ErfcxAccurateSeries.asym_term_step.
Print Assumptions ErfcxAccurateSeries.accurate_series_remainder.
Print Assumptions ErfcxAccurateSeries.accurate_series_cap_remainder.
Print Assumptions ErfcxAccurateSeries.accurate_series_stopped_remainder.

Require ErfcxAccurateTerms.
Print Assumptions Q256Real.top_small.
Print Assumptions Q256Real.mul_pow2_any.
Print Assumptions ErfcxAccurateTerms.q_asym_term_error.
Print Assumptions ErfcxAccurateTerms.q_asym_stop_remainder.
