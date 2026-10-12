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
