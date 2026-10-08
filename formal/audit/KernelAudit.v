(** The axiom audit of the kernels' proofs. They apply the Gappa certificates'
    theorems, which scripts/check_formal.sh builds from the certificates where
    it checks them, so they are audited after those, here; the script requires
    their global axioms to be among formal/axioms.expected and, for the
    constants CoqInterval proves, formal/axioms.int63.expected. *)

Require ExpTables ExpReduction ExpFast ExpAccurate ExpSmall.

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
