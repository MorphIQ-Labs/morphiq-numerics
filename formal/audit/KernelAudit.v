(** The axiom audit of the kernels' proofs. They apply the Gappa certificates'
    theorems, which scripts/check_formal.sh builds from the certificates where
    it checks them, so they are audited after those, here; the script requires
    their global axioms to be among formal/axioms.expected. *)

Require ExpReduction.

Print Assumptions ExpReduction.reduce_ok.
