(** The complete positive extended-input evaluator used by the normal family.
    The table's absolute error becomes a relative bound using a positive lower
    bound for erfcx on [1/4,16]. The asymptotic branch has a tighter bound. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxAccurateTerms ErfcxConstants ErfcxGaussianTarget
  NormalErfcxIdentity NormalErfcxSensitivity NormalResidualGrid
  NormalExtendedTable NormalErfcxAsymptotic.
Open Scope R_scope.

Definition normal_q_sixteen := mul_pow2 q_one 4.
Lemma normal_q_sixteen_ok : valid normal_q_sixteen /\ qval normal_q_sixteen=16.
Proof.
  destruct q_one_ok as[Q Value];destruct(mul_pow2_any _ 4 Q)as[Sixteen E].
  split;[exact Sixteen|unfold normal_q_sixteen;rewrite E,Value;change(bpow radix2 4)with 16;ring].
Qed.

Definition normal_q_erfcx_positive x :=
  match cmp_abs x normal_q_sixteen with
  | Lt => normal_q_erfcx_extended_table x
  | _ => normal_q_erfcx_asymptotic x
  end.

Lemma normal_erfcx_table_lower x : 0<x<=16 -> /64<=gaussian_erfcx x.
Proof.
  intros X;pose proof(normal_erfcx_decreasing x 16 X)as Decreasing.
  pose proof(normal_erfcx_large_lower 16 ltac:(lra))as Lower.
  assert (Constant : /2<=inv_sqrt_pi)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
  lra.
Qed.

Theorem normal_q_erfcx_extended_table_relative x : valid x -> /4<=qval x<16 ->
  valid(normal_q_erfcx_extended_table x) /\ exists e,Rabs e<=bpow radix2 (-117) /\
  qval(normal_q_erfcx_extended_table x)=gaussian_erfcx(qval x)*(1+e).
Proof.
  intros X Range;destruct(normal_q_erfcx_extended_table_error x X Range)as[Result Error].
  pose proof(normal_erfcx_table_lower (qval x) ltac:(split;lra))as Lower.
  set(f:=gaussian_erfcx(qval x))in *.
  split;[exact Result|]. exists((qval(normal_q_erfcx_extended_table x)-f)/f);split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f)by lra.
    apply(Rmult_le_reg_r f);[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    assert (Budget : bpow radix2 (-123)=(/64)*bpow radix2 (-117))by(bpow_num;field).
    rewrite Budget in Error;pose proof(bpow_gt_0 radix2 (-117));nra.
  - field;lra.
Qed.

Theorem normal_q_erfcx_positive_error x : valid x -> /4<=qval x<=3*bpow radix2 1022 ->
  valid(normal_q_erfcx_positive x) /\ exists e,Rabs e<=bpow radix2 (-117) /\
  qval(normal_q_erfcx_positive x)=gaussian_erfcx(qval x)*(1+e).
Proof.
  intros X Range;destruct normal_q_sixteen_ok as[Sixteen Value].
  pose proof(normal_q_compare_abs x normal_q_sixteen X Sixteen)as Compare.
  rewrite Value,(Rabs_pos_eq 16),(Rabs_pos_eq(qval x))in Compare by lra.
  assert (Asym : 16<=qval x ->
    valid(normal_q_erfcx_asymptotic x) /\ exists e,Rabs e<=bpow radix2 (-117) /\
    qval(normal_q_erfcx_asymptotic x)=gaussian_erfcx(qval x)*(1+e)).
  { intros Large;destruct(normal_q_erfcx_asymptotic_error x X ltac:(split;lra))as[Result [e [E V]]].
    split;[exact Result|]. exists e;split.
    - eapply Rle_trans;[exact E|apply bpow_le;lia].
    - rewrite positive_erfcx_gaussian in V by lra;exact V. }
  unfold normal_q_erfcx_positive;destruct(cmp_abs x normal_q_sixteen).
  - apply Asym;lra.
  - apply normal_q_erfcx_extended_table_relative;[exact X|split;lra].
  - apply Asym;lra.
Qed.
