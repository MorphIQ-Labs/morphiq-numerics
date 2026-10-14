(** Accurate CDF and centered-CDF complements outside the central interval.
    The tail bound includes its scaling, table/asymptotic dispatch and product. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTerms ErfcxAccurateSquare
  NormalTailAnalytic NormalTailRange NormalAccurateTailFull NormalAccurateRounding.
Open Scope R_scope.

Theorem normal_q_outer_tail_range x : finite x -> /2<=B x<=38.6 ->
  0<qval(normal_q_tail x)<=/2.
Proof.
  intros F X;destruct(normal_q_tail_error x F X)as[_ [e [E Value]]].
  pose proof(normal_tail_outer_range(B x)(proj1 X))as Target.
  apply Rabs_le_inv in E;assert(bpow radix2 (-115)<=/4)by(interval with(i_prec 80)).
  rewrite Value;split;nra.
Qed.

Definition normal_q_outer_complement constant x := add constant (neg_q(normal_q_tail x)).

Theorem normal_q_outer_complement_error constant x c : valid constant -> qval constant=c ->
  /2<=c<=1 -> finite x -> /2<=B x<=38.6 ->
  valid(normal_q_outer_complement constant x) /\ exists e,Rabs e<=bpow radix2 (-112) /\
  qval(normal_q_outer_complement constant x)=(c-normal_tail(B x))*(1+e).
Proof.
  intros C Cvalue Crange F X;destruct(normal_q_tail_error x F X)as[T [et [ET Tvalue]]].
  pose proof(normal_tail_outer_range(B x)(proj1 X))as Target.
  pose proof(normal_q_outer_tail_range x F X)as TailRange.
  destruct(neg_any _ T)as[NT NTvalue];destruct(add_any _ _ C NT)as[Result Addition].
  assert (AddError : Rabs(qval(normal_q_outer_complement constant x)-(c-qval(normal_q_tail x)))<=bpow radix2 (-254)).
  { unfold normal_q_outer_complement;rewrite Cvalue,NTvalue in Addition.
    eapply Rle_trans;[exact Addition|].
    rewrite(Rabs_pos_eq c),Rabs_Ropp,(Rabs_pos_eq(qval(normal_q_tail x)))by lra.
    replace(bpow radix2 (-254))with(bpow radix2 (-254)*1)at 2 by ring.
    apply Rmult_le_compat_l;[apply bpow_ge_0|apply Rmax_lub;lra]. }
  assert (TailError : Rabs(qval(normal_q_tail x)-normal_tail(B x))<=bpow radix2 (-116)).
  { rewrite Tvalue;replace(normal_tail(B x)*(1+et)-normal_tail(B x))with(normal_tail(B x)*et)by ring.
    rewrite Rabs_mult,(Rabs_pos_eq(normal_tail(B x)))by lra.
    replace(bpow radix2 (-116))with((/2)*bpow radix2 (-115))by(bpow_num;field).
    apply Rmult_le_compat;[lra|apply Rabs_pos|lra|exact ET]. }
  assert (Absolute : Rabs(qval(normal_q_outer_complement constant x)-(c-normal_tail(B x)))<=bpow radix2 (-115)).
  { replace(qval(normal_q_outer_complement constant x)-(c-normal_tail(B x)))with
      ((qval(normal_q_outer_complement constant x)-(c-qval(normal_q_tail x)))+
        -(qval(normal_q_tail x)-normal_tail(B x)))by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp.
    assert(bpow radix2 (-254)+bpow radix2 (-116)<=bpow radix2 (-115))by(interval with(i_prec 300));lra. }
  split;[exact Result|];exists((qval(normal_q_outer_complement constant x)-(c-normal_tail(B x)))/(c-normal_tail(B x)));split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(c-normal_tail(B x)))by lra.
    apply(Rmult_le_reg_r(c-normal_tail(B x)));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    replace(bpow radix2 (-115))with((/8)*bpow radix2 (-112))in Absolute by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-112));nra.
  - field;lra.
Qed.

Theorem normal_q_outer_complement_rounded constant x c : valid constant -> qval constant=c ->
  /2<=c<=1 -> finite x -> /2<=B x<=38.6 ->
  finite(Q256.to_f64(normal_q_outer_complement constant x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-111) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_outer_complement constant x))=(c-normal_tail(B x))*(1+d)+a.
Proof.
  intros C Cvalue Crange F X.
  destruct(normal_q_outer_complement_error constant x c C Cvalue Crange F X)as[Result Error].
  pose proof(normal_tail_outer_range(B x)(proj1 X))as Target.
  replace(bpow radix2 (-111))with(2*bpow radix2 (-112))by(bpow_num;field).
  apply normal_q_positive_rounded;try assumption;[split;lra|split;[apply bpow_ge_0|interval with(i_prec 80)]].
Qed.

Corollary normal_q_outer_cdf_error x : finite x -> /2<=B x<=38.6 ->
  valid(normal_q_outer_complement q_one x) /\ exists e,Rabs e<=bpow radix2 (-112) /\
  qval(normal_q_outer_complement q_one x)=(1-normal_tail(B x))*(1+e).
Proof.
  intros F X;destruct q_one_ok as[Q Value];apply normal_q_outer_complement_error;try assumption;split;lra.
Qed.

Corollary normal_q_outer_center_error x : finite x -> /2<=B x<=38.6 ->
  valid(normal_q_outer_complement q_half x) /\ exists e,Rabs e<=bpow radix2 (-112) /\
  qval(normal_q_outer_complement q_half x)=NormalCentered.normal_center(B x)*(1+e).
Proof.
  intros F X;destruct q_half_ok as[Q Value].
  pose proof(normal_q_outer_complement_error q_half x (/2)Q Value ltac:(split;lra) F X)as Result.
  rewrite normal_tail_complement in Result;replace(/2-(/2-NormalCentered.normal_center(B x)))with
    (NormalCentered.normal_center(B x))in Result by ring;exact Result.
Qed.
