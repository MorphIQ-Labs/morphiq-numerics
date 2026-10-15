(** The fixed 40-level Q256 centered-CDF Horner evaluation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalCenterConstants.
Open Scope R_scope.

Fixpoint normal_q_center_horner z count :=
  match count with
  | O => normal_q_center_coefficient 40
  | S previous => add (normal_q_center_coefficient (40-S previous))
      (mul z (normal_q_center_horner z previous))
  end.
Fixpoint normal_center_horner z count : R :=
  match count with
  | O => normal_center_coefficient 40
  | S previous => normal_center_coefficient (40-S previous)+z*normal_center_horner z previous
  end.

Lemma normal_center_horner_range z count : Rabs z<=/4 ->
  Rabs(normal_center_horner z count)<=2.
Proof.
  intros Z. induction count as [|n IH].
  - cbn [normal_center_horner]. pose proof(normal_center_coefficient_range 40).
    rewrite Rabs_pos_eq;lra.
  - cbn [normal_center_horner]. pose proof(normal_center_coefficient_range (40-S n)).
    apply Rabs_le_inv in Z,IH. apply Rabs_le;split;interval with(i_prec 80).
Qed.

Lemma normal_center_horner_product z h e m :
  Rabs z<=/4 -> Rabs h<=2 -> Rabs e<=bpow radix2 (-250) ->
  Rabs m<=bpow radix2 (-255) -> Rabs(z*(h+e)*(1+m))<=1.
Proof.
  intros Z H E M. apply Rabs_le_inv in Z,H,E,M.
  bpow_num_all. apply Rabs_le;split;interval with(i_prec 300).
Qed.

Lemma normal_center_horner_step_error z h e m c a :
  Rabs z<=/4 -> Rabs h<=2 -> Rabs e<=bpow radix2 (-250) ->
  Rabs m<=bpow radix2 (-255) -> Rabs c<=bpow radix2 (-255) ->
  Rabs a<=bpow radix2 (-253) ->
  Rabs(c+z*(e+(h+e)*m)+a)<=bpow radix2 (-250).
Proof.
  intros Z H E M C A. apply Rabs_le_inv in Z,H,E,M,C,A.
  bpow_num_all. apply Rabs_le;split;interval with(i_prec 300).
Qed.

Theorem normal_q_center_horner_error z count : valid z -> Rabs(qval z)<=/4 ->
  (count<=40)%nat -> valid(normal_q_center_horner z count) /\
  Rabs(qval(normal_q_center_horner z count)-normal_center_horner (qval z) count)
    <=bpow radix2 (-250).
Proof.
  intros Z Zrange. induction count as [|n IH];intros N.
  - cbn [normal_q_center_horner normal_center_horner].
    destruct(normal_q_center_coefficient_error 40 ltac:(lia)) as [C Error].
    split;[exact C|]. eapply Rle_trans;[exact Error|apply bpow_le;lia].
  - destruct(IH ltac:(lia)) as [H Error].
    destruct(normal_q_center_coefficient_error (40-S n) ltac:(lia)) as [C Cerror].
    destruct(mul_relative _ _ Z H) as [P [m [M Pvalue]]].
    destruct(add_any _ _ C P) as [Result Addition].
    set(h:=normal_center_horner (qval z) n) in *.
    set(e:=qval(normal_q_center_horner z n)-h) in *.
    assert (Hvalue : qval(normal_q_center_horner z n)=h+e) by (unfold e;ring).
    assert (Hrange : Rabs h<=2) by (apply normal_center_horner_range;exact Zrange).
    assert (Prange : Rabs(qval(mul z (normal_q_center_horner z n)))<=1).
    { rewrite Pvalue,Hvalue;apply normal_center_horner_product;assumption. }
    assert (Crange : Rabs(qval(normal_q_center_coefficient (40-S n)))<=2).
    { pose proof(normal_center_coefficient_range (40-S n)).
      apply Rabs_le_inv in Cerror. apply Rabs_le. bpow_num_all;split;lra. }
    assert (AddError : Rabs(qval(add (normal_q_center_coefficient (40-S n))
      (mul z (normal_q_center_horner z n)))-
      (qval(normal_q_center_coefficient (40-S n))+qval(mul z (normal_q_center_horner z n))))
      <=bpow radix2 (-253)).
    { eapply Rle_trans;[exact Addition|].
      replace(bpow radix2 (-253))with(bpow radix2 (-254)*2) by (bpow_num;field).
      apply Rmult_le_compat_l;[apply bpow_ge_0|apply Rmax_lub;lra]. }
    set(c:=qval(normal_q_center_coefficient (40-S n))-normal_center_coefficient (40-S n)) in *.
    set(a:=qval(add (normal_q_center_coefficient (40-S n)) (mul z (normal_q_center_horner z n)))-
      (qval(normal_q_center_coefficient (40-S n))+qval(mul z (normal_q_center_horner z n)))) in *.
    cbn [normal_q_center_horner normal_center_horner]. fold h.
    split;[exact Result|].
    replace(qval(add (normal_q_center_coefficient (40-S n)) (mul z (normal_q_center_horner z n)))-
      (normal_center_coefficient (40-S n)+qval z*h)) with(c+qval z*(e+(h+e)*m)+a)
      by (unfold c,a;rewrite Pvalue,Hvalue;ring).
    apply normal_center_horner_step_error;assumption.
Qed.
