(** Q256 centered CDF from the original binary64 argument, including the
    square's arithmetic error and the generated density constant. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalCentered NormalConstants NormalCenterHorner
  NormalCenterApproximation NormalAccurateRounding ErfcxAccurateInputs.
Open Scope R_scope.

Definition normal_q_center_argument x :=
  neg_q(mul_pow2(mul (q_float x) (q_float x)) (-1)).

Lemma normal_q_center_argument_error x : finite x -> Rabs(B x)<=/2 ->
  valid(normal_q_center_argument x) /\ Rabs(qval(normal_q_center_argument x))<=/4 /\
  Rabs(qval(normal_q_center_argument x)-(-B x*B x/2))<=bpow radix2 (-258).
Proof.
  intros F X. destruct(q_float_ok x F) as [Q Value].
  destruct(mul_relative _ _ Q Q) as [S [e [E Square]]].
  destruct(mul_pow2_any _ (-1) S) as [Half HalfValue].
  destruct(neg_any _ Half) as [Result ResultValue].
  assert (V : qval(normal_q_center_argument x)=(-B x*B x/2)*(1+e)).
  { unfold normal_q_center_argument;rewrite ResultValue,HalfValue,Square,Value.
    change(bpow radix2 (-1))with(/2);field. }
  split;[exact Result|]. rewrite V. apply Rabs_le_inv in X,E.
  split.
  - apply Rabs_le;split;bpow_num_all;interval with(i_prec 300).
  - replace((-B x*B x/2)*(1+e)-(-B x*B x/2))with((-B x*B x/2)*e)by ring.
    apply Rabs_le;split;bpow_num_all;interval with(i_prec 300).
Qed.

Definition normal_q_shape x := normal_q_center_horner (normal_q_center_argument x) 40.

Theorem normal_q_shape_error x : finite x -> Rabs(B x)<=/2 ->
  valid(normal_q_shape x) /\
  Rabs(qval(normal_q_shape x)-normal_shape(B x))<=bpow radix2 (-249).
Proof.
  intros F X.
  destruct(normal_q_center_argument_error x F X) as [Z [Zrange Zerror]].
  destruct(normal_q_center_horner_error _ 40 Z Zrange ltac:(lia)) as [Q Error].
  assert (Target : Rabs(-B x*B x/2)<=/4).
  { apply Rabs_le_inv in X;apply Rabs_le;split;nra. }
  pose proof(normal_center_horner_lipschitz _ _ 40 Zrange Target) as Perturbation.
  pose proof(normal_center_horner_truncation _ X) as Truncation.
  split;[exact Q|]. unfold normal_q_shape.
  replace(qval(normal_q_center_horner (normal_q_center_argument x) 40)-normal_shape(B x)) with
    ((qval(normal_q_center_horner (normal_q_center_argument x) 40)-
        normal_center_horner(qval(normal_q_center_argument x))40)+
      (normal_center_horner(qval(normal_q_center_argument x))40-normal_center_horner(-B x*B x/2)40)+
      (normal_center_horner(-B x*B x/2)40-normal_shape(B x))) by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|].
  assert (Budget : bpow radix2 (-250)+4*bpow radix2 (-258)+bpow radix2 (-280)<=bpow radix2 (-249))
    by (bpow_num;lra).
  lra.
Qed.

Definition normal_q_center x :=
  mul (mul (q_float x) normal_q_density) (normal_q_shape x).

Lemma normal_center_product_error s c a b :
  Rabs s<=bpow radix2 (-248) -> Rabs c<=bpow radix2 (-255) ->
  Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs((1+s)*(1+c)*(1+a)*(1+b)-1)<=bpow radix2 (-247).
Proof.
  intros S C A B. apply Rabs_le_inv in S,C,A,B.
  replace((1+s)*(1+c)*(1+a)*(1+b)-1)with(s+(1+s)*(c+(1+c)*(a+(1+a)*b)))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_center_error x : finite x -> Rabs(B x)<=/2 ->
  valid(normal_q_center x) /\ exists e,Rabs e<=bpow radix2 (-247) /\
  qval(normal_q_center x)=normal_center(B x)*(1+e).
Proof.
  intros F X. destruct(q_float_ok x F) as [Q Value].
  destruct(normal_q_shape_error x F X) as [S Serror].
  pose proof(normal_shape_range _ X) as Range.
  set(s:=qval(normal_q_shape x)/normal_shape(B x)-1).
  assert (Svalue : qval(normal_q_shape x)=normal_shape(B x)*(1+s)) by (unfold s;field;lra).
  assert (Sbound : Rabs s<=bpow radix2 (-248)).
  { unfold s. replace(qval(normal_q_shape x)/normal_shape(B x)-1)with
      ((qval(normal_q_shape x)-normal_shape(B x))/normal_shape(B x))by(field;lra).
    unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(normal_shape(B x)))by lra.
    apply(Rmult_le_reg_r(normal_shape(B x)));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    eapply Rle_trans;[exact Serror|].
    replace(bpow radix2 (-249))with(bpow radix2 (-248)/2)by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-248));nra. }
  destruct normal_q_density_error as [D Derror].
  set(c:=qval normal_q_density/normal_density_constant-1).
  assert (Cbound : Rabs c<=bpow radix2 (-255)) by exact Derror.
  assert (Cvalue : qval normal_q_density=normal_density_constant*(1+c)).
  { unfold c;field;unfold normal_density_constant;interval with(i_prec 80). }
  destruct(mul_relative _ _ Q D) as [P [a [A Pvalue]]].
  destruct(mul_relative _ _ P S) as [Result [b [Berr ResultValue]]].
  split;[exact Result|]. exists((1+s)*(1+c)*(1+a)*(1+b)-1). split.
  - apply normal_center_product_error;assumption.
  - unfold normal_q_center,normal_center;rewrite ResultValue,Pvalue,Value,Cvalue,Svalue;ring.
Qed.

Theorem normal_q_center_rounded x : finite x -> Rabs(B x)<=/2 ->
  finite(Q256.to_f64(normal_q_center x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-246) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_center x))=normal_center(B x)*(1+d)+a.
Proof.
  intros F X. destruct(normal_q_center_error x F X) as [Q Error].
  pose proof(normal_shape_range _ X) as Shape.
  assert (Range : Rabs(normal_center(B x))<=1).
  { unfold normal_center,normal_density_constant.
    apply Rabs_le_inv in X;apply Rabs_le;split;interval with(i_prec 80). }
  assert (Epsilon : 0<=bpow radix2 (-247)<=/4).
  { split;[apply bpow_ge_0|interval with(i_prec 80)]. }
  replace(bpow radix2 (-246))with(2*bpow radix2 (-247))by(bpow_num;field).
  exact(normal_q_bounded_rounded _ _ _ Q Range Epsilon Error).
Qed.
