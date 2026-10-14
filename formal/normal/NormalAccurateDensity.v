(** The Q256 density product, before its final binary64 rounding. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalConstants NormalAccurateGaussian NormalCentered
  NormalAccurateRounding.
Open Scope R_scope.

Definition normal_density x := normal_density_constant*exp(-x*x/2).
Definition normal_q_density_regular x :=
  mul (normal_q_gaussian_regular x) normal_q_density.

Lemma normal_density_product_error a b c :
  Rabs a<=bpow radix2 (-238) -> Rabs b<=bpow radix2 (-255) ->
  Rabs c<=bpow radix2 (-255) ->
  Rabs((1+a)*(1+b)*(1+c)-1)<=bpow radix2 (-237).
Proof.
  intros A B C. apply Rabs_le_inv in A,B,C.
  replace ((1+a)*(1+b)*(1+c)-1) with (a+(1+a)*(b+(1+b)*c)) by ring.
  bpow_num_all. apply Rabs_le;split;interval with(i_prec 400).
Qed.

Lemma normal_density_range x : 0<normal_density x<=1.
Proof.
  assert (C : 0<normal_density_constant<=1).
  { unfold normal_density_constant;split;interval with(i_prec 80). }
  assert (E : 0<exp(-x*x/2)<=1).
  { split;[apply exp_pos|]. rewrite <- exp_0;apply exp_le;nra. }
  unfold normal_density;split;nra.
Qed.

Theorem normal_q_density_regular_error x : finite x ->
  bpow radix2 (-400)<=B x<=38.6 ->
  valid (normal_q_density_regular x) /\ exists e,
  Rabs e<=bpow radix2 (-237) /\
  qval(normal_q_density_regular x)=normal_density(B x)*(1+e).
Proof.
  intros F X.
  destruct(normal_q_gaussian_regular_error x F X) as [G [eg [Eg Gvalue]]].
  destruct normal_q_density_error as [D Derror].
  set (ed:=qval normal_q_density/normal_density_constant-1).
  assert (Ed : Rabs ed<=bpow radix2 (-255)) by exact Derror.
  assert (Dvalue : qval normal_q_density=normal_density_constant*(1+ed)).
  { unfold ed. field. unfold normal_density_constant;interval with(i_prec 80). }
  destruct(mul_relative _ _ G D) as [P [em [Em Pvalue]]].
  split;[exact P|]. exists((1+eg)*(1+ed)*(1+em)-1). split.
  - apply normal_density_product_error;assumption.
  - unfold normal_q_density_regular,normal_density.
    rewrite Pvalue,Gvalue,Dvalue;ring.
Qed.

Theorem normal_q_density_regular_rounded x : finite x ->
  bpow radix2 (-400)<=B x<=38.6 ->
  finite(Q256.to_f64(normal_q_density_regular x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-236) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_density_regular x))=normal_density(B x)*(1+d)+a.
Proof.
  intros F X.
  destruct(normal_q_density_regular_error x F X) as [Q Error].
  pose proof(normal_density_range(B x)) as Range.
  replace (bpow radix2 (-236)) with(2*bpow radix2 (-237)) by (bpow_num;field).
  assert (Fbound : 0<=normal_density(B x)<=1) by (split;lra).
  assert (Ebound : 0<=bpow radix2 (-237)<=/4).
  { split;[apply bpow_ge_0|interval with(i_prec 80)]. }
  exact(normal_q_positive_rounded _ _ _ Q Fbound Ebound Error).
Qed.

