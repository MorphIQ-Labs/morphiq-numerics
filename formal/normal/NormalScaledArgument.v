(** Q256 construction of x/sqrt(2), including its relative effect on erfcx.
    The relative sensitivity bound avoids an absolute-error loss in the tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxGaussianTarget
  NormalConstants NormalErfcxSensitivity.
Open Scope R_scope.

Definition normal_q_scaled_argument x := mul (q_float x) normal_q_inv_sqrt2.

Lemma normal_scaled_product_error a b :
  Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs((1+a)*(1+b)-1)<=bpow radix2 (-253).
Proof.
  intros A B;apply Rabs_le_inv in A,B.
  replace((1+a)*(1+b)-1)with(a+(1+a)*b)by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_scaled_argument_error x : finite x ->
  valid(normal_q_scaled_argument x) /\ exists e,
  Rabs e<=bpow radix2 (-253) /\
  qval(normal_q_scaled_argument x)=(B x/sqrt 2)*(1+e).
Proof.
  intros F. destruct(q_float_ok x F) as [X Xvalue].
  destruct normal_q_inv_sqrt2_error as [C Cerror].
  set(ec:=qval normal_q_inv_sqrt2/(/sqrt 2)-1).
  assert (Ec : Rabs ec<=bpow radix2 (-255))by exact Cerror.
  assert (Cvalue : qval normal_q_inv_sqrt2=(/sqrt 2)*(1+ec)).
  { unfold ec;field;interval with(i_prec 80). }
  destruct(mul_relative _ _ X C) as [Result [em [Em Value]]].
  split;[exact Result|]. exists((1+ec)*(1+em)-1). split.
  - apply normal_scaled_product_error;assumption.
  - unfold normal_q_scaled_argument;rewrite Value,Xvalue,Cvalue;unfold Rdiv;ring.
Qed.

Theorem normal_q_scaled_argument_range x : finite x -> 0<B x ->
  0<qval(normal_q_scaled_argument x)<=3*bpow radix2 1022.
Proof.
  intros F X.
  destruct(normal_q_scaled_argument_error x F) as [_ [e [E Value]]].
  assert (Scale : 0<(/sqrt 2)*(1+e)<=3/4).
  { apply Rabs_le_inv in E;bpow_num_all;split;interval with(i_prec 80). }
  assert (Upper : B x<bpow radix2 1024).
  { pose proof(abs_B2R_lt_emax 53 1024 x). change(Rabs(B x)<bpow radix2 1024)in H.
    rewrite Rabs_pos_eq in H by lra;exact H. }
  rewrite Value;unfold Rdiv.
  replace(3*bpow radix2 1022)with((3/4)*bpow radix2 1024).
  - split;[nra|].
    eapply Rle_trans with(B x*(3/4));[nra|nra].
  - replace(bpow radix2 1024)with(4*bpow radix2 1022).
    + field.
    + change 4 with(bpow radix2 2);rewrite <-bpow_plus;reflexivity.
Qed.

Theorem normal_q_scaled_erfcx_argument_error x : finite x -> 0<B x ->
  Rabs(gaussian_erfcx(qval(normal_q_scaled_argument x))-gaussian_erfcx(B x/sqrt 2))<=
    gaussian_erfcx(B x/sqrt 2)*bpow radix2 (-249).
Proof.
  intros F X. destruct(normal_q_scaled_argument_error x F) as [_ [e [E Value]]].
  set(z:=B x/sqrt 2).
  assert (Zpos : 0<z)by(unfold z;apply Rdiv_lt_0_compat;[exact X|interval with(i_prec 80)]).
  assert (Difference : Rabs(qval(normal_q_scaled_argument x)-z)=z*Rabs e).
  { rewrite Value;fold z;replace(z*(1+e)-z)with(z*e)by ring.
    rewrite Rabs_mult,Rabs_pos_eq by lra;reflexivity. }
  assert (Half : Rabs(qval(normal_q_scaled_argument x)-z)<=z/2).
  { rewrite Difference. assert (Small : Rabs e<=/2).
    { eapply Rle_trans;[exact E|interval with(i_prec 80)]. } nra. }
  pose proof(normal_erfcx_scaled_argument_error z _ Zpos Half) as Error.
  rewrite Difference in Error.
  replace(z*Rabs e/z)with(Rabs e)in Error by(field;lra).
  pose proof(normal_erfcx_positive z Zpos) as Positive.
  eapply Rle_trans;[exact Error|].
  replace(bpow radix2 (-249))with(16*bpow radix2 (-253))by(bpow_num;field).
  nra.
Qed.
