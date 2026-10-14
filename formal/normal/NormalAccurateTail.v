(** The Q256 normal tail in the erfcx asymptotic region. Every product,
    the scaled-argument perturbation, and final underflow rounding are included. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget NormalErfcxIdentity
  NormalErfcxSensitivity NormalScaledArgument NormalErfcxAsymptotic
  NormalAccurateGaussian NormalAccurateRounding NormalTailAnalytic.
Open Scope R_scope.

Definition normal_q_scaled_erfcx_asym x := normal_q_erfcx_asymptotic(normal_q_scaled_argument x).
Definition normal_q_tail_asym x :=
  mul_pow2 (mul (normal_q_gaussian_regular x) (normal_q_scaled_erfcx_asym x)) (-1).

Lemma normal_scaled_argument_large x : finite x -> 23<=B x ->
  16<=qval(normal_q_scaled_argument x).
Proof.
  intros F X. destruct(normal_q_scaled_argument_error x F) as [_ [e [E Value]]].
  assert (Scale : 7/10<=(/sqrt 2)*(1+e)).
  { apply Rabs_le_inv in E;bpow_num_all;interval with(i_prec 80). }
  rewrite Value;unfold Rdiv;nra.
Qed.

Lemma normal_scaled_asym_product_error a b :
  Rabs a<=bpow radix2 (-249) -> Rabs b<=bpow radix2 (-224) ->
  Rabs((1+a)*(1+b)-1)<=bpow radix2 (-223).
Proof.
  intros A B;apply Rabs_le_inv in A,B.
  replace((1+a)*(1+b)-1)with(a+(1+a)*b)by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_scaled_erfcx_asym_error x : finite x -> 23<=B x ->
  valid(normal_q_scaled_erfcx_asym x) /\ exists e,Rabs e<=bpow radix2 (-223) /\
  qval(normal_q_scaled_erfcx_asym x)=gaussian_erfcx(B x/sqrt 2)*(1+e).
Proof.
  intros F X. destruct(normal_q_scaled_argument_error x F) as [Q _].
  pose proof(normal_q_scaled_argument_range x F ltac:(lra)) as Range.
  pose proof(normal_scaled_argument_large x F X) as Large.
  destruct(normal_q_erfcx_asymptotic_error _ Q ltac:(split;lra)) as [Result [e [E Value]]].
  rewrite positive_erfcx_gaussian in Value by lra.
  pose proof(normal_q_scaled_erfcx_argument_error x F ltac:(lra)) as Argument.
  set(f:=gaussian_erfcx(B x/sqrt 2))in *.
  assert (Positive : 0<f).
  { unfold f;apply normal_erfcx_positive,Rdiv_lt_0_compat;[lra|interval with(i_prec 80)]. }
  set(a:=(gaussian_erfcx(qval(normal_q_scaled_argument x))-f)/f).
  assert (A : Rabs a<=bpow radix2 (-249)).
  { unfold a,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f) by lra.
    apply(Rmult_le_reg_r f);[exact Positive|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
  assert (Exact : gaussian_erfcx(qval(normal_q_scaled_argument x))=f*(1+a)).
  { unfold a;field;lra. }
  split;[exact Result|]. exists((1+a)*(1+e)-1). split.
  - apply normal_scaled_asym_product_error;assumption.
  - unfold normal_q_scaled_erfcx_asym;rewrite Value,Exact;ring.
Qed.

Lemma normal_tail_product_error a b c :
  Rabs a<=bpow radix2 (-238) -> Rabs b<=bpow radix2 (-223) ->
  Rabs c<=bpow radix2 (-255) ->
  Rabs((1+a)*(1+b)*(1+c)-1)<=bpow radix2 (-222).
Proof.
  intros A B C;apply Rabs_le_inv in A,B,C.
  replace((1+a)*(1+b)*(1+c)-1)with(a+(1+a)*(b+(1+b)*c))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_tail_asym_error x : finite x -> 23<=B x<=38.6 ->
  valid(normal_q_tail_asym x) /\ exists e,Rabs e<=bpow radix2 (-222) /\
  qval(normal_q_tail_asym x)=normal_tail(B x)*(1+e).
Proof.
  intros F X.
  assert (Domain : bpow radix2 (-400)<=B x<=38.6).
  { assert (Small : bpow radix2 (-400)<=23)by(interval with(i_prec 80));split;lra. }
  destruct(normal_q_gaussian_regular_error x F Domain) as [G [eg [Eg Gvalue]]].
  destruct(normal_q_scaled_erfcx_asym_error x F (proj1 X)) as [S [es [Es Svalue]]].
  destruct(mul_relative _ _ G S) as [P [em [Em Pvalue]]].
  destruct(mul_pow2_any _ (-1) P) as [Result Value].
  split;[exact Result|]. exists((1+eg)*(1+es)*(1+em)-1). split.
  - apply normal_tail_product_error;assumption.
  - unfold normal_q_tail_asym;rewrite Value,Pvalue,Gvalue,Svalue.
    unfold normal_tail;change(bpow radix2 (-1))with(/2);field.
Qed.

Theorem normal_q_tail_asym_rounded x : finite x -> 23<=B x<=38.6 ->
  finite(Q256.to_f64(normal_q_tail_asym x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-221) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_tail_asym x))=normal_tail(B x)*(1+d)+a.
Proof.
  intros F X. destruct(normal_q_tail_asym_error x F X) as [Q Error].
  pose proof(normal_tail_range(B x) ltac:(lra)) as Range.
  replace(bpow radix2 (-221))with(2*bpow radix2 (-222))by(bpow_num;field).
  assert (Fbound : 0<=normal_tail(B x)<=1)by(split;lra).
  assert (Ebound : 0<=bpow radix2 (-222)<=/4)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  exact(normal_q_positive_rounded _ _ _ Q Fbound Ebound Error).
Qed.
