(** The complete Q256 tail composition outside the central interval. The
    extended erfcx dispatcher covers both the table and asymptotic regions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget NormalErfcxSensitivity
  NormalScaledArgument NormalExtendedErfcx NormalAccurateGaussian
  NormalAccurateRounding NormalTailAnalytic.
Open Scope R_scope.

Definition normal_q_scaled_erfcx x := normal_q_erfcx_positive(normal_q_scaled_argument x).
Definition normal_q_tail x :=
  mul_pow2 (mul (normal_q_gaussian_regular x) (normal_q_scaled_erfcx x)) (-1).

Lemma normal_scaled_argument_table x : finite x -> /2<=B x ->
  /4<=qval(normal_q_scaled_argument x).
Proof.
  intros F X;destruct(normal_q_scaled_argument_error x F)as[_ [e [E Value]]].
  assert (Scale : 7/10<=(/sqrt 2)*(1+e)).
  { apply Rabs_le_inv in E;bpow_num_all;interval with(i_prec 80). }
  rewrite Value;unfold Rdiv;nra.
Qed.

Lemma normal_scaled_erfcx_product_error a b :
  Rabs a<=bpow radix2 (-249) -> Rabs b<=bpow radix2 (-117) ->
  Rabs((1+a)*(1+b)-1)<=bpow radix2 (-116).
Proof.
  intros A B;apply Rabs_le_inv in A,B.
  replace((1+a)*(1+b)-1)with(a+(1+a)*b)by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_scaled_erfcx_error x : finite x -> /2<=B x ->
  valid(normal_q_scaled_erfcx x) /\ exists e,Rabs e<=bpow radix2 (-116) /\
  qval(normal_q_scaled_erfcx x)=gaussian_erfcx(B x/sqrt 2)*(1+e).
Proof.
  intros F X;destruct(normal_q_scaled_argument_error x F)as[Q _].
  pose proof(normal_q_scaled_argument_range x F ltac:(lra))as Range.
  pose proof(normal_scaled_argument_table x F X)as Lower.
  destruct(normal_q_erfcx_positive_error _ Q ltac:(split;lra))as[Result [e [E Value]]].
  pose proof(normal_q_scaled_erfcx_argument_error x F ltac:(lra))as Argument.
  set(f:=gaussian_erfcx(B x/sqrt 2))in *.
  assert (Positive : 0<f).
  { unfold f;apply normal_erfcx_positive,Rdiv_lt_0_compat;[lra|interval with(i_prec 80)]. }
  set(a:=(gaussian_erfcx(qval(normal_q_scaled_argument x))-f)/f).
  assert (A : Rabs a<=bpow radix2 (-249)).
  { unfold a,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f)by lra.
    apply(Rmult_le_reg_r f);[exact Positive|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
  assert (Exact : gaussian_erfcx(qval(normal_q_scaled_argument x))=f*(1+a)).
  { unfold a;field;lra. }
  split;[exact Result|]. exists((1+a)*(1+e)-1);split.
  - apply normal_scaled_erfcx_product_error;assumption.
  - unfold normal_q_scaled_erfcx;rewrite Value,Exact;ring.
Qed.

Lemma normal_full_tail_product_error a b c :
  Rabs a<=bpow radix2 (-238) -> Rabs b<=bpow radix2 (-116) ->
  Rabs c<=bpow radix2 (-255) ->
  Rabs((1+a)*(1+b)*(1+c)-1)<=bpow radix2 (-115).
Proof.
  intros A B C;apply Rabs_le_inv in A,B,C.
  replace((1+a)*(1+b)*(1+c)-1)with(a+(1+a)*(b+(1+b)*c))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_tail_error x : finite x -> /2<=B x<=38.6 ->
  valid(normal_q_tail x) /\ exists e,Rabs e<=bpow radix2 (-115) /\
  qval(normal_q_tail x)=normal_tail(B x)*(1+e).
Proof.
  intros F X.
  assert (Domain : bpow radix2 (-400)<=B x<=38.6).
  { assert (Small : bpow radix2 (-400)<=/2)by(interval with(i_prec 80));split;lra. }
  destruct(normal_q_gaussian_regular_error x F Domain)as[G [eg [Eg Gvalue]]].
  destruct(normal_q_scaled_erfcx_error x F (proj1 X))as[S [es [Es Svalue]]].
  destruct(mul_relative _ _ G S)as[P [em [Em Pvalue]]].
  destruct(mul_pow2_any _ (-1) P)as[Result Value].
  split;[exact Result|]. exists((1+eg)*(1+es)*(1+em)-1);split.
  - apply normal_full_tail_product_error;assumption.
  - unfold normal_q_tail;rewrite Value,Pvalue,Gvalue,Svalue.
    unfold normal_tail;change(bpow radix2 (-1))with(/2);field.
Qed.

Theorem normal_q_tail_rounded x : finite x -> /2<=B x<=38.6 ->
  finite(Q256.to_f64(normal_q_tail x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-114) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_tail x))=normal_tail(B x)*(1+d)+a.
Proof.
  intros F X;destruct(normal_q_tail_error x F X)as[Q Error].
  pose proof(normal_tail_range(B x) ltac:(lra))as Range.
  replace(bpow radix2 (-114))with(2*bpow radix2 (-115))by(bpow_num;field).
  assert (Fbound : 0<=normal_tail(B x)<=1)by(split;lra).
  assert (Ebound : 0<=bpow radix2 (-115)<=/4)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  exact(normal_q_positive_rounded _ _ _ Q Fbound Ebound Error).
Qed.
