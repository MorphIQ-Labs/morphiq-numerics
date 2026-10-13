(** Normalized derivatives: the coefficient recurrence used by Q256. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Expm1Series ErfcxConstants ErfcxMoments
  ErfcxGaussianTarget ErfcxTaylorDerivatives ErfcxTaylorBounds.
Open Scope R_scope.
Definition taylor_coefficient n c := Derive_n gaussian_erfcx n c/INR(fact n).
Lemma taylor_coefficient_zero c : taylor_coefficient 0 c=gaussian_erfcx c.
Proof. unfold taylor_coefficient; cbn [Derive_n fact INR]; field. Qed.
Lemma taylor_coefficient_one c : taylor_coefficient 1 c=2*c*gaussian_erfcx c-2*inv_sqrt_pi.
Proof.
  unfold taylor_coefficient. rewrite taylor_derivative_n.
  cbn [taylor_derivatives fst snd]. change (INR(fact 1)) with 1. field.
Qed.
Lemma taylor_derivative_step n c :
  Derive_n gaussian_erfcx (S(S n)) c=
    2*c*Derive_n gaussian_erfcx (S n) c+2*INR(S n)*Derive_n gaussian_erfcx n c.
Proof.
  rewrite !taylor_derivative_n,!taylor_derivative_next.
  cbn [taylor_derivatives]. destruct (taylor_derivatives n c); reflexivity.
Qed.
Theorem taylor_coefficient_step n c :
  taylor_coefficient (S(S n)) c=
    (2*c*taylor_coefficient (S n) c+2*taylor_coefficient n c)/INR(S(S n)).
Proof.
  unfold taylor_coefficient. rewrite taylor_derivative_step,!INR_fact_succ.
  assert (N : INR(S n)<>0) by (apply not_0_INR; lia).
  assert (N2 : INR(S(S n))<>0) by (apply not_0_INR; lia).
  assert (F : INR(fact n)<>0) by (apply not_0_INR; pose proof(lt_O_fact n);lia).
  field; auto.
Qed.
Theorem taylor_coefficient_bound n c : (n<=100)%nat -> Rabs c<=16 ->
  Rabs(gaussian_erfcx c)<=3 -> Rabs(taylor_coefficient n c)<=bpow radix2 67.
Proof.
  intros N C F.
  pose proof (taylor_derivative_bound n c N ltac:(lra) ltac:(lra)) as D.
  pose proof (exponential_single_term n 40 ltac:(lra)) as Exp.
  assert (Fact : 0<INR(fact n)) by (apply lt_0_INR,lt_O_fact).
  unfold taylor_coefficient,Rdiv. rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(INR(fact n))) by lra.
  eapply Rle_trans with (512*40^n*/INR(fact n)).
  - apply Rmult_le_compat_r; [apply Rlt_le,Rinv_0_lt_compat;exact Fact|exact D].
  - eapply Rle_trans with (512*exp 40); [unfold Rdiv in Exp; nra|].
    bpow_num. interval with (i_prec 100).
Qed.
