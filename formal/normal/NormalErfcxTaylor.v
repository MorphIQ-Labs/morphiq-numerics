(** The extended-input Taylor evaluator, including the Q256 subtraction of
    its table center. Lookup must establish the stated residual-radius premise. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxAccurateInputs
  ErfcxAccurateCenterModel ErfcxAccurateCenterBounds ErfcxAccurateTaylorLoop
  ErfcxAccurateTaylor NormalErfcxSensitivity.
Open Scope R_scope.

Lemma normal_erfcx_positive_secant a b : 0<a<=b ->
  Rabs(gaussian_erfcx b-gaussian_erfcx a)<=2*(b-a).
Proof.
  intros Range. destruct(Rle_lt_or_eq_dec _ _ (proj2 Range))as[Lt|Eq].
  2: rewrite Eq,Rminus_diag_eq,Rabs_R0 by reflexivity;lra.
  destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative a b Lt)as[c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - destruct(normal_erfcx_derivative_bounds c ltac:(lra))as[Bounds _].
    assert (Constant : inv_sqrt_pi<=1)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
    rewrite Difference,Rabs_mult,Rabs_left1,(Rabs_pos_eq(b-a))by lra;nra.
Qed.

Theorem normal_erfcx_positive_lipschitz a b : 0<a -> 0<b ->
  Rabs(gaussian_erfcx b-gaussian_erfcx a)<=2*Rabs(b-a).
Proof.
  intros A B. destruct(Rle_dec a b)as[Order|Order].
  - rewrite (Rabs_pos_eq(b-a))by lra;apply normal_erfcx_positive_secant;split;lra.
  - rewrite Rabs_minus_sym,(Rabs_left(b-a))by lra.
    replace(-(b-a))with(a-b)by ring;apply normal_erfcx_positive_secant;split;lra.
Qed.

Definition normal_q_erfcx_residual x c := add x (neg_q(q_float c)).
Definition normal_q_erfcx_taylor_at x c i :=
  q_taylor_series (q_float c) i (normal_q_erfcx_residual x c).

Theorem normal_q_erfcx_residual_error x c i : valid x -> /4<=qval x<=16 ->
  finite c -> (i<177)%nat -> B c=accurate_center i ->
  valid(normal_q_erfcx_residual x c) /\
  Rabs(accurate_center i+qval(normal_q_erfcx_residual x c)-qval x)<=bpow radix2 (-250).
Proof.
  intros X Range Fc I Center.
  destruct(q_float_ok c Fc)as[C Cvalue]. destruct(neg_any _ C)as[NC NCvalue].
  destruct(add_any _ _ X NC)as[H Error].
  destruct(accurate_center_bounds i I)as[CenterRange _].
  rewrite NCvalue,Cvalue,Center,Rabs_Ropp in Error.
  assert (Inputs : Rmax(Rabs(qval x))(Rabs(accurate_center i))<=16).
  { apply Rmax_lub;[rewrite Rabs_pos_eq;lra|exact CenterRange]. }
  split;[exact H|].
  replace(accurate_center i+qval(normal_q_erfcx_residual x c)-qval x)with
    (qval(normal_q_erfcx_residual x c)-(qval x+ -accurate_center i))by ring.
  eapply Rle_trans;[exact Error|].
  replace(bpow radix2 (-250))with(bpow radix2 (-254)*16)by(bpow_num;field).
  apply Rmult_le_compat_l;[apply bpow_ge_0|exact Inputs].
Qed.

Theorem normal_q_erfcx_taylor_at_error x c i : valid x -> /4<=qval x<=16 ->
  finite c -> (i<177)%nat -> B c=accurate_center i ->
  Rabs(qval(normal_q_erfcx_residual x c))<=/8 ->
  valid(normal_q_erfcx_taylor_at x c i) /\
  Rabs(qval(normal_q_erfcx_taylor_at x c i)-gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range Fc I Center Radius.
  destruct(normal_q_erfcx_residual_error x c i X Range Fc I Center)as[H Residual].
  destruct(q_float_ok c Fc)as[C Cvalue].
  destruct(q_taylor_series_error _ i _ C H I ltac:(rewrite Cvalue;exact Center) Radius)as[Q Error].
  set(y:=accurate_center i+qval(normal_q_erfcx_residual x c))in *.
  assert (Y : 0<y).
  { apply Rabs_le_inv in Residual.
    assert(Small : bpow radix2 (-250)</4)by(interval with(i_prec 80));lra. }
  pose proof(normal_erfcx_positive_lipschitz (qval x) y ltac:(lra) Y)as Sensitivity.
  assert (Perturbation : Rabs(gaussian_erfcx y-gaussian_erfcx(qval x))<=bpow radix2 (-249)).
  { eapply Rle_trans;[exact Sensitivity|].
    replace(bpow radix2 (-249))with(2*bpow radix2 (-250))by(bpow_num;field);lra. }
  split;[exact Q|]. unfold normal_q_erfcx_taylor_at.
  replace(qval(q_taylor_series (q_float c) i (normal_q_erfcx_residual x c))-gaussian_erfcx(qval x))with
    ((qval(q_taylor_series (q_float c) i (normal_q_erfcx_residual x c))-gaussian_erfcx y)+
     (gaussian_erfcx y-gaussian_erfcx(qval x)))by ring.
  eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra.
Qed.
