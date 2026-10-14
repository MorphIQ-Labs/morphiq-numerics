(** Central log-CDF: propagate the central probability error through the
    double-word logarithm before applying the computed relative guard. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa NormalCentered NormalAccurateCentralCdf NormalCdfCentralFast
  NormalLogDw NormalLogSensitivity NormalCenterFastTail.
Open Scope R_scope.

Lemma normal_log_absolute_perturbation f g epsilon : 0<f -> 0<=epsilon<=/2 ->
  Rabs(g-f)<=epsilon*f -> Rabs(ln g-ln f)<=2*epsilon.
Proof.
  intros F Epsilon Error;set(e:=(g-f)/f).
  assert(E : Rabs e<=epsilon).
  { unfold e,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f)by lra.
    apply(Rmult_le_reg_r f);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;lra. }
  replace g with(f*(1+e))by(unfold e;field;lra).
  exact(normal_log_relative_perturbation f e epsilon F Epsilon E).
Qed.

Definition normal_log_central_fast64 x :=
  let '(h,l):=normal_cdf_central_fast64 x in normal_log_dw64 h l.

Theorem normal_log_central_fast_ieee x : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_log_central_fast64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=4 /\ Rabs(B l)<=bpow radix2 (-52) /\
  Rabs((B h+B l)-ln(normal_cdf(B x)))<=7*bpow radix2 (-65)*Rabs(ln(normal_cdf(B x))).
Proof.
  intros Fx X;pose proof(normal_cdf_central_fast_ieee x Fx X)as Cdf.
  unfold normal_log_central_fast64;destruct(normal_cdf_central_fast64 x)as[a b].
  destruct Cdf as[Fa [Fb [Anorm [A [Bl CdfError]]]]].
  pose proof(normal_central_cdf_range(B x)(proj2 X))as TargetRange.
  assert(High : /8<=B a<=7/8).
  { pose proof(Rabs_triang_inv(B a+B b)(normal_cdf(B x)))as Range.
    apply Rabs_le_inv in CdfError,Bl;split;[lra|bpow_num_all;lra]. }
  assert(LogRange : /4<=Rabs(ln(normal_cdf(B x)))<=2).
  { assert(-2<=ln(normal_cdf(B x))<= -/4)by(split;interval with(i_prec 80)).
    rewrite Rabs_left1 by lra;split;lra. }
  pose proof(normal_log_dw_ieee a b Fa Fb High Bl)as Log.
  destruct(normal_log_dw64 a b)as[h l];destruct Log as[Fh [Fl [Norm LogError]]].
  assert(InputError : Rabs(ln(B a+B b)-ln(normal_cdf(B x)))<=bpow radix2 (-65)).
  { replace(bpow radix2 (-65))with(2*bpow radix2 (-66))by(bpow_num;field).
    apply normal_log_absolute_perturbation;[lra|split;interval with(i_prec 100)|].
    eapply Rle_trans;[exact CdfError|];bpow_num_all;nra. }
  assert(HighError : Rabs(ln(B a)-ln(normal_cdf(B x)))<=bpow radix2 (-50)).
  { replace(bpow radix2 (-50))with(2*bpow radix2 (-51))by(bpow_num;field).
    apply normal_log_absolute_perturbation;[lra|split;interval with(i_prec 100)|].
    replace(B a-normal_cdf(B x))with(((B a+B b)-normal_cdf(B x))-B b)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-ln(normal_cdf(B x)))<=7*bpow radix2 (-65)*Rabs(ln(normal_cdf(B x)))).
  { replace((B h+B l)-ln(normal_cdf(B x)))with
      (((B h+B l)-ln(B a+B b))+(ln(B a+B b)-ln(normal_cdf(B x))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    pose proof(Rabs_triang_inv(ln(B a))(ln(normal_cdf(B x))))as HighLog.
    bpow_num_all;nra. }
  assert(Sum : Rabs(B h+B l)<=4).
  { pose proof(Rabs_triang_inv(B h+B l)(ln(normal_cdf(B x))));bpow_num_all;nra. }
  assert(H : Rabs(B h)<=4).
  { rewrite Norm;change 4 with(bpow radix2 2);apply normal_center_round_bound;[exact Sum|lia]. }
  pose proof(rnd_err_below(B h+B l)2 ltac:(lia)Sum)as Rounded;rewrite <-Norm in Rounded.
  change(2-54)%Z with(-52)%Z in Rounded.
  assert(L : Rabs(B l)<=bpow radix2 (-52)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;assumption.
Qed.
