(** Logarithm of the corrected erfcx factor. Retaining the logarithm's
    magnitude keeps the negative log-CDF composition bound relative. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxGaussianSeries
  NormalErfcxSensitivity NormalErfcxFastScaled NormalErfcxFastRange
  NormalLogDw NormalLogCentralFast NormalCenterFastTail.
Open Scope R_scope.

Lemma normal_erfcx_log_upper z : /3<=z -> gaussian_erfcx z<=3/4.
Proof.
  intros Z;pose proof(normal_erfcx_decreasing (/3)z ltac:(split;lra))as Decreasing.
  pose proof(gaussian_approx_error 2 (/3))as Approx.
  assert(Bound : gaussian_approx 2 (/3)+
    2*inv_sqrt_pi*exp((/3)*(/3))*Rabs(/3)*((((/3)*(/3))^3)/INR(fact 3))<=3/4).
  { unfold gaussian_approx,gaussian_sum,inv_sqrt_pi;cbn[sum_f_R0 fact Nat.mul Nat.add Nat.sub INR];interval with(i_prec 100). }
  apply Rabs_le_inv in Approx;lra.
Qed.

Definition normal_log_erfcx64 x :=
  let '(h,l):=normal_erfcx_fast_scaled64 x in normal_log_dw64 h l.

Theorem normal_log_erfcx_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_log_erfcx64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ Rabs(B h)<=8 /\ Rabs(B l)<=bpow radix2 (-51) /\
  Rabs((B h+B l)-ln(gaussian_erfcx(B x/sqrt 2)))<=
    bpow radix2 (-64)*Rabs(ln(gaussian_erfcx(B x/sqrt 2)))+bpow radix2 (-64).
Proof.
  intros Fx X;pose proof(normal_erfcx_fast_scaled_ieee x Fx X)as Factor.
  unfold normal_log_erfcx64;destruct(normal_erfcx_fast_scaled64 x)as[a b].
  destruct Factor as[Fa [Fb [Anorm [A [Bl FactorError]]]]].
  assert(Z : /3<=B x/sqrt 2<=27)by(split;interval with(i_prec 80)).
  set(f:=gaussian_erfcx(B x/sqrt 2))in *.
  assert(F : /256<=f<=3/4).
  { unfold f;split;[apply normal_erfcx_compact_lower;split;lra|apply normal_erfcx_log_upper;exact(proj1 Z)]. }
  assert(High : /1024<=B a<=7/8).
  { apply Rabs_le_inv in FactorError,Bl;bpow_num_all;split;lra. }
  pose proof(normal_log_dw_ieee a b Fa Fb High Bl)as Log.
  destruct(normal_log_dw64 a b)as[h l];destruct Log as[Fh [Fl [Norm Evaluation]]].
  assert(InputError : Rabs(ln(B a+B b)-ln f)<=bpow radix2 (-65)).
  { replace(bpow radix2 (-65))with(2*bpow radix2 (-66))by(bpow_num;field).
    apply normal_log_absolute_perturbation;[lra|split;interval with(i_prec 80)|exact FactorError]. }
  assert(HighError : Rabs(ln(B a)-ln f)<=bpow radix2 (-43)).
  { replace(bpow radix2 (-43))with(2*bpow radix2 (-44))by(bpow_num;field).
    apply normal_log_absolute_perturbation;[lra|split;interval with(i_prec 80)|].
    replace(B a-f)with(((B a+B b)-f)-B b)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;bpow_num_all;nra. }
  assert(LogRange : -6<=ln f<= -/4)by(split;interval with(i_prec 80)).
  assert(Error : Rabs((B h+B l)-ln f)<=bpow radix2 (-64)*Rabs(ln f)+bpow radix2 (-64)).
  { replace((B h+B l)-ln f)with(((B h+B l)-ln(B a+B b))+(ln(B a+B b)-ln f))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    pose proof(Rabs_triang_inv(ln(B a))(ln f));bpow_num_all;nra. }
  assert(Sum : Rabs(B h+B l)<=8).
  { pose proof(Rabs_triang_inv(B h+B l)(ln f));rewrite(Rabs_left1(ln f))in * by lra;bpow_num_all;lra. }
  assert(H : Rabs(B h)<=8).
  { rewrite Norm;change 8 with(bpow radix2 3);apply normal_center_round_bound;[exact Sum|lia]. }
  pose proof(rnd_err_below(B h+B l)3 ltac:(lia)Sum)as Rounded;rewrite <-Norm in Rounded.
  change(3-54)%Z with(-51)%Z in Rounded.
  assert(L : Rabs(B l)<=bpow radix2 (-51)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;assumption.
Qed.
