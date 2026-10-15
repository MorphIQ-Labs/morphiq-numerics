(** Subtract the generated ln(2) pair from the logarithmic erfcx factor.
    Both terms have the same sign after subtraction, so cancellation is bounded. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa NormalConstants ErfcxGaussianTarget NormalErfcxFastScaled
  NormalLogErfcx NormalCenterFastTail LnFastCompose.
Open Scope R_scope.

Definition normal_ln2_constant64 := two_sum64 normal_ln2_hi normal_ln2_lo.

Lemma normal_ln2_constant_ieee : let '(h,l):=normal_ln2_constant64 in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ Rabs(B h)<=1 /\ Rabs(B l)<=bpow radix2 (-54) /\
  /2<=B h+B l<=1 /\ Rabs((B h+B l)-ln 2)<=bpow radix2 (-105).
Proof.
  destruct normal_ln2_hi_ok as[Fh H],normal_ln2_lo_ok as[Fl L].
  pose proof(two_sum_ieee normal_ln2_hi normal_ln2_lo Fh Fl
    ltac:(rewrite H;interval with(i_prec 80))ltac:(rewrite L;interval with(i_prec 80)))as Sum.
  unfold normal_ln2_constant64;destruct(two_sum64 normal_ln2_hi normal_ln2_lo)as[h l].
  destruct Sum as[Fhigh [Flow [High Total]]].
  assert(Range : /2<=B h+B l<=1)by(rewrite Total,H,L;split;interval with(i_prec 80)).
  assert(Norm : B h=rndF(B h+B l))by(rewrite Total;exact High).
  assert(Hi : Rabs(B h)<=1).
  { rewrite Norm;change 1 with(bpow radix2 0);apply normal_center_round_bound;[change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra|lia]. }
  pose proof(rnd_err_below(B h+B l)0 ltac:(lia)
    ltac:(change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra))as Rounded.
  rewrite <-Norm in Rounded;change(0-54)%Z with(-54)%Z in Rounded.
  assert(Lo : Rabs(B l)<=bpow radix2 (-54)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  assert(Error : Rabs((B h+B l)-ln 2)<=bpow radix2 (-105)).
  { rewrite Total;pose proof normal_ln2_dw_error as Relative.
    replace(B normal_ln2_hi+B normal_ln2_lo-ln 2)with
      (((B normal_ln2_hi+B normal_ln2_lo)/ln 2-1)*ln 2)by(field;interval with(i_prec 80)).
    rewrite Rabs_mult,(Rabs_pos_eq(ln 2))by(interval with(i_prec 80)).
    assert(0<=ln 2<=1)by(split;interval with(i_prec 80));pose proof(Rabs_pos((B normal_ln2_hi+B normal_ln2_lo)/ln 2-1));bpow_num_all;nra. }
  repeat split;tauto.
Qed.

Definition normal_log_tail_factor64 x :=
  let '(a,b):=normal_log_erfcx64 x in let '(c,d):=normal_ln2_constant64 in sub64 a b c d.

Theorem normal_log_tail_factor_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_log_tail_factor64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ Rabs(B h)<=16 /\ Rabs(B l)<=bpow radix2 (-50) /\
  Rabs((B h+B l)-(ln(gaussian_erfcx(B x/sqrt 2))-ln 2))<=
    bpow radix2 (-64)*Rabs(ln(gaussian_erfcx(B x/sqrt 2)))+bpow radix2 (-63).
Proof.
  intros Fx X;pose proof(normal_log_erfcx_ieee x Fx X)as Log;pose proof normal_ln2_constant_ieee as Constant.
  unfold normal_log_tail_factor64;destruct(normal_log_erfcx64 x)as[a b];destruct normal_ln2_constant64 as[c d].
  destruct Log as[Fa [Fb [Anorm [A [Bl LogError]]]]].
  destruct Constant as[Fc [Fd [Cnorm [C [Dl [Csum ConstantError]]]]]].
  assert(Z : /3<=B x/sqrt 2<=27)by(split;interval with(i_prec 80)).
  assert(F : /256<=gaussian_erfcx(B x/sqrt 2)<=3/4).
  { split;[apply normal_erfcx_compact_lower;split;lra|apply normal_erfcx_log_upper;exact(proj1 Z)]. }
  set(v:=ln(gaussian_erfcx(B x/sqrt 2)))in *.
  assert(V : -6<=v<= -/4)by(unfold v;split;interval with(i_prec 80)).
  assert(Asum : -8<=B a+B b<= -/8).
  { apply Rabs_le_inv in LogError;rewrite(Rabs_left1 v)in LogError by lra;bpow_num_all;split;lra. }
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(Normal : B(fneg c)=rndF(B(fneg c)+B(fneg d)))by(rewrite !Nb;apply dw_opp;exact Cnorm).
  assert(Cancel : Rabs(B a+B b)+Rabs(B(fneg c)+B(fneg d))<=4*Rabs(B a+B b+(B(fneg c)+B(fneg d)))).
  { rewrite !Nb;rewrite !Rabs_left1 by lra;lra. }
  pose proof(lf_add_pair a b (fneg c)(fneg d)Fa Fb (Nf c Fc)(Nf d Fd)Anorm Normal
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)])
    ltac:(rewrite Nb,Rabs_Ropp;eapply Rle_trans;[exact C|interval with(i_prec 80)])
    ltac:(rewrite Nb,Rabs_Ropp;eapply Rle_trans;[exact Dl|interval with(i_prec 80)])Cancel)as Addition.
  unfold sub64;destruct(add64 a b (fneg c)(fneg d))as[h l].
  destruct Addition as[Fh [Fl [Norm [e [E Value]]]]];rewrite !Nb in Value.
  assert(Evaluation : Rabs((B h+B l)-((B a+B b)-(B c+B d)))<=bpow radix2 (-100)).
  { rewrite Value;replace((B a+B b+(-B c+ -B d))*(1+e)-((B a+B b)-(B c+B d)))with
      (((B a+B b)-(B c+B d))*e)by ring.
    rewrite Rabs_mult,(Rabs_left1((B a+B b)-(B c+B d)))by lra.
    pose proof(Rabs_pos e);bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-(v-ln 2))<=bpow radix2 (-64)*Rabs v+bpow radix2 (-63)).
  { replace((B h+B l)-(v-ln 2))with
      (((B h+B l)-((B a+B b)-(B c+B d)))+((B a+B b)-v)-((B c+B d)-ln 2))by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp.
    eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|];bpow_num_all;lra. }
  assert(Sum : Rabs(B h+B l)<=16).
  { pose proof(Rabs_triang_inv(B h+B l)(v-ln 2));assert(0<=ln 2<=1)by(split;interval with(i_prec 80)).
    rewrite(Rabs_left1(v-ln 2)),(Rabs_left1 v)in * by lra;bpow_num_all;lra. }
  assert(Hi : Rabs(B h)<=16).
  { rewrite Norm;change 16 with(bpow radix2 4);apply normal_center_round_bound;[exact Sum|lia]. }
  pose proof(rnd_err_below(B h+B l)4 ltac:(lia)Sum)as Rounded;rewrite <-Norm in Rounded.
  change(4-54)%Z with(-50)%Z in Rounded.
  assert(Lo : Rabs(B l)<=bpow radix2 (-50)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;assumption.
Qed.
