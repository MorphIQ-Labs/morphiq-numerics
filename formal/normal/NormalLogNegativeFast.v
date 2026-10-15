(** Fast negative-input log-CDF retains the exact original half-square
    and adds the logarithmic erfcx factor without forming an underflowed tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxGaussianTarget NormalGaussianKernel NormalLogTailFactor
  NormalLogErfcx NormalErfcxFastScaled NormalLogAnalytic NormalTailAnalytic
  NormalCenterFastTail LnFastCompose NormalLogDecision.
Open Scope R_scope.

Definition normal_log_negative_fast64 x :=
  let '(h,l):=normal_half_square64 x in
  let '(a,b):=two_sum64 h l in
  let '(c,d):=normal_log_tail_factor64 x in add64 a b c d.

Theorem normal_log_negative_fast_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_log_negative_fast64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ Rabs(B h)<=1024 /\ Rabs(B l)<=bpow radix2 (-44) /\
  /4<=Rabs(ln(normal_tail(B x)))<=1024 /\
  Rabs((B h+B l)-ln(normal_tail(B x)))<=7*bpow radix2 (-65)*Rabs(ln(normal_tail(B x))).
Proof.
  intros Fx X;pose proof(normal_half_square_exact x Fx ltac:(bpow_num;split;lra))as Square.
  pose proof(normal_log_tail_factor_ieee x Fx X)as Factor.
  unfold normal_log_negative_fast64;destruct(normal_half_square64 x)as[sh sl].
  destruct Square as[Fsh [Fsl [Exact [Sh Sl]]]].
  pose proof(two_sum_ieee sh sl Fsh Fsl
    ltac:(eapply Rle_trans;[exact Sh|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Sl|interval with(i_prec 80)]))as SquareSum.
  destruct(two_sum64 sh sl)as[a b];destruct SquareSum as[Fa [Fb [High Total]]].
  assert(Anorm : B a=rndF(B a+B b))by(rewrite Total;exact High).
  assert(SquareValue : B a+B b= -B x*B x/2)by lra.
  assert(SquareRange : -685<=B a+B b<= -/8)by(rewrite SquareValue;split;nra).
  assert(A : Rabs(B a)<=1024).
  { rewrite Anorm;change 1024 with(bpow radix2 10);apply normal_center_round_bound;[change(bpow radix2 10)with 1024;apply Rabs_le;split;lra|lia]. }
  pose proof(rnd_err_below(B a+B b)10 ltac:(lia)
    ltac:(change(bpow radix2 10)with 1024;apply Rabs_le;split;lra))as SquareLow.
  rewrite <-Anorm in SquareLow;change(10-54)%Z with(-44)%Z in SquareLow.
  assert(Bl : Rabs(B b)<=bpow radix2 (-44)).
  { replace(B a-(B a+B b))with(-B b)in SquareLow by ring;rewrite Rabs_Ropp in SquareLow;exact SquareLow. }
  destruct(normal_log_tail_factor64 x)as[c d];destruct Factor as[Fc [Fd [Cnorm [C [Dl FactorError]]]]].
  assert(Z : /3<=B x/sqrt 2<=27)by(split;interval with(i_prec 80)).
  assert(F : /256<=gaussian_erfcx(B x/sqrt 2)<=3/4).
  { split;[apply normal_erfcx_compact_lower;split;lra|apply normal_erfcx_log_upper;exact(proj1 Z)]. }
  set(v:=ln(gaussian_erfcx(B x/sqrt 2)))in *.
  assert(V : -6<=v<= -/4)by(unfold v;split;interval with(i_prec 80)).
  assert(Ln2 : /2<=ln 2<=1)by(split;interval with(i_prec 80)).
  assert(Identity : ln(normal_tail(B x))= -B x*B x/2+v-ln 2).
  { rewrite normal_log_tail_identity by lra;unfold v,Rdiv.
    rewrite ln_mult,ln_Rinv by(try apply Rinv_0_lt_compat;lra);ring. }
  assert(Target : -700<=ln(normal_tail(B x))<= -3/4)by(rewrite Identity;split;nra).
  assert(Csum : -8<=B c+B d<= -/2).
  { apply Rabs_le_inv in FactorError;rewrite(Rabs_left1 v)in FactorError by lra;bpow_num_all;split;lra. }
  assert(Cancel : Rabs(B a+B b)+Rabs(B c+B d)<=4*Rabs(B a+B b+(B c+B d))).
  { rewrite !Rabs_left1 by lra;lra. }
  pose proof(lf_add_pair a b c d Fa Fb Fc Fd Anorm Cnorm
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact C|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Dl|interval with(i_prec 80)])Cancel)as Addition.
  destruct(add64 a b c d)as[h l];destruct Addition as[Fh [Fl [Norm [e [E Value]]]]].
  assert(Evaluation : Rabs((B h+B l)-(B a+B b+(B c+B d)))<=bpow radix2 (-93)).
  { rewrite Value;replace((B a+B b+(B c+B d))*(1+e)-(B a+B b+(B c+B d)))with
      ((B a+B b+(B c+B d))*e)by ring.
    rewrite Rabs_mult,(Rabs_left1(B a+B b+(B c+B d)))by lra.
    pose proof(Rabs_pos e);bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-ln(normal_tail(B x)))<=7*bpow radix2 (-65)*Rabs(ln(normal_tail(B x)))).
  { replace((B h+B l)-ln(normal_tail(B x)))with
      (((B h+B l)-(B a+B b+(B c+B d)))+((B c+B d)-(v-ln 2)))by(rewrite Identity,SquareValue;ring).
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite(Rabs_left1(ln(normal_tail(B x)))),(Rabs_left1 v)in * by lra.
    rewrite Identity;bpow_num_all;nra. }
  assert(Sum : Rabs(B h+B l)<=1024).
  { pose proof(Rabs_triang_inv(B h+B l)(ln(normal_tail(B x))));rewrite(Rabs_left1(ln(normal_tail(B x))))in * by lra;bpow_num_all;lra. }
  assert(Hi : Rabs(B h)<=1024).
  { rewrite Norm;change 1024 with(bpow radix2 10);apply normal_center_round_bound;[exact Sum|lia]. }
  pose proof(rnd_err_below(B h+B l)10 ltac:(lia)Sum)as Rounded;rewrite <-Norm in Rounded.
  change(10-54)%Z with(-44)%Z in Rounded.
  assert(Lo : Rabs(B l)<=bpow radix2 (-44)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;try assumption;rewrite Rabs_left1 by lra;lra.
Qed.

Definition normal_log_negative_decide64 x :=
  let '(h,l):=normal_log_negative_fast64 x in normal_log_decide64 h l.

Local Opaque normal_log_negative_fast64 normal_log_decide64.

Theorem normal_log_negative_decided x v : finite x -> /2<=B x<=37 ->
  normal_log_negative_decide64 x=Some v -> finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
  intros Fx X Decision;pose proof(normal_log_negative_fast_ieee x Fx X)as Log.
  unfold normal_log_negative_decide64 in Decision;destruct(normal_log_negative_fast64 x)as[h l].
  destruct Log as[Fh [Fl [_ [H [L [Target Error]]]]]].
  exact(normal_log_wide_decide_ok h l (ln(normal_tail(B x)))v Fh Fl H L Target Error Decision).
Qed.
