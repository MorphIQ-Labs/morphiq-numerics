(** Central CDF composition: add one half to the unrounded centered value.
    The computed relative guard also covers the final double-word addition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant.
Require Import StageGappa ExpFast NormalCentered NormalAccurateCentralCdf NormalCenterCentral
  NormalCenterFastTail NormalRelativeDecision.
Open Scope R_scope.

Definition normal_cdf_central_fast64 x :=
  let '(h,l):=normal_center_central64 x in add_f64_64 h l ExpFast.c_half.

Theorem normal_cdf_central_fast_ieee x : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_cdf_central_fast64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ /8<=B h<=1 /\
  Rabs(B l)<=bpow radix2 (-54) /\ Rabs((B h+B l)-normal_cdf(B x))<=bpow radix2 (-68).
Proof.
  intros Fx X;pose proof(normal_center_central_ieee x Fx X)as Center.
  unfold normal_cdf_central_fast64;destruct(normal_center_central64 x)as[a b].
  destruct Center as[Fa [Fb [Anorm [A [Bl CenterError]]]]].
  assert(Half : B ExpFast.c_half=/2)by(rewrite ExpFast.c_half_val;field).
  pose proof(normal_central_cdf_range (B x)(proj2 X))as Target.
  assert(Center : -/4<=normal_center(B x)<=/4).
  { pose proof(normal_center_range (B x)(proj2 X));apply Rabs_le_inv in H;exact H. }
  assert(SumRange : /8<=B a+B b+B ExpFast.c_half<=1).
  { apply Rabs_le_inv in CenterError;rewrite Half;bpow_num_all;split;lra. }
  assert(Bound : forall w,Rabs(B w)<=1 -> bnd 1 0 (B w)).
  { intros w W;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;exact W. }
  destruct(add_f64_64_ok 1 0 a b ExpFast.c_half Fa Fb ExpFast.c_half_finite
    (Bound a ltac:(lra))(Bound b ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)]))
    (Bound _ ltac:(rewrite Half;interval with(i_prec 80)))
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[Fh [Fl Value]].
  pose proof(add_f64_dw (B a)(B b)(B ExpFast.c_half)(B_fmt a)(B_fmt b)(B_fmt _)Anorm)as Normalized.
  pose proof(add_f64_ieee a b ExpFast.c_half Fa Fb ExpFast.c_half_finite Anorm
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)])
    ltac:(rewrite Half;interval with(i_prec 80)))as Relative.
  rewrite <-Value in Normalized;destruct(add_f64_64 a b ExpFast.c_half)as[h l];cbn[fst snd]in *.
  destruct Relative as[_ [_ Relative]].
  assert(Evaluation : Rabs((B h+B l)-(B a+B b+B ExpFast.c_half))<=bpow radix2 (-105)).
  { replace((B h+B l)-(B a+B b+B ExpFast.c_half))with
      ((((B h+B l)-(B a+B b+B ExpFast.c_half))/(B a+B b+B ExpFast.c_half))*(B a+B b+B ExpFast.c_half))by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq(B a+B b+B ExpFast.c_half))by lra.
    pose proof(Rabs_pos(((B h+B l)-(B a+B b+B ExpFast.c_half))/(B a+B b+B ExpFast.c_half))).
    unfold prec in Relative;change (- (53))%Z with (-53)%Z in Relative;bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-normal_cdf(B x))<=bpow radix2 (-68)).
  { unfold normal_cdf;replace((B h+B l)-(/2+normal_center(B x)))with
      (((B h+B l)-(B a+B b+B ExpFast.c_half))+((B a+B b)-normal_center(B x)))by(rewrite Half;ring).
    eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  assert(Range : /8<=B h+B l<=1).
  { apply Rabs_le_inv in Error;bpow_num_all;split;lra. }
  assert(High : /8<=B h<=1).
  { rewrite Normalized;split.
    - change(/8)with(bpow radix2 (-3));apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 1 with(bpow radix2 0);apply round_le_generic;[exact _|exact _| |exact(proj2 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_err_below(B h+B l)0 ltac:(lia)ltac:(change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra))as Rounded.
  rewrite <-Normalized in Rounded;change(0-54)%Z with(-54)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-54)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;tauto.
Qed.

Definition normal_cdf_central_decide64 x :=
  let '(h,l):=normal_cdf_central_fast64 x in normal_relative_decide64 h l.

Local Opaque normal_cdf_central_fast64 normal_relative_decide64.

Theorem normal_cdf_central_decided x v : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  normal_cdf_central_decide64 x=Some v -> finite v /\ B v=rndF(normal_cdf(B x)).
Proof.
  intros Fx X Decision;pose proof(normal_cdf_central_fast_ieee x Fx X)as Fast.
  unfold normal_cdf_central_decide64 in Decision;destruct(normal_cdf_central_fast64 x)as[h l].
  destruct Fast as[Fh [Fl [_ [H [L Error]]]]].
  apply(normal_relative_decide_ok h l 0 (normal_cdf(B x))v Fh Fl ltac:(lia));try assumption.
  - change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra.
  - change(0-52)%Z with(-52)%Z;eapply Rle_trans;[exact L|];apply bpow_le;lia.
Qed.
