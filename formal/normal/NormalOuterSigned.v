(** Signed outer centered-CDF values use the same relative guard as the
    positive complements. Negation preserves normalization and error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
Require Import StageGappa NormalOuterFast NormalOuterFastRange NormalTailAnalytic
  NormalScaledRelativeDecision NormalRelativeDecision.
Open Scope R_scope.

Definition normal_outer_signed_fast64 (negative:bool) c x :=
  let '(h,l):=normal_outer_fast64 c x in
  if negative then(fneg h,fneg l)else(h,l).
Definition normal_outer_signed_target (negative:bool) c x :=
  if negative then -(B c-normal_tail(B x))else B c-normal_tail(B x).

Theorem normal_outer_signed_ieee negative c x : finite c -> /2<=B c<=1 -> finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_outer_signed_fast64 negative c x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ Rabs(B h)<=2 /\
  Rabs(B l)<=bpow radix2 (-53) /\
  3/16<=Rabs(normal_outer_signed_target negative c x)<=1 /\
  Rabs((B h+B l)-normal_outer_signed_target negative c x)<=
    3*bpow radix2 (-66)*Rabs(normal_outer_signed_target negative c x).
Proof.
  intros Fc C Fx X;pose proof(normal_outer_fast_ieee c x Fc C Fx X)as Outer.
  unfold normal_outer_signed_fast64,normal_outer_signed_target;destruct(normal_outer_fast64 c x)as[h l].
  destruct Outer as[Fh [Fl [Norm [H [L Error]]]]].
  pose proof(normal_outer_tail_tight(B x)(proj1 X))as Tail.
  assert(Target : 3/16<=B c-normal_tail(B x)<=1)by(split;lra).
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  destruct negative;cbn[fst snd].
  - rewrite !Nb,!Rabs_Ropp,(Rabs_pos_eq(B h)),(Rabs_pos_eq(B c-normal_tail(B x)))by lra.
    assert(Normal : -B h=rndF(-B h+ -B l))by(apply dw_opp;exact Norm).
    assert(High : Rabs(-B h)<=2)by(rewrite Rabs_Ropp,Rabs_pos_eq;lra).
    assert(Low : Rabs(-B l)<=bpow radix2 (-53))by(rewrite Rabs_Ropp;exact L).
    assert(E : Rabs((-B h+ -B l)- -(B c-normal_tail(B x)))<=3*bpow radix2 (-66)*(B c-normal_tail(B x))).
    { replace((-B h+ -B l)- -(B c-normal_tail(B x)))with(-((B h+B l)-(B c-normal_tail(B x))))by ring.
      rewrite Rabs_Ropp;exact Error. }
    repeat split;try tauto;apply Nf;assumption.
  - rewrite(Rabs_pos_eq(B h)),(Rabs_pos_eq(B c-normal_tail(B x)))by lra.
    repeat split;tauto.
Qed.

Definition normal_outer_signed_decide64 negative c x :=
  let '(h,l):=normal_outer_signed_fast64 negative c x in normal_relative_decide64 h l.

Local Opaque normal_outer_signed_fast64 normal_relative_decide64.

Theorem normal_outer_signed_decided negative c x v : finite c -> /2<=B c<=1 -> finite x -> /2<=B x<=37 ->
  normal_outer_signed_decide64 negative c x=Some v ->
  finite v /\ B v=rndF(normal_outer_signed_target negative c x).
Proof.
  intros Fc C Fx X Decision;pose proof(normal_outer_signed_ieee negative c x Fc C Fx X)as Outer.
  unfold normal_outer_signed_decide64 in Decision;destruct(normal_outer_signed_fast64 negative c x)as[h l].
  destruct Outer as[Fh [Fl [_ [H [L [Target Error]]]]]].
  apply(normal_scaled_relative_decide_ok h l 0 (normal_outer_signed_target negative c x)v);try assumption.
  - lia.
  - change(bpow radix2 0)with 1;lra.
  - change(0-51)%Z with(-51)%Z;eapply Rle_trans;[exact L|apply bpow_le;lia].
  - change(bpow radix2 0)with 1;split;lra.
Qed.
