(** Acceptance of the fast normal tail, including subnormal guard products.
    The external exponent bounds the rounding of guard and endpoint words. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision NormalDensityDecision NormalFastDecision NormalRelativeDecision
  NormalTailFast NormalTailAnalytic NormalScaledRelativeDecision.
Open Scope R_scope.

Theorem normal_tail_relative_decide_ok h l k target v : finite h -> finite l ->
  (-991<=k<=0)%Z -> 0<=B h<=8*bpow radix2 k -> Rabs(B l)<=bpow radix2 (k-51) ->
  bpow radix2 k/4096<=target<=6*bpow radix2 k ->
  Rabs((B h+B l)-target)<=3*bpow radix2 (-66)*target ->
  normal_relative_decide64 h l=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl K H L Target Error Decision.
  assert(Positive : 0<=target)by(pose proof(bpow_gt_0 radix2 k);nra).
  apply(normal_scaled_relative_decide_ok h l k target v);try assumption;
    rewrite ?(Rabs_pos_eq(B h)),?(Rabs_pos_eq target)by lra;tauto.
Qed.

Definition normal_tail_decide64 x :=
  let '(h,l,k):=normal_tail_fast64 x in normal_relative_decide64 h l.

Local Opaque normal_tail_fast64 normal_relative_decide64.

Theorem normal_tail_fast_decided x v : finite x -> /2<=B x<=37 ->
  normal_tail_decide64 x=Some v -> finite v /\ B v=rndF(normal_tail(B x)).
Proof.
  intros Fx X Decision;pose proof(normal_tail_fast_ieee x Fx X)as Tail.
  unfold normal_tail_decide64 in Decision;destruct(normal_tail_fast64 x)as[[h l]k].
  destruct Tail as[Fh [Fl [K [_ [H [L [Target Error]]]]]]].
  apply(normal_tail_relative_decide_ok h l k (normal_tail(B x))v);try assumption.
  - lia.
  - eapply Rle_trans;[exact Error|].
    assert(0<=normal_tail(B x))by(pose proof(bpow_gt_0 radix2 k);nra).
    bpow_num_all;nra.
Qed.
