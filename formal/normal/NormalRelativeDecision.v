(** The shared signed relative guard used by the centered-CDF branches. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa NormalFastDecision NormalDensityDecision.
Open Scope R_scope.

Definition normal_relative_decide64 h l :=
  normal_interval_decide64 h l (normal_density_guard64(b64_abs h)).

Theorem normal_relative_decide_ok h l k target v :
  finite h -> finite l -> (-1000<=k<=0)%Z ->
  bpow radix2 k/8<=Rabs(B h)<=4*bpow radix2 k -> Rabs(B l)<=bpow radix2 (k-52) ->
  Rabs((B h+B l)-target)<=bpow radix2 (k-68) ->
  normal_relative_decide64 h l=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl K H L Error Decision;unfold normal_relative_decide64 in Decision.
  assert(Fabs : finite(b64_abs h))by(unfold b64_abs;destruct h;simpl in *;congruence).
  pose proof(normal_density_guard_bounds (b64_abs h)k Fabs K)as Guard.
  rewrite B_abs in Guard;specialize(Guard H);destruct Guard as[Fe [E [Budget Upper]]].
  apply(normal_interval_decide_ok h l (normal_density_guard64(b64_abs h))target
    (bpow radix2 (k-68))(k-21)v);try assumption.
  - assert(bpow radix2 k<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia);lra.
  - lia.
  - replace(k-52)%Z with(k+ -52)%Z in L by ring;replace(k-61)%Z with(k+ -61)%Z in Upper by ring.
    replace(k-21)%Z with(k+ -21)%Z by ring;rewrite bpow_plus in L,Upper|-*.
    assert(bpow radix2 (-52)+bpow radix2 (-61)<=bpow radix2 (-21))by(bpow_num;interval with(i_prec 100)).
    pose proof(bpow_gt_0 radix2 k);nra.
  - replace(k-21-54)%Z with(k-75)%Z by ring;exact Budget.
  - rewrite Rabs_minus_sym;exact Error.
Qed.
