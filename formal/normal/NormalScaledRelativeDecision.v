(** A signed relative guard with an external scale. Its rounding bound
    includes subnormal guard products and both endpoint low words. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision NormalDensityDecision NormalFastDecision NormalRelativeDecision.
Open Scope R_scope.

Theorem normal_scaled_relative_decide_ok h l k target v : finite h -> finite l ->
  (-991<=k<=0)%Z -> Rabs(B h)<=8*bpow radix2 k -> Rabs(B l)<=bpow radix2 (k-51) ->
  bpow radix2 k/4096<=Rabs target<=6*bpow radix2 k ->
  Rabs((B h+B l)-target)<=3*bpow radix2 (-66)*Rabs target ->
  normal_relative_decide64 h l=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl K H L Target Error Decision;unfold normal_relative_decide64 in Decision.
  assert(Fabs : finite(b64_abs h))by(unfold b64_abs;destruct h;exact Fh).
  pose proof(Rabs_pos(B h))as HighNonnegative.
  destruct(erfcx_pow2_ok (-64)ltac:(lia))as[Fc C].
  set(s:=bpow radix2 k)in *;assert(S : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert(Product : Rabs(B(b64_abs h)*B(erfcx_pow2(-64)))<=bpow radix2 (k-30)).
  { rewrite B_abs,C,Rabs_mult,Rabs_Rabsolu,(Rabs_pos_eq(bpow radix2 (-64)))by(pose proof(bpow_gt_0 radix2 (-64));lra).
    replace(k-30)%Z with(k+ -30)%Z by ring;rewrite bpow_plus;fold s;bpow_num_all;nra. }
  assert(Small : bpow radix2 (k-30)<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
  destruct(fmul16 (b64_abs h)(erfcx_pow2(-64))Fabs Fc ltac:(lra))as[Fe Value].
  fold(normal_density_guard64(b64_abs h))in Fe,Value.
  pose proof(rnd_err_below _ (k-30)ltac:(lia)Product)as Rounded.
  rewrite <-Value,B_abs,C in Rounded by lra.
  replace(k-30-54)%Z with(k-84)%Z in Rounded by ring;apply Rabs_le_inv in Rounded.
  assert(HighTarget : Rabs target<=Rabs(B h)+3*bpow radix2 (-66)*Rabs target+bpow radix2 (k-51)).
  { pose proof(Rabs_triang_inv target (B h+B l))as Difference.
    rewrite Rabs_minus_sym in Difference.
    pose proof(Rabs_triang(B h)(B l));lra. }
  assert(Guard : 0<=B(normal_density_guard64(b64_abs h)) /\
    3*bpow radix2 (-66)*Rabs target+bpow radix2 (k-84)<=B(normal_density_guard64(b64_abs h)) /\
    B(normal_density_guard64(b64_abs h))<=bpow radix2 (k-60)).
  { replace(k-84)%Z with(k+ -84)%Z in * by ring;replace(k-51)%Z with(k+ -51)%Z in HighTarget by ring.
    replace(k-60)%Z with(k+ -60)%Z by ring;rewrite !bpow_plus in Rounded,HighTarget|-*;fold s in Rounded,HighTarget|-*.
    bpow_num_all;repeat split;try nra.
    rewrite bpow_plus;fold s;bpow_num;nra. }
  destruct Guard as[E [Budget Upper]].
  apply(normal_interval_decide_ok h l (normal_density_guard64(b64_abs h))target
    (3*bpow radix2 (-66)*Rabs target)(k-30)v);try assumption.
  - nra.
  - lia.
  - replace(k-51)%Z with(k+ -51)%Z in L by ring;replace(k-60)%Z with(k+ -60)%Z in Upper by ring.
    replace(k-30)%Z with(k+ -30)%Z by ring;rewrite bpow_plus in L,Upper|-*;fold s in L,Upper|-*;bpow_num_all;nra.
  - replace(k-30-54)%Z with(k-84)%Z by ring;exact Budget.
  - rewrite Rabs_minus_sym;exact Error.
Qed.

