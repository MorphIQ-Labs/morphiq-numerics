(** Acceptance of the fast normal tail, including subnormal guard products.
    The external exponent bounds the rounding of guard and endpoint words. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision NormalDensityDecision NormalFastDecision NormalRelativeDecision
  NormalTailFast NormalTailAnalytic.
Open Scope R_scope.

Theorem normal_tail_relative_decide_ok h l k target v : finite h -> finite l ->
  (-991<=k<=0)%Z -> 0<=B h<=8*bpow radix2 k -> Rabs(B l)<=bpow radix2 (k-51) ->
  bpow radix2 k/4096<=target<=6*bpow radix2 k ->
  Rabs((B h+B l)-target)<=3*bpow radix2 (-66)*target ->
  normal_relative_decide64 h l=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl K H L Target Error Decision;unfold normal_relative_decide64 in Decision.
  assert(Fabs : finite(b64_abs h))by(unfold b64_abs;destruct h;exact Fh).
  destruct(erfcx_pow2_ok (-64)ltac:(lia))as[Fc C].
  set(s:=bpow radix2 k)in *;assert(S : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert(Product : Rabs(B(b64_abs h)*B(erfcx_pow2(-64)))<=bpow radix2 (k-30)).
  { rewrite B_abs,C,Rabs_mult,Rabs_Rabsolu,(Rabs_pos_eq(bpow radix2 (-64))),(Rabs_pos_eq(B h))by(pose proof(bpow_gt_0 radix2 (-64));lra).
    replace(k-30)%Z with(k+ -30)%Z by ring;rewrite bpow_plus;fold s;bpow_num_all;nra. }
  assert(Small : bpow radix2 (k-30)<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
  destruct(fmul16 (b64_abs h)(erfcx_pow2(-64))Fabs Fc ltac:(lra))as[Fe Value].
  fold(normal_density_guard64(b64_abs h))in Fe,Value.
  pose proof(rnd_err_below _ (k-30)ltac:(lia)Product)as Rounded.
  rewrite <-Value,B_abs,C,(Rabs_pos_eq(B h))in Rounded by lra.
  replace(k-30-54)%Z with(k-84)%Z in Rounded by ring;apply Rabs_le_inv in Rounded.
  assert(HighTarget : target<=B h+3*bpow radix2 (-66)*target+bpow radix2 (k-51)).
  { pose proof(Rabs_triang_inv target (B h+B l))as Difference.
    rewrite Rabs_minus_sym,(Rabs_pos_eq target)in Difference by nra.
    pose proof(Rabs_triang(B h)(B l));rewrite(Rabs_pos_eq(B h))in H0 by lra;lra. }
  assert(Guard : 0<=B(normal_density_guard64(b64_abs h)) /\
    3*bpow radix2 (-66)*target+bpow radix2 (k-84)<=B(normal_density_guard64(b64_abs h)) /\
    B(normal_density_guard64(b64_abs h))<=bpow radix2 (k-60)).
  { replace(k-84)%Z with(k+ -84)%Z in * by ring;replace(k-51)%Z with(k+ -51)%Z in HighTarget by ring.
    replace(k-60)%Z with(k+ -60)%Z by ring;rewrite !bpow_plus in Rounded,HighTarget|-*;fold s in Rounded,HighTarget|-*.
    bpow_num_all;repeat split;try nra.
    rewrite bpow_plus;fold s;bpow_num;nra. }
  destruct Guard as[E [Budget Upper]].
  apply(normal_interval_decide_ok h l (normal_density_guard64(b64_abs h))target
    (3*bpow radix2 (-66)*target)(k-30)v);try assumption.
  - rewrite Rabs_pos_eq by lra;nra.
  - lia.
  - replace(k-51)%Z with(k+ -51)%Z in L by ring;replace(k-60)%Z with(k+ -60)%Z in Upper by ring.
    replace(k-30)%Z with(k+ -30)%Z by ring;rewrite bpow_plus in L,Upper|-*;fold s in L,Upper|-*;bpow_num_all;nra.
  - replace(k-30-54)%Z with(k-84)%Z by ring;exact Budget.
  - rewrite Rabs_minus_sym;exact Error.
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
