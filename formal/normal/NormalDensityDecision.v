(** The fast density guard covers both the composition error and the
    rounded endpoint arithmetic. An accepted test is correctly rounded. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa ErfcxDecision NormalDensityFast NormalAccurateDensity NormalFastDecision.
Open Scope R_scope.

Definition normal_density_guard64 h := fmul h (erfcx_pow2 (-64)).

Lemma normal_density_guard_bounds h k : finite h -> (-1000<=k<=0)%Z ->
  bpow radix2 k/8<=B h<=4*bpow radix2 k ->
  finite(normal_density_guard64 h) /\ 0<=B(normal_density_guard64 h) /\
  bpow radix2 (k-68)+bpow radix2 (k-75)<=B(normal_density_guard64 h) /\
  B(normal_density_guard64 h)<=bpow radix2 (k-61).
Proof.
  intros F K H;destruct(erfcx_pow2_ok (-64)ltac:(lia))as[Fc C].
  set(s:=bpow radix2 k)in *;assert(S : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert (Product : Rabs(B h*B(erfcx_pow2(-64)))<=bpow radix2 (k-21)).
  { rewrite C,Rabs_mult,(Rabs_pos_eq(B h)),(Rabs_pos_eq(bpow radix2 (-64)))by(pose proof(bpow_gt_0 radix2 (-64));lra).
    replace(k-21)%Z with(k+ -21)%Z by ring;rewrite bpow_plus;fold s;bpow_num_all;nra. }
  assert (Small : bpow radix2 (k-21)<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
  destruct(fmul16 h (erfcx_pow2(-64))F Fc ltac:(lra))as[Fe Value];fold(normal_density_guard64 h)in Fe,Value.
  pose proof(rnd_err_below _ (k-21)ltac:(lia)Product)as Error;rewrite <-Value,C in Error.
  replace(k-21-54)%Z with(k-75)%Z in Error by ring;apply Rabs_le_inv in Error.
  split;[exact Fe|].
  replace(k-75)%Z with(k+ -75)%Z in * by ring;replace(k-68)%Z with(k+ -68)%Z by ring;replace(k-61)%Z with(k+ -61)%Z by ring.
  rewrite bpow_plus in Error;fold s in Error;bpow_num_all.
  repeat split;rewrite ?bpow_plus;fold s;bpow_num;nra.
Qed.

Definition normal_density_fast_decide64 x :=
  let '(h,l,k):=normal_density_fast64 x in normal_interval_decide64 h l (normal_density_guard64 h).

Local Opaque normal_density_fast64 normal_density_guard64 normal_interval_decide64.

Theorem normal_density_fast_decided x v : finite x -> bpow radix2 (-33)<=B x<=37 ->
  normal_density_fast_decide64 x=Some v -> finite v /\ B v=rndF(normal_density(B x)).
Proof.
  intros F X Decision;pose proof(normal_density_fast_ieee x F X)as Fast.
  unfold normal_density_fast_decide64 in Decision;destruct(normal_density_fast64 x)as[[h l]k].
  destruct Fast as[Fh [Fl [K [H [L [Norm Error]]]]]].
  destruct(normal_density_guard_bounds h k Fh K H)as[Fe [E [Budget Upper]]].
  apply(normal_interval_decide_ok h l (normal_density_guard64 h)(normal_density(B x))
    (bpow radix2 (k-68))(k-21)v);try assumption.
  - rewrite Rabs_pos_eq;[|pose proof(bpow_gt_0 radix2 k);lra].
    assert(bpow radix2 k<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia);lra.
  - lia.
  - replace(k-52)%Z with(k+ -52)%Z in L by ring;replace(k-61)%Z with(k+ -61)%Z in Upper by ring.
    replace(k-21)%Z with(k+ -21)%Z by ring;rewrite bpow_plus in L,Upper|-*.
    assert(bpow radix2 (-52)+bpow radix2 (-61)<=bpow radix2 (-21))by(bpow_num;interval with(i_prec 100)).
    pose proof(bpow_gt_0 radix2 k);nra.
  - replace(k-21-54)%Z with(k-75)%Z by ring;exact Budget.
  - rewrite Rabs_minus_sym;exact Error.
Qed.
