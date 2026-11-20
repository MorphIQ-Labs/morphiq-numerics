(** The denominator selected by tan_parts is in Q256::recip's proved domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import TrigQuadrant TrigAccurate TrigClosest TrigRounding.
Open Scope R_scope.

Definition trig_tan_num {A:Type} (k:Z) (s c:A) := if Z.odd k then c else s.
Definition trig_tan_den {A:Type} (k:Z) (s c:A) := if Z.odd k then s else c.

Lemma trig_nearest_remainder_range x n : -/2<x*(2/PI)-IZR n</2 ->
  Rabs(x-IZR n*(PI/2))<=0.7854.
Proof.
  intro Near. assert (Pi:0<PI) by exact PI_RGT_0.
  replace (x-IZR n*(PI/2)) with ((x*(2/PI)-IZR n)*(PI/2)) by (field; lra).
  rewrite Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
  assert (A:Rabs(x*(2/PI)-IZR n)<=/2) by (apply Rabs_le; lra).
  pose proof AsinFacts.quarter_pi_le. nra.
Qed.

Lemma trig_odd_nearest_large x n : 0<=x -> -/2<x*(2/PI)-IZR n</2 ->
  Z.odd (n mod 4)=true -> PI/4<=x.
Proof.
  intros X Near Odd. pose proof (trig_nearest_nonnegative x n X Near) as N.
  assert (Notzero:n<>0%Z) by (intro Zero; rewrite Zero in Odd; discriminate).
  assert (One:1<=IZR n) by (change (IZR 1<=IZR n); apply IZR_le; lia).
  assert (Pi:0<PI) by exact PI_RGT_0.
  assert (Id:(x*(2/PI))*(PI/2)=x) by (field; lra).
  nra.
Qed.

Theorem trig_tan_denominator_bound x n : finite x -> 0<=B x ->
  -/2<B x*(2/PI)-IZR n</2 ->
  let t:=B x-IZR n*(PI/2) in
  bpow radix2 (-63)<=Rabs(trig_tan_den (n mod 4) (sin t) (cos t))<=1.
Proof.
  intros F X Near. cbv zeta.
  set (t:=B x-IZR n*(PI/2)).
  pose proof (trig_nearest_remainder_range (B x) n Near) as Range. fold t in Range.
  destruct (trig_small_bounds t Range) as [Sin Cos].
  unfold trig_tan_den. destruct (Z.odd (n mod 4)) eqn:Odd; split.
  - pose proof (trig_odd_nearest_large (B x) n X Near Odd) as Large.
    pose proof (trig_binary64_separation x n F Large) as Gap.
    assert (Pi:1<=PI/2) by interval.
    assert (T:bpow radix2 (-62)<=Rabs t).
    { unfold t. replace (B x-IZR n*(PI/2)) with ((B x*(2/PI)-IZR n)*(PI/2))
        by (field; pose proof PI_RGT_0; lra).
      rewrite Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
      replace (/2^62) with (bpow radix2 (-62)) in Gap by (rewrite pow_IZR; reflexivity).
      pose proof (Rabs_pos (B x*(2/PI)-IZR n)); nra. }
    assert (Budget:bpow radix2 (-63)<=0.89*bpow radix2 (-62)) by interval.
    lra.
  - apply Rabs_le; apply SIN_bound.
  - assert (Small:bpow radix2 (-63)<=0.69).
    { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia|change (/2<=0.69); lra]. }
    pose proof (Rle_abs (cos t)); lra.
  - apply Rabs_le; apply COS_bound.
Qed.

Lemma trig_tan_recip_domain q v : valid q -> bpow radix2 (-63)<=Rabs v<=1 ->
  Rabs(qval q-v)<=bpow radix2 (-198)*Rabs v ->
  bpow radix2 (-1022)<=Rabs(qval q) /\ finite(Q256.to_f64 q) /\ v<>0.
Proof.
  intros V [Lower Upper] Error.
  assert (Small:bpow radix2 (-198)<=/2) by (change (/2) with (bpow radix2 (-1)); apply bpow_le; lia).
  assert (Abs:Rabs v<=Rabs(qval q-v)+Rabs(qval q)).
  { pose proof (Rabs_triang (v-qval q) (qval q)) as T.
    replace (v-qval q+qval q) with v in T by ring. rewrite Rabs_minus_sym in T. exact T. }
  assert (Half:bpow radix2 (-64)<=Rabs(qval q)).
  { assert (Budget:bpow radix2 (-64)=/2*bpow radix2 (-63)) by (change (/2) with (bpow radix2 (-1)); rewrite <-bpow_plus; reflexivity).
    pose proof (Rabs_pos v). rewrite Budget. nra. }
  split.
  - apply Rle_trans with (bpow radix2 (-64)); [apply bpow_le; lia|exact Half].
  - split.
    + exact (proj1 (trig_accurate_round q v V Upper Error)).
    + intro Zero. rewrite Zero,Rabs_R0 in Lower. pose proof (bpow_gt_0 radix2 (-63)); lra.
Qed.
