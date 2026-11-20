(** The actual accurate tangent quotient, quadrant and original sign. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import IEEE64.
Require Import AsinKernel TrigQuadrant TrigAccurate TrigReduction TrigWindow
  TrigTanDomain TrigTanQuotient.
Open Scope R_scope.

Definition trig_tan_selected k negative s c :=
  let q:=Q256.mul (trig_tan_num k s c) (AsinKernel.q_recip (trig_tan_den k s c)) in
  if xorb (Z.odd k) negative then Q256.neg_q q else q.
Definition trig_tan_real k negative r :=
  let q:=trig_tan_num k (sin r) (cos r)/trig_tan_den k (sin r) (cos r) in
  if xorb (Z.odd k) negative then -q else q.
Definition trig_tan_accurate64 bits negative :=
  let '(k,q):=trig_reduce64 bits in
  let '(s,c):=q_sin_cos q in trig_tan_selected k negative s c.

Lemma trig_tan_analytic n r negative : (0<=n)%Z ->
  trig_tan_den (n mod 4) (sin r) (cos r)<>0 ->
  trig_tan_real (n mod 4) negative r =
  tan(if negative then -(r+IZR n*(PI/2)) else r+IZR n*(PI/2)).
Proof.
  intros N D. destruct (trig_analytic_quadrant n r N) as [S C].
  pose proof (Z.mod_pos_bound n 4 ltac:(lia)) as K.
  assert (Cases:(n mod 4=0 \/ n mod 4=1 \/ n mod 4=2 \/ n mod 4=3)%Z) by lia.
  unfold tan. destruct negative; rewrite ?sin_neg,?cos_neg,S,C;
    destruct Cases as [H|[H|[H|H]]]; rewrite H in D |- *;
    cbn [trig_tan_real trig_tan_num trig_tan_den Z.odd quadrant_sin quadrant_cos xorb] in D |- *;
    unfold Rdiv; rewrite <-?Ropp_inv_permute by exact D; ring.
Qed.

Lemma trig_tan_selected_error k negative s c r : valid s -> valid c ->
  Rabs(qval s-sin r)<=bpow radix2 (-198)*Rabs(sin r) ->
  Rabs(qval c-cos r)<=bpow radix2 (-198)*Rabs(cos r) ->
  bpow radix2 (-63)<=Rabs(trig_tan_den k (sin r) (cos r))<=1 ->
  valid(trig_tan_selected k negative s c) /\
  Rabs(qval(trig_tan_selected k negative s c)-trig_tan_real k negative r)<=
    bpow radix2 (-196)*Rabs(trig_tan_real k negative r).
Proof.
  intros S C Es Ec Lower.
  assert (N:valid(trig_tan_num k s c)) by (unfold trig_tan_num; destruct (Z.odd k); assumption).
  assert (D:valid(trig_tan_den k s c)) by (unfold trig_tan_den; destruct (Z.odd k); assumption).
  assert (En:Rabs(qval(trig_tan_num k s c)-trig_tan_num k (sin r) (cos r))<=
    bpow radix2 (-198)*Rabs(trig_tan_num k (sin r) (cos r)))
    by (unfold trig_tan_num; destruct (Z.odd k); assumption).
  assert (Ed:Rabs(qval(trig_tan_den k s c)-trig_tan_den k (sin r) (cos r))<=
    bpow radix2 (-198)*Rabs(trig_tan_den k (sin r) (cos r)))
    by (unfold trig_tan_den; destruct (Z.odd k); assumption).
  destruct (trig_tan_recip_domain _ _ D Lower Ed) as [Min [F Nonzero]].
  destruct (trig_q_quotient_error _ _ _ _ N D Nonzero Min F En Ed) as [V Error].
  unfold trig_tan_selected,trig_tan_real. destruct (xorb (Z.odd k) negative).
  - destruct (neg_any _ V) as [Vn Val]. split; [exact Vn|]. rewrite Val.
    replace (-qval(Q256.mul (trig_tan_num k s c) (q_recip (trig_tan_den k s c)))-
      -(trig_tan_num k (sin r) (cos r)/trig_tan_den k (sin r) (cos r))) with
      (-(qval(Q256.mul (trig_tan_num k s c) (q_recip (trig_tan_den k s c)))-
      trig_tan_num k (sin r) (cos r)/trig_tan_den k (sin r) (cos r))) by ring.
    rewrite !Rabs_Ropp; exact Error.
  - split; assumption.
Qed.

Theorem trig_tan_accurate_value_correct x negative : finite x -> 0<=B x ->
  let q:=trig_tan_accurate64 (bits_of_b64 x) negative in
  let v:=tan(if negative then -B x else B x) in
  valid q /\ Rabs(qval q-v)<=bpow radix2 (-196)*Rabs v.
Proof.
  intros F X. cbv zeta.
  destruct (trig_reduce_correct x F X) as [n [q [Eq [V [Q [Near Err]]]]]].
  pose proof (trig_nearest_nonnegative (B x) n X Near) as N.
  set (t:=B x-IZR n*(PI/2)).
  pose proof (trig_nearest_remainder_range (B x) n Near) as Range. fold t in Range.
  assert (E:Rabs(qval q-t)<=bpow radix2 (-199)*Rabs t).
  { replace (bpow radix2 (-199)) with (/2^199) by (rewrite pow_IZR; reflexivity). exact Err. }
  destruct (trig_series_composed q t V ltac:(pose proof AsinFacts.quarter_pi_le; lra) Range E)
    as [Vs [Vc [Es Ec]]].
  pose proof (trig_tan_denominator_bound x n F X Near) as Lower. cbv zeta in Lower. fold t in Lower.
  unfold trig_tan_accurate64. rewrite Eq.
  destruct (q_sin_cos q) as [s c] eqn:Pair. cbn [fst snd] in Vs,Vc,Es,Ec.
  pose proof (trig_tan_selected_error (n mod 4) negative s c t Vs Vc Es Ec Lower) as Bound.
  assert (Dnonzero:trig_tan_den (n mod 4) (sin t) (cos t)<>0).
  { intro Zero. rewrite Zero,Rabs_R0 in Lower. pose proof (bpow_gt_0 radix2 (-63)); lra. }
  rewrite (trig_tan_analytic n t negative N Dnonzero) in Bound.
  replace (t+IZR n*(PI/2)) with (B x) in Bound by (unfold t; ring).
  exact Bound.
Qed.
