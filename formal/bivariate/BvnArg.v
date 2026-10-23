(** The computed exponent argument of one quadrature node.

    The exponent of the Plackett integrand at [S = sin t] is
    [Q(S) = (r/2 - p S)/(1 - S^2) = d/(4 (1 - S)) + m/(4 (1 + S))] with
    [d = (x - y)^2] and [m = (x + y)^2], two non-negative terms. The Rust forms
    [d' p + m' q] from the rounded differences and sums, squared, and the
    per-correlation [p = 0.25/(1 - s)] and [q = 0.25/(1 + s)] of the rounded
    sine [s]. This file bounds its distance from [Q(s)] by [7.1 u Q(s)] plus a
    subnormal-scale constant. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import BvnRound BvnQ.
Open Scope R_scope.

Definition argnc (x y sh : R) : R :=
  rndF (rndF (rndF (rndF (x - y) * rndF (x - y)) * rndF (/ 4 / rndF (1 - sh)))
      + rndF (rndF (rndF (x + y) * rndF (x + y)) * rndF (/ 4 / rndF (1 + sh)))).

Lemma fmtF_one : fmtF 1.
Proof.
  replace 1 with (bpow radix2 0) by reflexivity.
  apply generic_format_bpow. unfold FLT_exp. apply Z.max_lub; lia.
Qed.

(** The product of six near-one factors, over a seventh. *)
Lemma factor_range d1 d2 db d3 ds da :
  Rabs d1 <= u -> Rabs d2 <= u -> Rabs db <= u -> Rabs d3 <= u -> Rabs ds <= u -> Rabs da <= u ->
  Rabs ((1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds) / (1 + da) - 1) <= 71 / 10 * u.
Proof.
  intros H1 H2 Hb H3 Hs Ha.
  pose proof u_pos as Hu. pose proof u_val as Huv.
  assert (Hu1 : u < / 1000) by (rewrite Huv; lra).
  apply Rabs_le_between in H1. apply Rabs_le_between in H2. apply Rabs_le_between in Hb.
  apply Rabs_le_between in H3. apply Rabs_le_between in Hs. apply Rabs_le_between in Ha.
  destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b]. destruct Hb as [Hba Hbb].
  destruct H3 as [H3a H3b]. destruct Hs as [Hsa Hsb]. destruct Ha as [Haa Hab].
  set (N := (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds)).
  assert (HNu : N <= (1 + u) ^ 6).
  { unfold N.
    assert (h1 : (1 + d1) * (1 + d1) <= (1 + u) * (1 + u)) by (apply Rmult_le_compat; lra).
    assert (h2 : (1 + d1) * (1 + d1) * (1 + d2) <= (1 + u) * (1 + u) * (1 + u))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact h1 | lra]).
    assert (h3 : (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) <= (1 + u) * (1 + u) * (1 + u) * (1 + u))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos|]; lra | lra | exact h2 | lra]).
    assert (h4 : (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) <= (1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]; lra | lra | exact h3 | lra]).
    assert (h5 : (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds) <= (1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]|]; lra | lra | exact h4 | lra]).
    replace ((1 + u) ^ 6) with ((1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u)) by ring. exact h5. }
  assert (HNl : (1 - u) ^ 6 <= N).
  { unfold N.
    assert (h1 : (1 - u) * (1 - u) <= (1 + d1) * (1 + d1)) by (apply Rmult_le_compat; lra).
    assert (h2 : (1 - u) * (1 - u) * (1 - u) <= (1 + d1) * (1 + d1) * (1 + d2))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact h1 | lra]).
    assert (h3 : (1 - u) * (1 - u) * (1 - u) * (1 - u) <= (1 + d1) * (1 + d1) * (1 + d2) * (1 + db))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos|]; lra | lra | exact h2 | lra]).
    assert (h4 : (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) <= (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]; lra | lra | exact h3 | lra]).
    assert (h5 : (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) <= (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds))
      by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]|]; lra | lra | exact h4 | lra]).
    replace ((1 - u) ^ 6) with ((1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u)) by ring. exact h5. }
  assert (Hup : (1 + u) ^ 6 / (1 - u) <= 1 + 71 / 10 * u) by (rewrite Huv; interval with (i_prec 100)).
  assert (Hlo : 1 - 71 / 10 * u <= (1 - u) ^ 6 / (1 + u)) by (rewrite Huv; interval with (i_prec 100)).
  assert (Hq1 : N / (1 + da) <= N / (1 - u)).
  { unfold Rdiv. apply Rmult_le_compat; [| left; apply Rinv_0_lt_compat; lra | lra | apply Rinv_le_contravar; lra].
    assert (0 <= (1 - u) ^ 6) by (apply pow_le; lra). lra. }
  assert (Hq2 : N / (1 + u) <= N / (1 + da)).
  { unfold Rdiv. apply Rmult_le_compat_l; [assert (0 <= (1 - u) ^ 6) by (apply pow_le; lra); lra | apply Rinv_le_contravar; lra]. }
  assert (Hq3 : N / (1 - u) <= (1 + u) ^ 6 / (1 - u)) by (unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact HNu]).
  assert (Hq4 : (1 - u) ^ 6 / (1 + u) <= N / (1 + u)) by (unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact HNl]).
  replace ((1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds) / (1 + da)) with (N / (1 + da)) by reflexivity.
  apply Rabs_le. split; lra.
Qed.

(** One of the two terms: [(a (1 + d1))^2 (1 + d2) + z2] times the table value
    [(1/4) / (c (1 + da)) (1 + db)], rounded. *)
Lemma branch a c e dh f P t d1 d2 z2 da db d3 z3 :
  e = a * (1 + d1) -> dh = e * e * (1 + d2) + z2 -> f = c * (1 + da) ->
  P = (/ 4 / f) * (1 + db) -> t = dh * P * (1 + d3) + z3 ->
  / 200 <= c -> c <= 2 ->
  Rabs d1 <= u -> Rabs d2 <= u -> Rabs da <= u -> Rabs db <= u -> Rabs d3 <= u ->
  Rabs z2 <= z -> Rabs z3 <= z ->
  exists zt, t = a * a * (/ 4 / c) * ((1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) / (1 + da)) + zt
             /\ Rabs zt <= 100 * z.
Proof.
  intros Ee Edh Ef EP Et Hc1 Hc2 H1 H2 Ha Hb H3 Hz2 Hz3.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (Hu1 : u < / 1000) by (rewrite Huv; lra).
  exists (z2 * P * (1 + d3) + z3). split.
  - assert (Hda : 1 + da <> 0) by (apply Rabs_le_between in Ha; apply Rgt_not_eq; lra).
    assert (Hc0 : c <> 0) by (apply Rgt_not_eq; lra).
    rewrite Et, Edh, Ee, EP, Ef. field. split; assumption.
  - assert (HP : Rabs P <= 51).
    { rewrite EP, Ef. apply Rabs_le_between in Ha. apply Rabs_le_between in Hb.
      destruct Ha as [Ha1 Ha2]. destruct Hb as [Hb1 Hb2].
      assert (Hcd : c * (1 + da) >= / 200 * (1 - u)).
      { apply Rle_ge. apply Rmult_le_compat; lra. }
      assert (Hpos : 0 < c * (1 + da)) by (apply Rmult_lt_0_compat; lra).
      assert (Hq : / 4 / (c * (1 + da)) <= 50.1).
      { apply Rmult_le_reg_r with (c * (1 + da)); [exact Hpos |].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; exact Hpos). nra. }
      assert (Hq0 : 0 <= / 4 / (c * (1 + da))) by (apply Rlt_le; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hpos]).
      rewrite Rabs_mult. rewrite (Rabs_pos_eq (/ 4 / (c * (1 + da)))) by exact Hq0.
      assert (Rabs (1 + db) <= 1 + u) by (apply Rabs_le; lra).
      nra. }
    eapply Rle_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult.
    assert (Rabs (1 + d3) <= 1 + u) by (apply Rabs_le_between in H3; apply Rabs_le; lra).
    pose proof (Rabs_pos P). pose proof (Rabs_pos z2). pose proof (Rabs_pos (1 + d3)).
    assert (Rabs z2 * Rabs P <= z * 51) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]).
    assert (Rabs z2 * Rabs P * Rabs (1 + d3) <= z * 51 * (1 + u)) by (apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | apply Rabs_pos | lra | lra]).
    nra.
Qed.

(** The identity that makes the exponent a sum of two non-negative terms. *)
Lemma Qf_split x y sh : 1 - sh <> 0 -> 1 + sh <> 0 ->
  Qf (x * x + y * y) (x * y) sh = (x - y) * (x - y) * (/ 4 / (1 - sh)) + (x + y) * (x + y) * (/ 4 / (1 + sh)).
Proof.
  intros H1 H2. unfold Qf.
  assert (H3 : 1 - sh * sh <> 0) by (replace (1 - sh * sh) with ((1 - sh) * (1 + sh)) by ring; apply Rmult_integral_contrapositive; split; assumption).
  field. repeat split; assumption.
Qed.

Lemma arg_nc x y sh sg : fmtF x -> fmtF y -> fmtF sh -> Rabs x <= 64 -> Rabs y <= 64 ->
  Rabs sh <= sg -> sg <= 99 / 100 ->
  Rabs (argnc x y sh - Qf (x * x + y * y) (x * y) sh) <= 71 / 10 * u * Qf (x * x + y * y) (x * y) sh + 300 * z.
Proof.
  intros Fx Fy Fs Hx Hy Hs Hsg.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (Hu1 : u < / 1000) by (rewrite Huv; lra).
  apply Rabs_le_between in Hs. destruct Hs as [Hs1 Hs2].
  assert (Hc1 : / 200 <= 1 - sh <= 2) by (split; lra).
  assert (Hc2 : / 200 <= 1 + sh <= 2) by (split; lra).
  destruct Hc1 as [Hc1a Hc1b]. destruct Hc2 as [Hc2a Hc2b].
  (* the difference branch *)
  destruct (rnd_sub_delta x y Fx Fy) as [d1 [Hd1 E1]].
  set (e1 := rndF (x - y)) in *.
  destruct (rnd_split (e1 * e1)) as [d2 [z2 [Hd2 [Hz2 E2]]]].
  set (dh := rndF (e1 * e1)) in *.
  destruct (rnd_sub_delta 1 sh fmtF_one Fs) as [da [Hda Ea]].
  set (f1 := rndF (1 - sh)) in *.
  assert (Hf1n : / 4 / f1 <> 0 -> True) by auto.
  assert (Hf1 : bpow radix2 (-1022) <= Rabs (/ 4 / f1)).
  { rewrite Ea. apply Rabs_le_between in Hda. destruct Hda as [Hda1 Hda2].
    assert (Hpos : 0 < (1 - sh) * (1 + da)) by (apply Rmult_lt_0_compat; lra).
    assert (0 < / 4 / ((1 - sh) * (1 + da))) by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hpos]).
    rewrite Rabs_pos_eq by lra.
    assert (/ 8 <= / 4 / ((1 - sh) * (1 + da))).
    { apply Rmult_le_reg_r with ((1 - sh) * (1 + da)); [exact Hpos |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; exact Hpos). nra. }
    assert (bpow radix2 (-1022) <= / 8) by (replace (/ 8) with (bpow radix2 (-3)) by reflexivity; apply bpow_le; lia).
    lra. }
  destruct (rnd_delta (/ 4 / f1) (or_intror Hf1)) as [db [Hdb EP]].
  set (P := rndF (/ 4 / f1)) in *.
  destruct (rnd_split (dh * P)) as [d3 [z3 [Hd3 [Hz3 Et]]]].
  set (t1 := rndF (dh * P)) in *.
  destruct (branch (x - y) (1 - sh) e1 dh f1 P t1 d1 d2 z2 da db d3 z3 E1 E2 Ea EP Et Hc1a Hc1b Hd1 Hd2 Hda Hdb Hd3 Hz2 Hz3) as [zt1 [Et1 Hzt1]].
  (* the sum branch *)
  destruct (rnd_add_delta x y Fx Fy) as [d1' [Hd1' E1']].
  set (e2 := rndF (x + y)) in *.
  destruct (rnd_split (e2 * e2)) as [d2' [z2' [Hd2' [Hz2' E2']]]].
  set (mh := rndF (e2 * e2)) in *.
  destruct (rnd_add_delta 1 sh fmtF_one Fs) as [da' [Hda' Ea']].
  set (f2 := rndF (1 + sh)) in *.
  assert (Hf2 : bpow radix2 (-1022) <= Rabs (/ 4 / f2)).
  { rewrite Ea'. apply Rabs_le_between in Hda'. destruct Hda' as [Hda1 Hda2].
    assert (Hpos : 0 < (1 + sh) * (1 + da')) by (apply Rmult_lt_0_compat; lra).
    assert (0 < / 4 / ((1 + sh) * (1 + da'))) by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hpos]).
    rewrite Rabs_pos_eq by lra.
    assert (/ 8 <= / 4 / ((1 + sh) * (1 + da'))).
    { apply Rmult_le_reg_r with ((1 + sh) * (1 + da')); [exact Hpos |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; exact Hpos). nra. }
    assert (bpow radix2 (-1022) <= / 8) by (replace (/ 8) with (bpow radix2 (-3)) by reflexivity; apply bpow_le; lia).
    lra. }
  destruct (rnd_delta (/ 4 / f2) (or_intror Hf2)) as [db' [Hdb' EQ]].
  set (Q := rndF (/ 4 / f2)) in *.
  destruct (rnd_split (mh * Q)) as [d3' [z3' [Hd3' [Hz3' Et']]]].
  set (t2 := rndF (mh * Q)) in *.
  destruct (branch (x + y) (1 + sh) e2 mh f2 Q t2 d1' d2' z2' da' db' d3' z3' E1' E2' Ea' EQ Et' Hc2a Hc2b Hd1' Hd2' Hda' Hdb' Hd3' Hz2' Hz3') as [zt2 [Et2 Hzt2]].
  (* the sum *)
  destruct (rnd_split (t1 + t2)) as [ds [zs [Hds [Hzs Es]]]].
  change (argnc x y sh) with (rndF (t1 + t2)).
  rewrite Es.
  rewrite (Qf_split x y sh ltac:(lra) ltac:(lra)).
  set (D := (x - y) * (x - y)). set (M := (x + y) * (x + y)).
  set (P0 := / 4 / (1 - sh)). set (Q0 := / 4 / (1 + sh)).
  assert (HD : 0 <= D) by (unfold D; apply Rle_0_sqr). assert (HM : 0 <= M) by (unfold M; apply Rle_0_sqr).
  assert (HP0 : 0 <= P0) by (unfold P0; apply Rlt_le; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  assert (HQ0 : 0 <= Q0) by (unfold Q0; apply Rlt_le; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  set (g1 := (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) / (1 + da)) in *.
  set (g2 := (1 + d1') * (1 + d1') * (1 + d2') * (1 + db') * (1 + d3') / (1 + da')) in *.
  assert (Hg1 : Rabs (g1 * (1 + ds) - 1) <= 71 / 10 * u).
  { assert (E : g1 * (1 + ds) = (1 + d1) * (1 + d1) * (1 + d2) * (1 + db) * (1 + d3) * (1 + ds) / (1 + da)) by (unfold g1; field; apply Rabs_le_between in Hda; apply Rgt_not_eq; lra).
    rewrite E. apply factor_range; assumption. }
  assert (Hg2 : Rabs (g2 * (1 + ds) - 1) <= 71 / 10 * u).
  { assert (E : g2 * (1 + ds) = (1 + d1') * (1 + d1') * (1 + d2') * (1 + db') * (1 + d3') * (1 + ds) / (1 + da')) by (unfold g2; field; apply Rabs_le_between in Hda'; apply Rgt_not_eq; lra).
    rewrite E. apply factor_range; assumption. }
  assert (Eq : (t1 + t2) * (1 + ds) + zs - (D * P0 + M * Q0)
               = D * P0 * (g1 * (1 + ds) - 1) + M * Q0 * (g2 * (1 + ds) - 1) + (1 + ds) * (zt1 + zt2) + zs).
  { rewrite Et1, Et2. unfold D, M, P0, Q0 in *. ring. }
  rewrite Eq.
  eapply Rle_trans; [apply Rabs_triang |]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat_r; apply Rplus_le_compat_r; apply Rabs_triang |].
  rewrite (Rabs_mult (D * P0)), (Rabs_mult (M * Q0)), (Rabs_mult (1 + ds)).
  rewrite (Rabs_pos_eq (D * P0)) by (apply Rmult_le_pos; assumption).
  rewrite (Rabs_pos_eq (M * Q0)) by (apply Rmult_le_pos; assumption).
  assert (Hb1 : D * P0 * Rabs (g1 * (1 + ds) - 1) <= D * P0 * (71 / 10 * u)) by (apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption | exact Hg1]).
  assert (Hb2 : M * Q0 * Rabs (g2 * (1 + ds) - 1) <= M * Q0 * (71 / 10 * u)) by (apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption | exact Hg2]).
  assert (Hb3 : Rabs (1 + ds) * Rabs (zt1 + zt2) <= (1 + u) * (200 * z)).
  { assert (Rabs (1 + ds) <= 1 + u) by (apply Rabs_le_between in Hds; apply Rabs_le; lra).
    assert (Rabs (zt1 + zt2) <= 200 * z) by (eapply Rle_trans; [apply Rabs_triang | lra]).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | assumption | assumption]. }
  assert (Hb4 : (1 + u) * (200 * z) <= 201 * z) by nra.
  assert (Hqs : D * P0 * (71 / 10 * u) + M * Q0 * (71 / 10 * u) = 71 / 10 * u * (D * P0 + M * Q0)) by ring.
  lra.
Qed.
