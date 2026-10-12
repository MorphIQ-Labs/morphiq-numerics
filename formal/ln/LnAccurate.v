(** ln/mod.rs's accurate paths ([Reduced::accurate_value], [series],
    [Reduced::z_prime], [split] and the accurate branches of [ln] and
    [ln_1p], docs/ln.md, sections 6 and 7), transcribed on the proved Q128
    transcription (formal/q) and proved:
    - [ln_acc_ok]: [ln]'s 128-bit value is within [2^-123] relatively of
      [ln x], and [Q128::to_f64] rounds it once;
    - [ln_accurate_ok]: so when [ln x] keeps [LM]'s mantissa distance
      [2^-118] from every rounding breakpoint, [ln] returns [RN(ln x)];
    - [ln_1p_acc_ok]: [ln_1p]'s 128-bit value, on both branches, is within
      [2^-123] relatively of [ln(1 + x)];
    - [rounds_as]: a real that close to a value far from every breakpoint
      rounds as that value does, for either sign.
    The series' levels and the three sums are the certificates' theorems
    (LnAccurateLevels.v); this file proves their hypotheses about the
    transcription. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Binary64Mul Encodings.
From Interval Require Import Tactic.
Require LnTables LnTableCheck LnAccurateLevels LnReduction ExpAccurate.
Import ListNotations LnTables ExpAccurate.

Open Scope R_scope.

(** * The constants *)

Definition q_recip (k : nat) : Q128.q128 :=
  let '(m, e) := nth (k - 1) ln_recips (0%Z, 0%Z) in Q128.new false m e.

Definition q_ln2 : Q128.q128 := Q128.new false ln_ln2_q (-128).

Definition q_neg_ln_r (i : nat) : Q128.q128 :=
  let '(n, m, e) := nth i ln_neg_ln_r_q (false, 0%Z, 0%Z) in Q128.new n m e.

Lemma new_top n m e : (2 ^ 127 <= m < 2 ^ 128)%Z ->
  NZ (Q128.new n m e) /\ Q128.qval (Q128.new n m e) = F2R (Float radix2 (if n then - m else m) e).
Proof.
  intros H. assert (W : (0 <= m < Q128.W)%Z) by (unfold Q128.W; lia).
  split; [apply new_nz, W | rewrite Q128.new_val by exact W; reflexivity].
Qed.

Lemma q_recip_ok k : (1 <= k <= 18)%nat ->
  NZ (q_recip k) /\ 0 < Q128.qval (q_recip k) /\ Rabs (Q128.qval (q_recip k) * INR k - 1) <= / 2 ^ 127.
Proof.
  intros Hk. pose proof (LnTableCheck.recip_q_ok k Hk) as R. unfold q_recip.
  destruct (nth (k - 1) ln_recips (0%Z, 0%Z)) as [m e]. destruct R as [M [_ B1]].
  destruct (new_top false m e M) as [N V]. rewrite V. unfold F2R. cbn [Fnum Fexp].
  split; [exact N | split; [apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0] | exact B1]].
Qed.

(** [1/1] is exactly [1]. *)
Lemma q_recip_1 : Q128.qval (q_recip 1) = 1.
Proof.
  unfold q_recip. change (nth (1 - 1) ln_recips (0%Z, 0%Z)) with (170141183460469231731687303715884105728%Z, (-127)%Z).
  cbv beta iota. rewrite Q128.new_val by (unfold Q128.W; lia). unfold QSpec.val, F2R. cbn [Fnum Fexp].
  change (IZR 170141183460469231731687303715884105728) with (bpow radix2 127). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma q_ln2_ok : NZ q_ln2 /\ exists eL, Rabs eL <= / 2 ^ 127 /\ Q128.qval q_ln2 = ln 2 * (1 + eL).
Proof.
  destruct LnTableCheck.ln2_q_ok as [M B1]. unfold q_ln2.
  destruct (new_top false ln_ln2_q (-128) M) as [N V]. split; [exact N | ].
  assert (P2 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  exists (Q128.qval (Q128.new false ln_ln2_q (-128)) / ln 2 - 1). split.
  - rewrite V. unfold F2R. cbn [Fnum Fexp].
    replace (IZR ln_ln2_q * bpow radix2 (-128) / ln 2 - 1) with ((IZR ln_ln2_q * bpow radix2 (-128) - ln 2) / ln 2)
      by (field; lra).
    unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ ln 2)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
    apply Rmult_le_reg_r with (ln 2); [lra | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact B1.
  - field. lra.
Qed.

Lemma q_neg_ln_r_ok i : (i < 128)%nat -> B (LnTables.ln_r i) <> 1 ->
  NZ (q_neg_ln_r i) /\ exists eN, Rabs eN <= / 2 ^ 127 /\
    Q128.qval (q_neg_ln_r i) = - ln (B (LnTables.ln_r i)) * (1 + eN).
Proof.
  intros Hi R1. pose proof (LnTableCheck.neg_ln_r_q_ok i Hi) as Q. unfold q_neg_ln_r.
  destruct (nth i ln_neg_ln_r_q (false, 0%Z, 0%Z)) as [[n m] e].
  destruct Q as [[E _] | [_ [M B1]]]; [contradiction | ].
  destruct (new_top n m e M) as [N V]. split; [exact N | ].
  set (t := ln (B (LnTables.ln_r i))) in *.
  assert (T0 : t <> 0).
  { unfold t. intros Z. apply R1. destruct (ln_r_table_ok i Hi) as [_ [_ [[Ra _] _]]].
    rewrite <- (exp_ln (B (LnTables.ln_r i))) by lra. rewrite Z, exp_0. reflexivity. }
  exists (Q128.qval (Q128.new n m e) / - t - 1). split.
  - rewrite V. replace (F2R (Float radix2 (if n then - m else m) e) / - t - 1)
      with ((F2R (Float radix2 (if n then - m else m) e) - - t) / - t) by (field; exact T0).
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv, Rabs_Ropp by (apply Ropp_neq_0_compat; exact T0).
    apply Rmult_le_reg_r with (Rabs t); [apply Rabs_pos_lt, T0 | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, T0). exact B1.
  - field. exact T0.
Qed.

(** * The series

    [series(z)]: [G_18 = 1/18], then [G_k = 1/k + (−(z·G_(k+1)))] for
    [k = 17, …, 1]. After [c] levels, [gq z c] is [G_(18−c)], against the
    exact [xs z c = X_(18−c)] at the same [z]. *)

Fixpoint gq (z : Q128.q128) (c : nat) : Q128.q128 :=
  match c with
  | O => q_recip 18
  | S c' => Q128.add (q_recip (17 - c')) (Q128.neg_q (Q128.mul z (gq z c')))
  end.

Fixpoint xs (z : R) (c : nat) : R :=
  match c with
  | O => / 18
  | S c' => / INR (17 - c') - z * xs z c'
  end.

Lemma neg_nz x : NZ x -> NZ (Q128.neg_q x).
Proof. unfold Q128.neg_q. destruct (Q128.m x =? 0)%Z; [auto | intros H; exact H]. Qed.

(** Every partial series [X_k] is within [1.01·Z/(k + 1)] of [1/k]. *)
Lemma xs_range z c : Rabs z <= 0.0078126 -> (c <= 17)%nat ->
  Rabs (xs z c - / INR (18 - c)) <= 0.0078127 * 1.01 / INR (19 - c).
Proof.
  intros Hz. induction c as [| c IH]; intros Hc.
  - cbn [xs]. replace (INR (18 - 0)) with 18 by (simpl; ring).
    rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
    replace (INR (19 - 0)) with 19 by (simpl; ring). lra.
  - specialize (IH ltac:(lia)). cbn [xs].
    set (K := INR (18 - c)) in *.
    assert (K2 : 2 <= K) by (unfold K; replace 2 with (INR 2) by reflexivity; apply le_INR; lia).
    assert (E1 : INR (17 - c) = K - 1) by (unfold K; replace (18 - c)%nat with (S (17 - c)) by lia; rewrite S_INR; ring).
    assert (E2 : INR (18 - S c) = K - 1) by (rewrite <- E1; f_equal; lia).
    assert (E3 : INR (19 - S c) = K) by (unfold K; f_equal; lia).
    assert (E4 : INR (19 - c) = K + 1) by (unfold K; replace (19 - c)%nat with (S (18 - c)) by lia; rewrite S_INR; ring).
    rewrite E1, E2, E3. rewrite E4 in IH.
    replace (/ (K - 1) - z * xs z c - / (K - 1)) with (- (z * xs z c)) by ring.
    rewrite Rabs_Ropp, Rabs_mult.
    apply Rabs_le_inv in IH.
    assert (A : Rabs (xs z c) <= / K + 0.0078127 * 1.01 / (K + 1)).
    { apply Rabs_le. split; [ | lra].
      assert (0 < 0.0078127 * 1.01 / (K + 1) <= / K)
        by (split; [apply Rdiv_lt_0_compat; lra | unfold Rdiv; apply Rmult_le_reg_l with (K * (K + 1)); [nra | ];
            field_simplify; [nra | lra | lra]]).
      lra. }
    apply Rle_trans with (0.0078126 * (/ K + 0.0078127 * 1.01 / (K + 1))).
    + apply Rmult_le_compat; try apply Rabs_pos; assumption.
    + unfold Rdiv. apply Rmult_le_reg_l with (K * (K + 1)); [nra | ].
      field_simplify; [nra | lra | lra].
Qed.

(** One Horner level: from [|G_(k+1) − X_(k+1)| <= Eprev] to
    [|G_k − X_k| <= Ecur], given level [k]'s certificate ([d = k]). *)
Lemma step z c d Eprev Ecur xlo xhi :
  NZ z -> Rabs (Q128.qval z) <= 0.0078126 -> (c < 17)%nat ->
  (forall kk zz Xn En m s, Rabs zz <= 0.0078126 -> xlo <= Xn <= xhi -> Rabs En <= Eprev ->
     Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
     Rabs (1 / d * (1 + kk) - zz * (Xn + En) * (1 + m) + s - (1 / d - zz * Xn)) <= Ecur) ->
  INR (17 - c) = d -> xlo <= xs (Q128.qval z) c <= xhi -> 0 <= xlo -> xhi <= 1 ->
  NZ (gq z c) -> Rabs (Q128.qval (gq z c) - xs (Q128.qval z) c) <= Eprev -> Eprev <= / 1000 ->
  NZ (gq z (S c)) /\ Rabs (Q128.qval (gq z (S c)) - xs (Q128.qval z) (S c)) <= Ecur.
Proof.
  intros Nz Hz Hc Cert Hd Xr X0 X1 NG HE Ep.
  set (k := (17 - c)%nat) in *.
  assert (Hk : (1 <= k <= 18)%nat) by (unfold k; lia).
  assert (D1 : 1 <= d) by (rewrite <- Hd; replace 1 with (INR 1) by reflexivity; apply le_INR; lia).
  destruct (q_recip_ok k Hk) as [Nk [Pk Vk]]. rewrite Hd in Vk.
  destruct (mul_any z (gq z c) Nz NG) as [N1 [m [Hm E1]]].
  pose proof (neg_nz _ N1) as N2.
  destruct (add_any (q_recip k) _ Nk N2) as [N3 E3].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hm. rewrite bpow_m in Hm.
  change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in E3. rewrite bpow_m in E3.
  cbn [gq xs]. fold k. split; [exact N3 | ].
  set (zv := Q128.qval z) in *. set (X := xs zv c) in *. set (G := Q128.qval (gq z c)) in *.
  set (r := Q128.qval (q_recip k)) in *.
  set (kk := r * d - 1).
  assert (Er : r = 1 / d * (1 + kk)) by (unfold kk; field; lra).
  assert (U : 0 < / 2 ^ 127 < / 1000000) by (split; interval with (i_prec 64)).
  (* both addends are at most 1 *)
  assert (Rr : Rabs r <= 1).
  { destruct (Nat.eq_dec k 1) as [K1 | K1].
    - unfold r. rewrite K1, q_recip_1, Rabs_R1. lra.
    - assert (D2 : 2 <= d) by (rewrite <- Hd; replace 2 with (INR 2) by reflexivity; apply le_INR; lia).
      apply Rabs_le_inv in Vk. rewrite Rabs_pos_eq by lra.
      apply Rmult_le_reg_r with d; [lra | ]. nra. }
  assert (Rg : Rabs G <= 1.001) by (apply Rabs_le_inv in HE; apply Rabs_le; lra).
  set (b := Q128.qval (Q128.mul z (gq z c))) in *.
  assert (Eb : b = zv * G * (1 + m)) by exact E1.
  assert (Rb : Rabs b <= 1).
  { rewrite Eb. apply Rle_trans with (0.0078126 * 1.001 * 1); [ | lra].
    apply Rabs_mult_le; [apply Rabs_mult_le; assumption | apply Rabs_le; lra]. }
  set (s := Q128.qval (Q128.add (q_recip k) (Q128.neg_q (Q128.mul z (gq z c)))) - (r + - b)).
  assert (Hs : Rabs s <= / 2 ^ 126).
  { unfold s. rewrite Q128.neg_ok in E3. fold b in E3. apply Rle_trans with (1 := E3).
    rewrite Rabs_Ropp. assert (Rmax (Rabs r) (Rabs b) <= 1) by (apply Rmax_lub; assumption).
    assert (0 < / 2 ^ 126) by interval with (i_prec 64). nra. }
  assert (HK : Rabs kk <= / 2 ^ 127) by exact Vk.
  pose proof (Cert kk zv X (G - X) m s Hz Xr HE HK Hm Hs) as Br.
  replace (Q128.qval (Q128.add (q_recip k) (Q128.neg_q (Q128.mul z (gq z c)))) - (/ INR k - zv * X))
    with (1 / d * (1 + kk) - zv * (X + (G - X)) * (1 + m) + s - (1 / d - zv * X)).
  - exact Br.
  - unfold s. rewrite Eb, <- Er, Hd. field. lra.
Qed.

Lemma recip_18 : NZ (q_recip 18) /\ Rabs (Q128.qval (q_recip 18) - / 18) <= 920 * / 2 ^ 141.
Proof.
  destruct (q_recip_ok 18 ltac:(lia)) as [N [_ V]]. split; [exact N | ].
  replace (INR 18) with 18 in V by (rewrite INR_IZR_INZ; reflexivity).
  replace (Q128.qval (q_recip 18) - / 18) with ((Q128.qval (q_recip 18) * 18 - 1) / 18) by field.
  unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 18)) by lra.
  apply Rle_trans with (/ 2 ^ 127 * / 18); [apply Rmult_le_compat_r; lra | interval with (i_prec 64)].
Qed.

(** The seventeen levels: [G_1 = gq z 17] is within [782·2^-135] of the
    exact partial series [X_1] at the same [z]. *)
Theorem series_ok z : NZ z -> Rabs (Q128.qval z) <= 0.0078126 ->
  NZ (gq z 17) /\ Rabs (Q128.qval (gq z 17) - xs (Q128.qval z) 17) <= 782 * / 2 ^ 135.
Proof.
  intros Nz Hz.
  assert (S0 : NZ (gq z 0) /\ Rabs (Q128.qval (gq z 0) - xs (Q128.qval z) 0) <= 920 * / 2 ^ 141)
    by exact recip_18.
  Ltac lvl Nz Hz c L Sin Sout :=
    let N := fresh "N" in let E := fresh "E" in let XR := fresh "XR" in destruct Sin as [N E];
    pose proof (xs_range _ c Hz ltac:(lia)) as XR;
    rewrite !INR_IZR_INZ in XR; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.sub] in XR;
    apply Rabs_le_inv in XR;
    pose proof (step _ c _ _ _ _ _ Nz Hz ltac:(lia) L ltac:(rewrite INR_IZR_INZ; reflexivity)
                     ltac:(split; lra) ltac:(lra) ltac:(lra) N E ltac:(interval with (i_prec 64))) as Sout.
  lvl Nz Hz 0%nat LnAccurateLevels.level_17 S0 S1.
  lvl Nz Hz 1%nat LnAccurateLevels.level_16 S1 S2.
  lvl Nz Hz 2%nat LnAccurateLevels.level_15 S2 S3.
  lvl Nz Hz 3%nat LnAccurateLevels.level_14 S3 S4.
  lvl Nz Hz 4%nat LnAccurateLevels.level_13 S4 S5.
  lvl Nz Hz 5%nat LnAccurateLevels.level_12 S5 S6.
  lvl Nz Hz 6%nat LnAccurateLevels.level_11 S6 S7.
  lvl Nz Hz 7%nat LnAccurateLevels.level_10 S7 S8.
  lvl Nz Hz 8%nat LnAccurateLevels.level_09 S8 S9.
  lvl Nz Hz 9%nat LnAccurateLevels.level_08 S9 S10.
  lvl Nz Hz 10%nat LnAccurateLevels.level_07 S10 S11.
  lvl Nz Hz 11%nat LnAccurateLevels.level_06 S11 S12.
  lvl Nz Hz 12%nat LnAccurateLevels.level_05 S12 S13.
  lvl Nz Hz 13%nat LnAccurateLevels.level_04 S13 S14.
  lvl Nz Hz 14%nat LnAccurateLevels.level_03 S14 S15.
  lvl Nz Hz 15%nat LnAccurateLevels.level_02 S15 S16.
  lvl Nz Hz 16%nat LnAccurateLevels.level_01 S16 S17.
  exact S17.
Qed.

(** * The truncation

    [z·X_1] is [ln(1 + z)]'s series to degree 18, [alt 18 z]. With
    [g = ln(1 + t) − alt n t], [g' = (−t)^n / (1 + t)], so between 0 and [z]
    [|g'| <= |t|^n / (1 − Z)], and [|g(z)| <= |z|^(n+1) / ((n + 1)(1 − Z))]
    (mean value theorem on [|z|^(n+1)/((n+1)(1 − Z)) ∓ g]). *)

Fixpoint alt (n : nat) (t : R) : R :=
  match n with
  | O => 0
  | S k => alt k t + (-1) ^ k / INR (S k) * t ^ S k
  end.

Fixpoint dalt (n : nat) (t : R) : R :=
  match n with
  | O => 0
  | S k => dalt k t + (- t) ^ k
  end.

Lemma alt_deriv n t : derivable_pt_lim (alt n) t (dalt n t).
Proof.
  induction n as [|k IH].
  - change (alt 0) with (fct_cte 0). apply derivable_pt_lim_const.
  - change (alt (S k)) with (plus_fct (alt k) (mult_real_fct ((-1) ^ k / INR (S k)) (fun t => t ^ S k))).
    eapply LnCheck.lim_eq.
    + apply derivable_pt_lim_plus; [exact IH | apply derivable_pt_lim_scal, derivable_pt_lim_pow].
    + cbn [dalt Init.Nat.pred]. assert (0 < INR (S k)) by (apply lt_0_INR; lia).
      replace (- t) with (-1 * t) by ring. rewrite Rpow_mult_distr. field. lra.
Qed.

Lemma dalt_closed n t : (1 + t) * dalt n t = 1 - (- t) ^ n.
Proof. induction n as [|k IH]; [simpl; ring | cbn [dalt]; rewrite Rmult_plus_distr_l, IH; simpl; ring]. Qed.

Lemma alt_0 n : alt n 0 = 0.
Proof.
  induction n as [|k IH]; [reflexivity | ].
  cbn [alt]. rewrite IH, pow_ne_zero by lia. field. apply not_0_INR. lia.
Qed.

Lemma alt_rem n Z0 z : 0 <= Z0 < 1 -> Rabs z <= Z0 ->
  Rabs (ln (1 + z) - alt n z) <= Rabs z ^ (n + 1) / (INR (n + 1) * (1 - Z0)).
Proof.
  intros [Z1 Z2] Hz.
  set (C := / (INR (n + 1) * (1 - Z0))).
  assert (Pn : 0 < INR (n + 1)) by (apply lt_0_INR; lia).
  assert (PC : 0 < C) by (unfold C; apply Rinv_0_lt_compat; nra).
  set (g := fun t => ln (1 + t) - alt n t).
  assert (Dg : forall t, Rabs t < 1 -> derivable_pt_lim g t ((- t) ^ n / (1 + t))).
  { intros t Ht. apply Rabs_lt_inv in Ht.
    change g with (minus_fct (fun t => ln (1 + t)) (alt n)).
    eapply LnCheck.lim_eq.
    - apply derivable_pt_lim_minus; [ | apply alt_deriv].
      apply (derivable_pt_lim_comp (fun t => 1 + t) ln t 1 (/ (1 + t))).
      + eapply LnCheck.lim_eq; [apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id] | ring].
      + apply derivable_pt_lim_ln. lra.
    - apply Rmult_eq_reg_l with (1 + t); [ | lra].
      replace ((1 + t) * (/ (1 + t) * 1 - dalt n t)) with (1 - (1 + t) * dalt n t) by (field; lra).
      rewrite dalt_closed. field. lra. }
  assert (G0 : g 0 = 0) by (unfold g; rewrite Rplus_0_r, ln_1, alt_0; ring).
  change (ln (1 + z) - alt n z) with (g z).
  replace (Rabs z ^ (n + 1) / (INR (n + 1) * (1 - Z0))) with (C * Rabs z ^ (n + 1)) by (unfold C, Rdiv; ring).
  (* |g'(t)| <= C·(n + 1)·|t|^n between 0 and z *)
  assert (Bd : forall t, Rabs t <= Z0 -> Rabs ((- t) ^ n / (1 + t)) <= C * INR (n + 1) * Rabs t ^ n).
  { intros t Ht. apply Rabs_le_inv in Ht as Ht'.
    unfold Rdiv. rewrite Rabs_mult, <- RPow_abs, Rabs_Ropp, Rabs_Rinv, (Rabs_pos_eq (1 + t)) by lra.
    replace (C * INR (n + 1)) with (/ (1 - Z0)) by (unfold C; field; lra).
    rewrite Rmult_comm. apply Rmult_le_compat_r; [apply pow_le, Rabs_pos | ].
    apply Rinv_le_contravar; lra. }
  destruct (Rtotal_order z 0) as [Neg | [Zr | Pos]].
  - (* z < 0: on [z, 0], w = C·(−t)^(n+1) ∓ g decreases *)
    assert (Rabs z = - z) by (apply Rabs_left; exact Neg).
    set (u := fun t => C * (- t) ^ (n + 1)).
    assert (Du : forall t, derivable_pt_lim u t (- C * INR (n + 1) * (- t) ^ n)).
    { intros t. unfold u. change (fun t => C * (- t) ^ (n + 1)) with (mult_real_fct C (comp (fun y => y ^ (n + 1)) (fun t => - t))).
      eapply LnCheck.lim_eq.
      - apply derivable_pt_lim_scal. apply derivable_pt_lim_comp; [apply derivable_pt_lim_opp, derivable_pt_lim_id | apply derivable_pt_lim_pow].
      - replace (Init.Nat.pred (n + 1)) with n by lia. ring. }
    assert (Mono : forall sg, sg = 1 \/ sg = -1 -> u z + sg * g z >= u 0 + sg * g 0).
    { intros sg Hsg.
      destruct (MVT_cor2 (fun t => u t + sg * g t) (fun t => - C * INR (n + 1) * (- t) ^ n + sg * ((- t) ^ n / (1 + t))) z 0 Neg)
        as [c [Ec [C1 C2]]].
      { intros c Hc. apply derivable_pt_lim_plus; [apply Du | ].
        change (fun t => sg * g t) with (mult_real_fct sg g). apply derivable_pt_lim_scal.
        apply Dg. apply Rabs_def1; lra. }
      assert (Bc : Rabs ((- c) ^ n / (1 + c)) <= C * INR (n + 1) * Rabs c ^ n)
        by (apply Bd; rewrite Rabs_left by lra; lra).
      assert (Ac : Rabs c ^ n = (- c) ^ n) by (rewrite Rabs_left by lra; reflexivity).
      rewrite Ac in Bc. apply Rabs_le_inv in Bc.
      assert (Dn : - C * INR (n + 1) * (- c) ^ n + sg * ((- c) ^ n / (1 + c)) <= 0) by (destruct Hsg; subst sg; nra).
      cbv beta in Ec. nra. }
    pose proof (Mono 1 (or_introl eq_refl)) as M1. pose proof (Mono (-1) (or_intror eq_refl)) as M2.
    unfold u in M1, M2. rewrite Ropp_0, pow_ne_zero in M1, M2 by lia. rewrite G0 in M1, M2.
    assert (Ez : (- z) ^ (n + 1) = Rabs z ^ (n + 1)) by (rewrite Rabs_left by lra; reflexivity).
    rewrite Ez in M1, M2. apply Rabs_le. lra.
  - subst z. rewrite G0, Rabs_R0, pow_ne_zero by lia. lra.
  - assert (Rabs z = z) by (apply Rabs_pos_eq; lra).
    set (u := fun t => C * t ^ (n + 1)).
    assert (Du : forall t, derivable_pt_lim u t (C * INR (n + 1) * t ^ n)).
    { intros t. unfold u. change (fun t => C * t ^ (n + 1)) with (mult_real_fct C (fun y => y ^ (n + 1))).
      eapply LnCheck.lim_eq; [apply derivable_pt_lim_scal, derivable_pt_lim_pow | ].
      replace (Init.Nat.pred (n + 1)) with n by lia. ring. }
    assert (Mono : forall sg, sg = 1 \/ sg = -1 -> u z - sg * g z >= u 0 - sg * g 0).
    { intros sg Hsg.
      destruct (MVT_cor2 (fun t => u t - sg * g t) (fun t => C * INR (n + 1) * t ^ n - sg * ((- t) ^ n / (1 + t))) 0 z Pos)
        as [c [Ec [C1 C2]]].
      { intros c Hc. apply derivable_pt_lim_minus; [apply Du | ].
        change (fun t => sg * g t) with (mult_real_fct sg g). apply derivable_pt_lim_scal.
        apply Dg. apply Rabs_def1; lra. }
      assert (Bc : Rabs ((- c) ^ n / (1 + c)) <= C * INR (n + 1) * Rabs c ^ n)
        by (apply Bd; rewrite Rabs_pos_eq by lra; lra).
      rewrite (Rabs_pos_eq c) in Bc by lra. apply Rabs_le_inv in Bc.
      assert (Dn : 0 <= C * INR (n + 1) * c ^ n - sg * ((- c) ^ n / (1 + c))) by (destruct Hsg; subst sg; nra).
      cbv beta in Ec. nra. }
    pose proof (Mono 1 (or_introl eq_refl)) as M1. pose proof (Mono (-1) (or_intror eq_refl)) as M2.
    unfold u in M1, M2. rewrite pow_ne_zero in M1, M2 by lia. rewrite G0 in M1, M2.
    rewrite (Rabs_pos_eq z) by lra. apply Rabs_le. lra.
Qed.

(** [z·X_1] is [alt 18 z]. *)
Lemma xs_alt z : z * xs z 17 = alt 18 z.
Proof. cbn [xs alt INR Nat.sub]. field. Qed.

(** The truncation: [|X_1 − ln(1 + z)/z| <= 28·2^-135]. *)
Lemma trunc_ok z : z <> 0 -> Rabs z <= 0.0078126 -> Rabs (xs z 17 - ln (1 + z) / z) <= 28 * / 2 ^ 135.
Proof.
  intros Nz Hz.
  pose proof (alt_rem 18 0.0078126 z ltac:(lra) Hz) as R.
  rewrite <- xs_alt in R.
  replace (xs z 17 - ln (1 + z) / z) with (- (ln (1 + z) - z * xs z 17) / z) by (field; exact Nz).
  unfold Rdiv at 1. rewrite Rabs_mult, Rabs_Ropp, Rabs_Rinv by exact Nz.
  apply Rmult_le_reg_r with (Rabs z); [apply Rabs_pos_lt, Nz | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, Nz).
  apply Rle_trans with (1 := R).
  replace (INR (18 + 1)) with 19 by (rewrite INR_IZR_INZ; reflexivity).
  rewrite pow_add, pow_1.
  replace (Rabs z ^ 18 * Rabs z / (19 * (1 - 0.0078126))) with (Rabs z ^ 18 * / (19 * (1 - 0.0078126)) * Rabs z)
    by (unfold Rdiv; ring).
  apply Rmult_le_compat_r; [apply Rabs_pos | ].
  assert (Rabs z ^ 18 <= 0.0078126 ^ 18) by (apply pow_incr; split; [apply Rabs_pos | exact Hz]).
  assert (0.0078126 ^ 18 * / (19 * (1 - 0.0078126)) <= 28 * / 2 ^ 135) by interval with (i_prec 100).
  assert (0 <= / (19 * (1 - 0.0078126))) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  nra.
Qed.

(** * [ln(1 + z)] in Q128

    [z.mul(series(z))]: [z·G_1 = ln(1 + z)·(1 + E1/X1)·(1 + mz)] with
    [X1 = ln(1 + z)/z] (or [1] at [z = 0]) and [E1 = G_1 − X1], the
    certificates' variables. *)

Definition lnz (z : Q128.q128) : Q128.q128 := Q128.mul z (gq z 17).

Lemma x1_range z : z <> 0 -> Rabs z <= 0.0078126 -> 0.996 <= ln (1 + z) / z <= 1.004.
Proof.
  intros Nz Hz. pose proof (alt_rem 1 0.0078126 z ltac:(lra) Hz) as R.
  assert (A : alt 1 z = z) by (simpl; field). rewrite A in R.
  replace (INR (1 + 1)) with 2 in R by (simpl; ring).
  assert (D : Rabs (ln (1 + z) / z - 1) <= Rabs z / (2 * (1 - 0.0078126))).
  { replace (ln (1 + z) / z - 1) with ((ln (1 + z) - z) / z) by (field; exact Nz).
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Nz.
    apply Rmult_le_reg_r with (Rabs z); [apply Rabs_pos_lt, Nz | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, Nz).
    apply Rle_trans with (1 := R). rewrite pow_add, pow_1. unfold Rdiv. nra. }
  assert (Rabs z / (2 * (1 - 0.0078126)) <= 0.004) by (unfold Rdiv; apply Rmult_le_reg_r with (2 * (1 - 0.0078126)); [lra | ];
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra; lra).
  apply Rabs_le_inv in D. lra.
Qed.

Theorem lnz_ok z : NZ z -> Rabs (Q128.qval z) <= 0.0078126 ->
  NZ (lnz z) /\ exists X1 E1 mz, 0.995118 <= X1 <= 1.004931 /\ Rabs E1 <= 818 * / 2 ^ 135 /\
    - / 2 ^ 127 <= mz <= 0 /\ Q128.qval (lnz z) = ln (1 + Q128.qval z) * (1 + E1 / X1) * (1 + mz).
Proof.
  intros Nz Hz. destruct (series_ok z Nz Hz) as [NG EG].
  destruct (mul_any z (gq z 17) Nz NG) as [NL [mz [Hm EL]]].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hm. rewrite bpow_m in Hm.
  split; [exact NL | ]. unfold lnz. rewrite EL.
  set (zv := Q128.qval z) in *.
  destruct (Req_dec zv 0) as [Z0 | Z0].
  { exists 1, 0, mz. rewrite Z0, Rplus_0_r, ln_1, Rabs_R0.
    split; [lra | split; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; apply pow_lt; lra] | ]].
    split; [exact Hm | ring]. }
  pose proof (x1_range zv Z0 Hz) as XR. pose proof (trunc_ok zv Z0 Hz) as TR.
  set (X1 := ln (1 + zv) / zv) in *.
  exists X1, (Q128.qval (gq z 17) - X1), mz. split; [lra | ]. split.
  - replace (Q128.qval (gq z 17) - X1) with ((Q128.qval (gq z 17) - xs zv 17) + (xs zv 17 - X1)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    assert (782 * / 2 ^ 135 + 28 * / 2 ^ 135 <= 818 * / 2 ^ 135) by interval with (i_prec 64). lra.
  - split; [exact Hm | ]. unfold X1. field. split; [exact Z0 | ].
    intros L0. assert (X1 = 0) by (unfold X1; rewrite L0; unfold Rdiv; ring). lra.
Qed.

(** * [Reduced::accurate_value]

    [(E·ln 2 + (−ln R[i])) + z·G_1], a zero term skipped: [E·ln 2] where
    [E = 0], [−ln R[i]] where [R[i] = 1]. [E] converts to binary64 exactly,
    then to Q128. *)

Definition fe (e : Z) : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE e 0 false.

Lemma fe_ok e : (Z.abs e <= 2 ^ 52)%Z -> finite (fe e) /\ B (fe e) = IZR e.
Proof.
  intros He. pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE e 0 false) as C.
  assert (Fm : fmtF (IZR e)).
  { apply generic_format_FLT. exists (Float radix2 e 0); [unfold F2R; simpl; ring | simpl; lia | simpl; unfold emin; lia]. }
  replace (F2R (Float radix2 e 0)) with (IZR e) in C by (unfold F2R; simpl; ring).
  rewrite round_generic in C by (auto with typeclass_instances || exact Fm).
  rewrite Rlt_bool_true in C.
  - destruct C as [V [F _]]. split; [exact F | exact V].
  - apply Rle_lt_trans with (bpow radix2 52); [ | apply bpow_lt; lia].
    rewrite <- abs_IZR. change (bpow radix2 52) with (IZR (2 ^ 52)). apply IZR_le. exact He.
Qed.

Definition acc_value (e : Z) (i : nat) (r : f64) (z : Q128.q128) : Q128.q128 :=
  let l := lnz z in
  let e_ln2 := if (e =? 0)%Z then None else Some (Q128.mul (qf (fe e)) q_ln2) in
  let neg_ln_r := match Bcompare 53 1024 r LnReduction.c_one with Some Eq => None | _ => Some (q_neg_ln_r i) end in
  match e_ln2, neg_ln_r with
  | Some a, Some b => Q128.add (Q128.add a b) l
  | Some t, None | None, Some t => Q128.add t l
  | None, None => l
  end.

Lemma s_rel s A C lx g : lx <> 0 -> Rabs s <= bpow radix2 (-126) * Rmax (Rabs A) (Rabs C) ->
  Rabs A <= g * Rabs lx -> Rabs C <= g * Rabs lx -> Rabs (s / lx) <= / 2 ^ 126 * g.
Proof.
  intros N Hs HA HC. change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in Hs. rewrite bpow_m in Hs.
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact N. apply Rmult_le_reg_r with (Rabs lx); [apply Rabs_pos_lt, N | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, N).
  apply Rle_trans with (1 := Hs). rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | ].
  apply Rmax_lub; assumption.
Qed.

Lemma ln_r_finite i : (i < 128)%nat -> finite (ln_r i) /\ / 2 <= B (ln_r i) <= 2.
Proof. intros Hi. destruct (ln_r_table_ok i Hi) as [F [_ [R _]]]. split; [exact F | exact R]. Qed.

Lemma cmp_one r : finite r ->
  (Bcompare 53 1024 r LnReduction.c_one = Some Eq <-> B r = 1).
Proof.
  intros Fr. destruct LnReduction.c_one_ok as [F1 B1].
  rewrite Bcompare_correct by assumption. rewrite B1.
  split; [intros H; injection H as H; apply Rcompare_Eq_inv, H | intros H; rewrite H, Rcompare_Eq; reflexivity].
Qed.

(** * The sums over reals

    The three ways [accurate_value] assembles its result, each reduced to
    its certificate: [v] is the computed value, [lx] the exact one, [lnR]
    and [lnYR] stand for [ln R[i]] and [ln(y·R[i])], [dl] for
    [ln(1 + z_computed) − ln(y·R[i])], and each [s] for an addition's error. *)

Lemma abs_prod3 a b c A C D : Rabs a <= A -> Rabs b <= C -> Rabs c <= D -> Rabs (a * b * c) <= A * C * D.
Proof. intros. apply Rabs_mult_le; [apply Rabs_mult_le | ]; assumption. Qed.

Lemma div_le t b lx : lx <> 0 -> Rabs t <= b * Rabs lx -> Rabs (t / lx) <= b.
Proof.
  intros Nl Ht. assert (Pl : 0 < Rabs lx) by (apply Rabs_pos_lt, Nl).
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Nl.
  apply Rmult_le_reg_r with (Rabs lx); [exact Pl | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact Ht.
Qed.

Lemma one_plus u e : 0 <= u -> Rabs e <= u -> Rabs (1 + e) <= 1 + u.
Proof. intros H0 H. apply Rabs_le_inv in H. apply Rabs_le. lra. Qed.

Lemma one_minus m : - / 2 ^ 127 <= m <= 0 -> Rabs (1 + m) <= 1.
Proof. intros H. assert (/ 2 ^ 127 < 1) by interval with (i_prec 64). apply Rabs_le. lra. Qed.

(** Case B: [v = N + L + s], [lx = −lnR + lnYR]. *)
Lemma core_b lx lnR lnYR dl L N v eN q mz X1 E1 s :
  lx <> 0 -> lx = - lnR + lnYR -> N = - lnR * (1 + eN) -> L = (lnYR + dl) * ((1 + q) * (1 + mz)) ->
  q = E1 / X1 -> v = N + L + s ->
  Rabs lnYR <= 533 / 1024 * Rabs lx -> Rabs eN <= / 2 ^ 127 ->
  Rabs dl * (1 + / 2 ^ 100) <= 524 * / 2 ^ 135 * Rabs lx -> Rabs ((1 + q) * (1 + mz)) <= 1 + / 2 ^ 100 ->
  0.995118 <= X1 <= 1.004931 -> Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 ->
  Rabs s <= bpow radix2 (-126) * Rmax (Rabs N) (Rabs L) ->
  Rabs (v - lx) <= / 2 ^ 123 * Rabs lx.
Proof.
  intros Nl Elx EN EL Eq Ev H3 HeN Hdl Hrho HX HE Hmz Hs.
  assert (Pl : 0 < Rabs lx) by (apply Rabs_pos_lt, Nl).
  assert (U : 0 < / 2 ^ 127 <= / 10 ^ 38) by (split; interval with (i_prec 64)).
  assert (U1 : 0 < / 2 ^ 100 <= / 10 ^ 30) by (split; interval with (i_prec 64)).
  assert (U2 : 0 < 524 * / 2 ^ 135 <= / 10 ^ 37) by (split; interval with (i_prec 64)).
  assert (Dl : Rabs dl <= 524 * / 2 ^ 135 * Rabs lx).
  { apply Rle_trans with (2 := Hdl). pose proof (Rabs_pos dl). nra. }
  assert (HR : Rabs lnR <= (1 + 533 / 1024) * Rabs lx).
  { replace lnR with (lnYR - lx) by lra. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (HN : Rabs N <= 1.5206 * Rabs lx).
  { rewrite EN, Rabs_mult, Rabs_Ropp. pose proof (one_plus _ _ (Rlt_le _ _ (proj1 U)) HeN).
    apply Rle_trans with ((1 + 533 / 1024) * Rabs lx * (1 + / 2 ^ 127)); [apply Rmult_le_compat; try apply Rabs_pos; assumption | nra]. }
  assert (HL : Rabs L <= 1.5206 * Rabs lx).
  { rewrite EL, Rabs_mult.
    apply Rle_trans with ((533 / 1024 * Rabs lx + 524 * / 2 ^ 135 * Rabs lx) * (1 + / 2 ^ 100)).
    - apply Rmult_le_compat; try apply Rabs_pos; [ | exact Hrho].
      apply Rle_trans with (1 := Rabs_triang _ _). lra.
    - nra. }
  pose proof (s_rel s N L lx 1.5206 Nl Hs HN HL) as S2.
  assert (S2b : Rabs (s / lx) <= 784 * / 2 ^ 135).
  { apply Rle_trans with (1 := S2). interval with (i_prec 64). }
  assert (K3 : Rabs (lnYR / lx) <= 533 * / 2 ^ 10).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Nl.
    apply Rmult_le_reg_r with (Rabs lx); [exact Pl | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    replace (533 * / 2 ^ 10) with (533 / 1024) by (simpl; field). exact H3. }
  assert (DZ : Rabs (dl * ((1 + q) * (1 + mz)) / lx) <= 524 * / 2 ^ 135).
  { apply div_le; [exact Nl | ]. rewrite Rabs_mult. apply Rle_trans with (2 := Hdl).
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hrho]. }
  pose proof (LnAccurateLevels.sum_b X1 (lnYR / lx) eN E1 mz _ _ HX K3 HeN HE Hmz DZ S2b) as C.
  replace (v - lx) with (lx * ((1 - lnYR / lx) * (1 + eN) + lnYR / lx * (1 + E1 / X1) * (1 + mz)
                              + dl * ((1 + q) * (1 + mz)) / lx + s / lx - 1)).
  - rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact C].
  - rewrite Ev, EN, EL, Eq. replace lnR with (lnYR - lx) by lra. field. split; [lra | exact Nl].
Qed.

(** Case C with [R[i] = 1]: [v = a + L + s], [lx = E2 + lnYR]. *)
Lemma core_c1 lx E2 lnYR dl L a v eL mL q mz X1 E1 s :
  lx <> 0 -> lx = E2 + lnYR -> a = E2 * (1 + eL) * (1 + mL) -> L = (lnYR + dl) * ((1 + q) * (1 + mz)) ->
  q = E1 / X1 -> v = a + L + s ->
  Rabs lnYR <= 752 / 65536 * Rabs lx -> Rabs eL <= / 2 ^ 127 -> - / 2 ^ 127 <= mL <= 0 ->
  Rabs dl * (1 + / 2 ^ 100) <= 524 * / 2 ^ 135 * Rabs lx -> Rabs ((1 + q) * (1 + mz)) <= 1 + / 2 ^ 100 ->
  0.995118 <= X1 <= 1.004931 -> Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 ->
  Rabs s <= bpow radix2 (-126) * Rmax (Rabs a) (Rabs L) ->
  Rabs (v - lx) <= / 2 ^ 123 * Rabs lx.
Proof.
  intros Nl Elx Ea EL Eq Ev H3 HeL HmL Hdl Hrho HX HE Hmz Hs.
  assert (Pl : 0 < Rabs lx) by (apply Rabs_pos_lt, Nl).
  assert (U : 0 < / 2 ^ 127 <= / 10 ^ 38) by (split; interval with (i_prec 64)).
  assert (U1 : 0 < / 2 ^ 100 <= / 10 ^ 30) by (split; interval with (i_prec 64)).
  assert (U2 : 0 < 524 * / 2 ^ 135 <= / 10 ^ 37) by (split; interval with (i_prec 64)).
  assert (HE2 : Rabs E2 <= (1 + 752 / 65536) * Rabs lx).
  { replace E2 with (lx - lnYR) by lra. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (Ha : Rabs a <= 1.0115 * Rabs lx).
  { rewrite Ea. pose proof (one_plus _ _ (Rlt_le _ _ (proj1 U)) HeL). pose proof (one_minus _ HmL).
    apply Rle_trans with ((1 + 752 / 65536) * Rabs lx * (1 + / 2 ^ 127) * 1); [apply abs_prod3; assumption | nra]. }
  assert (HL : Rabs L <= 1.0115 * Rabs lx).
  { rewrite EL, Rabs_mult.
    apply Rle_trans with ((752 / 65536 * Rabs lx + 524 * / 2 ^ 135 * Rabs lx) * (1 + / 2 ^ 100)).
    - apply Rmult_le_compat; try apply Rabs_pos; [ | exact Hrho].
      apply Rle_trans with (1 := Rabs_triang _ _). assert (Rabs dl <= 524 * / 2 ^ 135 * Rabs lx) by (pose proof (Rabs_pos dl); nra). lra.
    - nra. }
  pose proof (s_rel s a L lx 1.0115 Nl Hs Ha HL) as S2.
  assert (S2b : Rabs (s / lx) <= 523 * / 2 ^ 135) by (apply Rle_trans with (1 := S2); interval with (i_prec 64)).
  assert (K3 : Rabs (lnYR / lx) <= 752 * / 2 ^ 16).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Nl.
    apply Rmult_le_reg_r with (Rabs lx); [exact Pl | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    replace (752 * / 2 ^ 16) with (752 / 65536) by (simpl; field). exact H3. }
  assert (DZ : Rabs (dl * ((1 + q) * (1 + mz)) / lx) <= 524 * / 2 ^ 135).
  { apply div_le; [exact Nl | ]. rewrite Rabs_mult. apply Rle_trans with (2 := Hdl).
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hrho]. }
  assert (K2 : Rabs 0 <= 514 * / 2 ^ 9) by (rewrite Rabs_R0; interval with (i_prec 64)).
  assert (E0 : Rabs 0 <= / 2 ^ 127) by (rewrite Rabs_R0; lra).
  assert (S1 : Rabs 0 <= 518 * / 2 ^ 134) by (rewrite Rabs_R0; interval with (i_prec 64)).
  pose proof (LnAccurateLevels.sum_c X1 0 (lnYR / lx) eL mL 0 0 E1 mz _ _ HX K2 K3 HeL HmL E0 S1 HE Hmz DZ S2b) as C.
  replace (v - lx) with (lx * ((1 - 0 - lnYR / lx) * (1 + eL) * (1 + mL) + 0 * (1 + 0) + 0
                              + lnYR / lx * (1 + E1 / X1) * (1 + mz)
                              + dl * ((1 + q) * (1 + mz)) / lx + s / lx - 1)).
  - rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact C].
  - rewrite Ev, Ea, EL, Eq. replace E2 with (lx - lnYR) by lra. field. split; [lra | exact Nl].
Qed.

(** Case C with [R[i] ≠ 1]: [v = S1 + L + s], [S1 = a + N + s1],
    [lx = E2 − lnR + lnYR]. *)
Lemma core_c2 lx E2 lnR lnYR dl L a N S1 v eL mL eN q mz X1 E1 s1 s :
  lx <> 0 -> lx = E2 - lnR + lnYR -> a = E2 * (1 + eL) * (1 + mL) -> N = - lnR * (1 + eN) ->
  L = (lnYR + dl) * ((1 + q) * (1 + mz)) -> q = E1 / X1 -> S1 = a + N + s1 -> v = S1 + L + s ->
  Rabs E2 <= 2071 / 1024 * Rabs lx -> Rabs lnR <= 514 / 512 * Rabs lx -> Rabs lnYR <= 752 / 65536 * Rabs lx ->
  Rabs eL <= / 2 ^ 127 -> - / 2 ^ 127 <= mL <= 0 -> Rabs eN <= / 2 ^ 127 ->
  Rabs dl * (1 + / 2 ^ 100) <= 524 * / 2 ^ 135 * Rabs lx -> Rabs ((1 + q) * (1 + mz)) <= 1 + / 2 ^ 100 ->
  0.995118 <= X1 <= 1.004931 -> Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 ->
  Rabs s1 <= bpow radix2 (-126) * Rmax (Rabs a) (Rabs N) ->
  Rabs s <= bpow radix2 (-126) * Rmax (Rabs S1) (Rabs L) ->
  Rabs (v - lx) <= / 2 ^ 123 * Rabs lx.
Proof.
  intros Nl Elx Ea EN EL Eq ES1 Ev H1 H2 H3 HeL HmL HeN Hdl Hrho HX HE Hmz Hs1 Hs.
  assert (Pl : 0 < Rabs lx) by (apply Rabs_pos_lt, Nl).
  assert (U : 0 < / 2 ^ 127 <= / 10 ^ 38) by (split; interval with (i_prec 64)).
  assert (U1 : 0 < / 2 ^ 100 <= / 10 ^ 30) by (split; interval with (i_prec 64)).
  assert (U2 : 0 < 524 * / 2 ^ 135 <= / 10 ^ 37) by (split; interval with (i_prec 64)).
  pose proof (one_plus _ _ (Rlt_le _ _ (proj1 U)) HeL) as AeL.
  pose proof (one_minus _ HmL) as AmL.
  pose proof (one_plus _ _ (Rlt_le _ _ (proj1 U)) HeN) as AeN.
  assert (Ha : Rabs a <= 2.0225 * Rabs lx).
  { rewrite Ea. apply Rle_trans with (2071 / 1024 * Rabs lx * (1 + / 2 ^ 127) * 1); [apply abs_prod3; assumption | nra]. }
  assert (HN : Rabs N <= 2.0225 * Rabs lx).
  { rewrite EN, Rabs_mult, Rabs_Ropp.
    apply Rle_trans with (514 / 512 * Rabs lx * (1 + / 2 ^ 127)); [apply Rmult_le_compat; try apply Rabs_pos; assumption | nra]. }
  pose proof (s_rel s1 a N lx 2.0225 Nl Hs1 Ha HN) as S1r.
  assert (S1b : Rabs (s1 / lx) <= 518 * / 2 ^ 134) by (apply Rle_trans with (1 := S1r); interval with (i_prec 64)).
  assert (S1a : Rabs s1 <= / 10 ^ 37 * Rabs lx).
  { assert (Rabs (s1 / lx) <= / 10 ^ 37) by (apply Rle_trans with (1 := S1b); interval with (i_prec 64)).
    replace s1 with (s1 / lx * lx) by (field; exact Nl). rewrite Rabs_mult. nra. }
  (* |S1| <= 1.0115 |lx| *)
  assert (HS1 : Rabs S1 <= 1.0115 * Rabs lx).
  { assert (ES : S1 = (lx - lnYR) + E2 * ((1 + eL) * (1 + mL) - 1) + (- lnR) * eN + s1)
      by (rewrite ES1, Ea, EN; replace lx with (E2 - lnR + lnYR) by lra; ring).
    rewrite ES.
    assert (Q1 : Rabs (lx - lnYR) <= (1 + 752 / 65536) * Rabs lx)
      by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra).
    assert (Q2 : Rabs ((1 + eL) * (1 + mL) - 1) <= 3 * / 2 ^ 127).
    { apply Rabs_le_inv in HeL. apply Rabs_le. split; nra. }
    assert (Q3 : Rabs (E2 * ((1 + eL) * (1 + mL) - 1)) <= 2071 / 1024 * Rabs lx * (3 * / 2 ^ 127))
      by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
    assert (Q4 : Rabs (- lnR * eN) <= 514 / 512 * Rabs lx * / 2 ^ 127)
      by (rewrite Rabs_mult, Rabs_Ropp; apply Rmult_le_compat; try apply Rabs_pos; assumption).
    pose proof (Rabs_triang (lx - lnYR + E2 * ((1 + eL) * (1 + mL) - 1) + - lnR * eN) s1) as T1.
    pose proof (Rabs_triang (lx - lnYR + E2 * ((1 + eL) * (1 + mL) - 1)) (- lnR * eN)) as T2.
    pose proof (Rabs_triang (lx - lnYR) (E2 * ((1 + eL) * (1 + mL) - 1))) as T3.
    nra. }
  assert (HL : Rabs L <= 1.0115 * Rabs lx).
  { rewrite EL, Rabs_mult.
    apply Rle_trans with ((752 / 65536 * Rabs lx + 524 * / 2 ^ 135 * Rabs lx) * (1 + / 2 ^ 100)).
    - apply Rmult_le_compat; try apply Rabs_pos; [ | exact Hrho].
      apply Rle_trans with (1 := Rabs_triang _ _). assert (Rabs dl <= 524 * / 2 ^ 135 * Rabs lx) by (pose proof (Rabs_pos dl); nra). lra.
    - nra. }
  pose proof (s_rel s S1 L lx 1.0115 Nl Hs HS1 HL) as S2.
  assert (S2b : Rabs (s / lx) <= 523 * / 2 ^ 135) by (apply Rle_trans with (1 := S2); interval with (i_prec 64)).
  assert (Kq : forall t b, Rabs t <= b * Rabs lx -> Rabs (t / lx) <= b).
  { intros t b Ht. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Nl.
    apply Rmult_le_reg_r with (Rabs lx); [exact Pl | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact Ht. }
  assert (K2 : Rabs (- lnR / lx) <= 514 * / 2 ^ 9).
  { replace (514 * / 2 ^ 9) with (514 / 512) by (simpl; field). apply Kq. rewrite Rabs_Ropp. exact H2. }
  assert (K3 : Rabs (lnYR / lx) <= 752 * / 2 ^ 16).
  { replace (752 * / 2 ^ 16) with (752 / 65536) by (simpl; field). apply Kq. exact H3. }
  assert (DZ : Rabs (dl * ((1 + q) * (1 + mz)) / lx) <= 524 * / 2 ^ 135).
  { apply Kq. rewrite Rabs_mult. apply Rle_trans with (2 := Hdl).
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hrho]. }
  pose proof (LnAccurateLevels.sum_c X1 (- lnR / lx) (lnYR / lx) eL mL eN (s1 / lx) E1 mz _ _
                HX K2 K3 HeL HmL HeN S1b HE Hmz DZ S2b) as C.
  replace (v - lx) with (lx * ((1 - - lnR / lx - lnYR / lx) * (1 + eL) * (1 + mL) + - lnR / lx * (1 + eN) + s1 / lx
                              + lnYR / lx * (1 + E1 / X1) * (1 + mz)
                              + dl * ((1 + q) * (1 + mz)) / lx + s / lx - 1)).
  - rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact C].
  - rewrite Ev, ES1, Ea, EN, EL, Eq. replace E2 with (lx + lnR - lnYR) by lra. field. split; [lra | exact Nl].
Qed.

(** [Reduced::accurate_value] at a [z] for [y·R[i] − 1], with [y] in interval
    [i] widened by [2^-52], is within [2^-123] relatively of
    [E·ln 2 + ln y]: [ln x] for [ln], and [ln(1 + x)] for [ln_1p]. The
    computed [z] may differ from the exact one by at most what [dz] allows
    (nothing for [ln]); with no table or [E] term it must be exact. *)
Theorem acc_value_ok e i (Y : R) zq :
  (i < 128)%nat -> (Z.abs e <= 1074)%Z -> ln_lo i - / 2 ^ 52 <= Y <= ln_hi i + / 2 ^ 52 ->
  NZ zq -> Rabs (Q128.qval zq) <= 0.0078126 ->
  (e = 0%Z -> B (ln_r i) = 1 -> Q128.qval zq = Y * B (ln_r i) - 1) ->
  Rabs (ln (1 + Q128.qval zq) - ln (Y * B (ln_r i))) * (1 + / 2 ^ 100)
    <= 524 * / 2 ^ 135 * Rabs (IZR e * ln 2 + ln Y) ->
  IZR e * ln 2 + ln Y <> 0 ->
  QSpec.normalized 128 (Q128.m (acc_value e i (ln_r i) zq)) /\
  Rabs (Q128.qval (acc_value e i (ln_r i) zq) - (IZR e * ln 2 + ln Y)) <= / 2 ^ 123 * Rabs (IZR e * ln 2 + ln Y).
Proof.
  intros Hi He HY Nz Hz Hex Hdz Hlx.
  set (lx := IZR e * ln 2 + ln Y) in *.
  destruct (ln_r_finite i Hi) as [Fr [R1 R2]].
  destruct (LnTableCheck.ratios_ok i Y Hi HY) as [PY [PR [RB RC]]].
  set (R := B (ln_r i)) in *.
  set (zc := Q128.qval zq) in *.
  assert (EYR : ln (Y * R) = ln Y + ln R) by (apply ln_mult; lra).
  set (lnYR := ln (Y * R)) in *.
  set (dl := ln (1 + zc) - lnYR) in *.
  destruct (lnz_ok zq Nz Hz) as [NL [X1 [E1 [mz [HX1 [HE1 [Hmz EL]]]]]]].
  fold zc in EL. set (L := Q128.qval (lnz zq)) in *.
  set (q := E1 / X1) in *.
  assert (Hq : Rabs q <= / 2 ^ 120).
  { unfold q, Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq X1) by lra.
    apply Rmult_le_reg_r with X1; [lra | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    assert (818 * / 2 ^ 135 <= / 2 ^ 120 * 0.995118) by interval with (i_prec 64). nra. }
  set (rho := (1 + q) * (1 + mz)).
  assert (Hrho : Rabs rho <= 1 + / 2 ^ 100).
  { unfold rho. apply Rabs_le_inv in Hq.
    assert (/ 2 ^ 120 < / 2 ^ 100 / 2) by interval with (i_prec 64).
    assert (0 < / 2 ^ 127 < / 2 ^ 120) by (split; interval with (i_prec 64)).
    apply Rabs_le. split; nra. }
  assert (EL' : L = (lnYR + dl) * rho) by (rewrite EL; unfold rho, dl; ring).
  assert (Plx : 0 < Rabs lx) by (apply Rabs_pos_lt, Hlx).
  set (dz := dl * rho / lx).
  assert (Hdz' : Rabs dz <= 524 * / 2 ^ 135).
  { unfold dz, Rdiv. rewrite !Rabs_mult, Rabs_Rinv by exact Hlx.
    apply Rmult_le_reg_r with (Rabs lx); [exact Plx | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    apply Rle_trans with (2 := Hdz). apply Rmult_le_compat_l; [apply Rabs_pos | exact Hrho]. }
  assert (U : 0 < / 2 ^ 127 <= / 10 ^ 38) by (split; interval with (i_prec 64)).
  assert (U6 : / 2 ^ 126 = 2 * / 2 ^ 127)
    by (replace (2 ^ 127) with (2 * 2 ^ 126) by (rewrite tech_pow_Rmult; reflexivity); field; apply pow_nonzero; lra).
  (* the result, by case *)
  unfold acc_value. fold (lnz zq).
  assert (Small : Rabs L <= (Rabs lnYR + 524 * / 2 ^ 135 * Rabs lx) * (1 + / 2 ^ 100)).
  { rewrite EL', Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [ | exact Hrho].
    apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat_l.
    assert (1 <= 1 + / 2 ^ 100) by (assert (0 < / 2 ^ 100) by interval with (i_prec 64); lra).
    assert (0 <= Rabs dl) by apply Rabs_pos. nra. }
  (* closing: from [qval = lx·T] and [|T − 1| <= 2^-123] *)
  assert (Close : forall v T, v = lx * T -> Rabs (T - 1) <= / 2 ^ 123 -> NZ (Q128.Q false 0 0) ->
            Rabs (v - lx) <= / 2 ^ 123 * Rabs lx).
  { intros v T Ev HT _. rewrite Ev. replace (lx * T - lx) with (lx * (T - 1)) by ring.
    rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact HT]. }
  assert (Norm : forall a, NZ a -> Rabs (Q128.qval a - lx) <= / 2 ^ 123 * Rabs lx -> QSpec.normalized 128 (Q128.m a)).
  { intros a [Za | Na] Ha; [ | exact Na]. exfalso. rewrite (qval_zero a Za), Rminus_0_l, Rabs_Ropp in Ha.
    assert (/ 2 ^ 123 < 1) by interval with (i_prec 64). nra. }
  assert (Mone : B (ln_r i) = 1 ->
            match Bcompare 53 1024 (ln_r i) LnReduction.c_one with Some Eq => @None Q128.q128 | _ => Some (q_neg_ln_r i) end = None).
  { intros H. apply (proj2 (cmp_one _ Fr)) in H. rewrite H. reflexivity. }
  assert (Mne : B (ln_r i) <> 1 ->
            match Bcompare 53 1024 (ln_r i) LnReduction.c_one with Some Eq => None | _ => Some (q_neg_ln_r i) end
            = Some (q_neg_ln_r i)).
  { intros H. destruct (Bcompare 53 1024 (ln_r i) LnReduction.c_one) as [[ | | ] | ] eqn:Cr; try reflexivity.
    exfalso. apply H. apply (cmp_one _ Fr). exact Cr. }
  destruct (Z.eqb_spec e 0) as [E0 | E0].
  - (* E = 0: lx = ln y *)
    assert (Lx : lx = ln Y) by (unfold lx; rewrite E0; simpl; ring).
    destruct (Req_dec R 1) as [Cr | R1'].
    + (* case A *)
      rewrite (Mone Cr).
      pose proof (Hex E0 Cr) as Zx. fold zc in Zx.
      assert (Ld : L = lx * ((X1 + E1) * (1 + mz) / X1)).
      { rewrite EL, Zx, Cr, Lx, Rmult_1_r. unfold q. replace (1 + (Y - 1)) with Y by ring. field. lra. }
      assert (B1 := LnAccurateLevels.sum_a X1 E1 mz HX1 HE1 Hmz).
      assert (Bd : Rabs (L - lx) <= / 2 ^ 123 * Rabs lx) by exact (Close L _ Ld B1 (or_introl eq_refl)).
      split; [exact (Norm _ NL Bd) | exact Bd].
    + (* case B *)
      rewrite (Mne R1').
      destruct (q_neg_ln_r_ok i Hi R1') as [NN [eN [HeN EN]]]. fold R in EN.
      destruct (add_any _ _ NN NL) as [NA EA]. fold L in EA.
      assert (Bd : Rabs (Q128.qval (Q128.add (q_neg_ln_r i) (lnz zq)) - lx) <= / 2 ^ 123 * Rabs lx).
      { apply (core_b lx (ln R) lnYR dl L (Q128.qval (q_neg_ln_r i)) _ eN q mz X1 E1
                 (Q128.qval (Q128.add (q_neg_ln_r i) (lnz zq)) - (Q128.qval (q_neg_ln_r i) + L)));
          [exact Hlx | rewrite Lx, EYR; ring | exact EN | exact EL' | reflexivity | ring
          | | exact HeN | exact Hdz | exact Hrho | exact HX1 | exact HE1 | exact Hmz | exact EA].
        rewrite Lx. exact (RB R1'). }
      split; [exact (Norm _ NA Bd) | exact Bd].
  - (* E ≠ 0 *)
    destruct (fe_ok e ltac:(lia)) as [Fe Be].
    pose proof (from_f64_nz (bits_of_b64 (fe e))) as Ne. fold (qf (fe e)) in Ne.
    assert (Ve : Q128.qval (qf (fe e)) = IZR e) by (unfold qf; rewrite from_f64_b64 by exact Fe; exact Be).
    destruct q_ln2_ok as [N2 [eL [HeL E2]]].
    destruct (mul_any (qf (fe e)) q_ln2 Ne N2) as [NA [mL [HmL Ea]]].
    change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in HmL. rewrite bpow_m in HmL.
    rewrite Ve, E2 in Ea.
    set (a := Q128.mul (qf (fe e)) q_ln2) in *.
    assert (Ea' : Q128.qval a = IZR e * ln 2 * (1 + eL) * (1 + mL)) by (rewrite Ea; ring).
    destruct (RC e E0) as [C2 [C3 C1]]. fold lx in C2, C3, C1.
    unfold LnTableCheck.k1c, LnTableCheck.k2c, LnTableCheck.k3c in C1, C2, C3.
    destruct (Req_dec R 1) as [Cr | R1'].
    + (* R[i] = 1 *)
      rewrite (Mone Cr).
      change (QSpec.normalized 128 (Q128.m (Q128.add a (lnz zq))) /\
              Rabs (Q128.qval (Q128.add a (lnz zq)) - lx) <= / 2 ^ 123 * Rabs lx).
      destruct (add_any _ _ NA NL) as [NS ES]. fold L in ES.
      assert (Bd : Rabs (Q128.qval (Q128.add a (lnz zq)) - lx) <= / 2 ^ 123 * Rabs lx).
      { apply (core_c1 lx (IZR e * ln 2) lnYR dl L (Q128.qval a) _ eL mL q mz X1 E1
                 (Q128.qval (Q128.add a (lnz zq)) - (Q128.qval a + L)));
          [exact Hlx | | exact Ea' | exact EL' | reflexivity | ring | exact C3 | exact HeL | exact HmL
          | exact Hdz | exact Hrho | exact HX1 | exact HE1 | exact Hmz | exact ES].
        unfold lx. rewrite EYR, Cr, ln_1. ring. }
      split; [exact (Norm _ NS Bd) | exact Bd].
    + (* R[i] ≠ 1 *)
      rewrite (Mne R1').
      change (QSpec.normalized 128 (Q128.m (Q128.add (Q128.add a (q_neg_ln_r i)) (lnz zq))) /\
              Rabs (Q128.qval (Q128.add (Q128.add a (q_neg_ln_r i)) (lnz zq)) - lx) <= / 2 ^ 123 * Rabs lx).
      destruct (q_neg_ln_r_ok i Hi R1') as [NN [eN [HeN EN]]]. fold R in EN.
      destruct (add_any _ _ NA NN) as [NS1 ES1].
      destruct (add_any _ _ NS1 NL) as [NS ES]. fold L in ES.
      assert (Bd : Rabs (Q128.qval (Q128.add (Q128.add a (q_neg_ln_r i)) (lnz zq)) - lx) <= / 2 ^ 123 * Rabs lx).
      { apply (core_c2 lx (IZR e * ln 2) (ln R) lnYR dl L (Q128.qval a) (Q128.qval (q_neg_ln_r i))
                 (Q128.qval (Q128.add a (q_neg_ln_r i))) _ eL mL eN q mz X1 E1
                 (Q128.qval (Q128.add a (q_neg_ln_r i)) - (Q128.qval a + Q128.qval (q_neg_ln_r i)))
                 (Q128.qval (Q128.add (Q128.add a (q_neg_ln_r i)) (lnz zq))
                    - (Q128.qval (Q128.add a (q_neg_ln_r i)) + L)));
          [exact Hlx | | exact Ea' | exact EN | exact EL' | reflexivity | ring | ring
          | exact C1 | exact C2 | exact C3 | exact HeL | exact HmL | exact HeN
          | exact Hdz | exact Hrho | exact HX1 | exact HE1 | exact Hmz | exact ES1 | exact ES].
        unfold lx. rewrite EYR. ring. }
      split; [exact (Norm _ NS Bd) | exact Bd].
Qed.

(** * Rounding once *)

(** Any real within [d/2] relatively of a nonzero [v] whose magnitude keeps
    mantissa distance [d] from every rounding breakpoint rounds as [v] does,
    for either sign of [v]. *)
Theorem rounds_as v w d : v <> 0 -> 0 < d <= / 2 -> midpoint_far (Rabs v) d ->
  Rabs (w - v) < d / 2 * Rabs v -> rndF w = rndF v.
Proof.
  intros Nv Hd Far Close.
  assert (Pos : forall v w, 0 < v -> midpoint_far v d -> Rabs (w - v) < d / 2 * v -> rndF w = rndF v).
  { clear v w Nv Far Close. intros v w Pv Far Close.
    destruct (far_abs v d Pv ltac:(lra)) as [F1 F2].
    apply (same_rounding_abs v w (d * bpow radix2 (mag radix2 v - 1)) Pv); [nra | exact Far | ].
    lra. }
  destruct (Rlt_or_le 0 v) as [Pv | Nv'].
  - rewrite (Rabs_pos_eq v) in Far, Close by lra. exact (Pos v w Pv Far Close).
  - assert (Pv : 0 < - v) by (destruct (Rle_lt_or_eq_dec _ _ Nv'); [lra | contradiction]).
    rewrite (Rabs_left v) in Far, Close by lra.
    assert (Opp : forall t, rndF (- t) = - rndF t).
    { intros t. assert (Hne : ne = fun n => negb (Z.even n)) by reflexivity. rewrite Hne. apply round_NE_opp. }
    assert (E : rndF (- w) = rndF (- v)).
    { apply (Pos (- v) (- w) Pv Far). replace (- w - - v) with (- (w - v)) by ring. rewrite Rabs_Ropp. exact Close. }
    rewrite !Opp in E. lra.
Qed.

(** [Q128::to_f64] rounds a value below [2^10] in magnitude once. *)
Lemma to_f64_small q : QSpec.normalized 128 (Q128.m q) -> Rabs (Q128.qval q) <= bpow radix2 10 ->
  B (Q128.to_f64 q) = rndF (Q128.qval q).
Proof.
  intros Nq Hq. apply to_f64_val; [exact Nq | ].
  assert (F : fmtF (bpow radix2 10)) by (apply generic_format_bpow; unfold FLT_exp, emin, prec; lia).
  apply Rle_lt_trans with (bpow radix2 10); [ | apply bpow_lt; lia].
  apply abs_round_le_generic; [exact _ | exact _ | exact F | exact Hq].
Qed.

Lemma ln_pow2 e y : 0 < y -> ln (bpow radix2 e * y) = IZR e * ln 2 + ln y.
Proof.
  intros Py. rewrite ln_mult by (try apply bpow_gt_0; exact Py). rewrite bpow_exp, ln_exp. reflexivity.
Qed.

(** The value is below [2^10]: [|ln|] of anything binary64 is below [745]. *)
Lemma small_value v lx : Rabs (v - lx) <= / 2 ^ 123 * Rabs lx -> Rabs lx <= 800 -> Rabs v <= bpow radix2 10.
Proof.
  intros H L. change (bpow radix2 10) with 1024.
  assert (/ 2 ^ 123 < 1) by interval with (i_prec 64).
  pose proof (Rabs_triang_inv v lx). pose proof (Rabs_pos lx). nra.
Qed.

Lemma lx_small e y : (Z.abs e <= 1074)%Z -> / 2 <= y <= 2 -> Rabs (IZR e * ln 2 + ln y) <= 800.
Proof.
  intros He Hy. assert (Re : Rabs (IZR e) <= 1074) by (rewrite <- abs_IZR; apply IZR_le; lia).
  apply Rabs_le_inv in Re. apply Rabs_le. split; interval with (i_prec 64).
Qed.

(** * [ln]'s accurate path *)

Definition ln_acc (x : f64) : Q128.q128 :=
  let '(e, i, y, r) := LnReduction.reduce x in acc_value e i r (LnReduction.z_exact y r).

Theorem ln_acc_ok x : finite x -> 0 < B x -> B x <> 1 ->
  QSpec.normalized 128 (Q128.m (ln_acc x)) /\
  Rabs (Q128.qval (ln_acc x) - ln (B x)) <= / 2 ^ 123 * Rabs (ln (B x)) /\
  B (Q128.to_f64 (ln_acc x)) = rndF (Q128.qval (ln_acc x)).
Proof.
  intros Fx Px N1. pose proof (LnReduction.reduce_ok x Fx Px) as RO. unfold ln_acc.
  destruct (LnReduction.reduce x) as [[[e i] y] r].
  destruct RO as [Hi [Er [Fy [Iy [Gy [Ex He]]]]]]. subst r.
  destruct (LnReduction.z_exact_ok y i Hi Fy Iy) as [Nz Vz].
  destruct (LnReduction.ln_range i Hi) as [L1 [L2 _]].
  pose proof (LnReduction.z_range y i Hi Iy Gy) as [_ [Zb _]].
  assert (Lx : ln (B x) = IZR e * ln 2 + ln (B y)) by (rewrite Ex; apply ln_pow2; lra).
  assert (Nl : IZR e * ln 2 + ln (B y) <> 0).
  { rewrite <- Lx. intros Z0. apply N1. rewrite <- (exp_ln (B x)) by exact Px. rewrite Z0. apply exp_0. }
  destruct (acc_value_ok e i (B y) (LnReduction.z_exact y (ln_r i)) Hi ltac:(lia)
              ltac:(split; [assert (0 < / 2 ^ 52) by (apply Rinv_0_lt_compat, pow_lt; lra); lra
                           | assert (0 < / 2 ^ 52) by (apply Rinv_0_lt_compat, pow_lt; lra); lra])
              Nz ltac:(rewrite Vz; lra) ltac:(intros _ _; exact Vz)
              ltac:(rewrite Vz; replace (1 + (B y * B (ln_r i) - 1)) with (B y * B (ln_r i)) by ring;
                    rewrite Rminus_diag_eq, Rabs_R0, Rmult_0_l by reflexivity;
                    apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra] | apply Rabs_pos])
              Nl) as [Nn Bd].
  rewrite <- Lx in Bd. split; [exact Nn | split; [exact Bd | ]].
  apply to_f64_small; [exact Nn | ]. apply (small_value _ (ln (B x)) Bd). rewrite Lx.
  apply lx_small; [lia | lra].
Qed.

(** [ln]'s accurate path end to end: for every finite [x > 0], [x ≠ 1], if
    [ln x] keeps [LM]'s mantissa distance [2^-118] from every rounding
    breakpoint (Property 2, docs/ln.md, section 2), the value returned is
    [RN(ln x)]. *)
Theorem ln_accurate_ok x : finite x -> 0 < B x -> B x <> 1 ->
  midpoint_far (Rabs (ln (B x))) (/ 2 ^ 118) ->
  B (Q128.to_f64 (ln_acc x)) = rndF (ln (B x)).
Proof.
  intros Fx Px N1 Far. destruct (ln_acc_ok x Fx Px N1) as [_ [Bd Rd]]. rewrite Rd.
  assert (Nl : ln (B x) <> 0).
  { intros Z0. apply N1. rewrite <- (exp_ln (B x)) by exact Px. rewrite Z0. apply exp_0. }
  apply rounds_as with (/ 2 ^ 118); [exact Nl | split; interval with (i_prec 64) | exact Far | ].
  apply Rle_lt_trans with (1 := Bd).
  assert (/ 2 ^ 123 < / 2 ^ 118 / 2) by interval with (i_prec 64).
  pose proof (Rabs_pos_lt _ Nl). nra.
Qed.

(** * [ln_1p]'s accurate path *)

Definition c_two_m7 : f64 := b64_of_bits 4575657221408423936.       (* 0x3f80000000000000, 2^-7 *)
Definition c_neg_two_m7 : f64 := b64_of_bits 13799029258263199744.  (* 0xbf80000000000000, -2^-7 *)
Definition c_two_53 : f64 := b64_of_bits 4845873199050653696.       (* 0x4340000000000000, 2^53 *)

Lemma c_two_m7_ok : finite c_two_m7 /\ B c_two_m7 = bpow radix2 (-7).
Proof. exact (LnReduction.pow2_bits 1016 ltac:(lia)). Qed.
Lemma c_two_53_ok : finite c_two_53 /\ B c_two_53 = bpow radix2 53.
Proof. exact (LnReduction.pow2_bits 1076 ltac:(lia)). Qed.
Lemma c_neg_two_m7_ok : finite c_neg_two_m7 /\ B c_neg_two_m7 = - bpow radix2 (-7).
Proof.
  split; [exact (bits_finite 13799029258263199744 _ _ _ eq_refl) | ].
  unfold c_neg_two_m7. rewrite (bits_val 13799029258263199744 true 4503599627370496 59 eq_refl).
  cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-7)) with (/ 128).
  rewrite opp_IZR. replace (2 ^ 59) with (4503599627370496 * 128) by (simpl; ring). field.
Qed.

(** [|x| < 2^-7], as [ln_1p] tests [x.abs() < TWO_M7]. *)
Definition small7 (x : f64) : bool :=
  match Bcompare 53 1024 x c_two_m7, Bcompare 53 1024 c_neg_two_m7 x with
  | Some Lt, Some Lt => true
  | _, _ => false
  end.

(** [split(x)]: [two_sum(1, x)] below [2^53], [(x, 1)] from it. *)
Definition split (x : f64) : f64 * f64 :=
  match Bcompare 53 1024 x c_two_53 with
  | Some Lt => two_sum64 LnReduction.c_one x
  | _ => (x, LnReduction.c_one)
  end.

(** [Reduced::z_prime(l)]: [z_exact + R[i]·l·2^-E] in Q128. *)
Definition z_prime (e : Z) (y r l : f64) : Q128.q128 :=
  Q128.add (LnReduction.z_exact y r) (Q128.mul_pow2 (Q128.mul (qf r) (qf l)) (- e)).

Definition ln_1p_acc (x : f64) : Q128.q128 :=
  if small7 x then lnz (qf x)
  else let '(h, l) := split x in
       let '(e, i, y, r) := LnReduction.reduce h in acc_value e i r (z_prime e y r l).

Lemma small7_ok x : finite x -> (small7 x = true <-> Rabs (B x) < bpow radix2 (-7)).
Proof.
  intros Fx. destruct c_two_m7_ok as [F1 B1]. destruct c_neg_two_m7_ok as [F2 B2].
  unfold small7. rewrite (Bcompare_correct _ _ x c_two_m7 Fx F1), (Bcompare_correct _ _ c_neg_two_m7 x F2 Fx), B1, B2.
  split.
  - destruct (Rcompare_spec (B x) (bpow radix2 (-7))); try discriminate;
      destruct (Rcompare_spec (- bpow radix2 (-7)) (B x)); try discriminate. intros _. apply Rabs_def1; lra.
  - intros H. apply Rabs_def2 in H as [H1 H2]. rewrite Rcompare_Lt, Rcompare_Lt by lra. reflexivity.
Qed.

Lemma split_ok x : finite x -> -1 < B x ->
  let '(h, l) := split x in
  finite h /\ finite l /\ B h + B l = 1 + B x /\ 0 < B h /\ Rabs (B l) <= 1.0001 / 9007199254740992 * B h /\
  (B x < bpow radix2 53 -> B h = rndF (1 + B x)) /\ (bpow radix2 53 <= B x -> B h = B x).
Proof.
  intros Fx Hx. destruct c_two_53_ok as [F53 B53]. destruct LnReduction.c_one_ok as [F1 B1].
  assert (U : 0 < / 2 ^ 52) by (apply Rinv_0_lt_compat, pow_lt; lra).
  assert (B53' : bpow radix2 53 = 2 ^ 52 * 2)
    by (change 53%Z with (Z.of_nat 53); rewrite bpow_powerRZ, <- pow_powerRZ; simpl; ring).
  unfold split. rewrite (Bcompare_correct _ _ x c_two_53 Fx F53), B53.
  destruct (Rcompare_spec (B x) (bpow radix2 53)) as [Lt | Eq | Gt].
  - assert (Bx : Rabs (B x) <= bpow radix2 1020).
    { assert (2 <= bpow radix2 1020) by (apply Rle_trans with (bpow radix2 1); [simpl; lra | apply bpow_le; lia]).
      apply Rabs_le. split; [lra | ].
      apply Rlt_le, Rlt_le_trans with (1 := Lt). apply bpow_le. lia. }
    pose proof (two_sum_ieee LnReduction.c_one x F1 Fx ltac:(rewrite B1, Rabs_R1; apply Rle_trans with (bpow radix2 1); [simpl; lra | apply bpow_le; lia]) Bx) as TS.
    destruct (two_sum64 LnReduction.c_one x) as [h l]. destruct TS as [Fh [Fl [Bh Ehl]]]. rewrite B1 in Bh, Ehl.
    destruct (Rle_or_lt (B x) (- / 2)) as [Neg | Big].
    + (* 1 + x is exact, by Sterbenz's lemma *)
      assert (Fm : fmtF (1 + B x)).
      { replace (1 + B x) with (B LnReduction.c_one - - B x) by (rewrite B1; ring).
        apply sterbenz; try exact _; [apply B_fmt | apply generic_format_opp, B_fmt | rewrite B1; lra]. }
      rewrite round_generic in Bh by (exact _ || exact Fm).
      assert (L0 : B l = 0) by lra. rewrite L0, Rabs_R0.
      split; [exact Fh | ]. split; [exact Fl | ]. split; [lra | ]. split; [lra | ].
      split; [apply Rmult_le_pos; lra | ]. split.
      * intros _. rewrite Bh. symmetry. apply round_generic; [exact _ | exact Fm].
      * intros. lra.
    + assert (Hh : / 2 <= B h).
      { rewrite Bh. apply round_ge_generic; [exact _ | exact _ | | lra].
        change (/ 2) with (bpow radix2 (-1)). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
      assert (Rel : Rabs (B h - (1 + B x)) <= bpow radix2 (-53) * Rabs (1 + B x)).
      { rewrite Bh. apply RoundingCore.rnd_rel. rewrite Rabs_pos_eq by lra.
        apply Rle_trans with (/ 2); [change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia | lra]. }
      change (bpow radix2 (-53)) with (/ 9007199254740992) in Rel.
      replace (B h - (1 + B x)) with (- B l) in Rel by lra. rewrite Rabs_Ropp in Rel.
      rewrite (Rabs_pos_eq (1 + B x)) in Rel by lra.
      assert (E52 : / 2 ^ 52 = 2 / 9007199254740992) by (simpl; field).
      apply Rabs_le_inv in Rel as Rel'.
      split; [exact Fh | ]. split; [exact Fl | ]. split; [lra | ]. split; [lra | ]. split; [ | split].
      * apply Rabs_le_inv in Rel. apply Rabs_le. split; lra.
      * intros _. exact Bh.
      * intros. lra.
  - assert (P : 2 <= / 2 ^ 52 * B x).
    { rewrite Eq, B53'. replace (/ 2 ^ 52 * (2 ^ 52 * 2)) with 2 by (field; apply pow_nonzero; lra). lra. }
    assert (P' : 1.0001 <= 1.0001 / 9007199254740992 * B x).
    { rewrite Eq, B53'. replace (2 ^ 52 * 2) with 9007199254740992 by (simpl; ring). lra. }
    split; [exact Fx | ]. split; [exact F1 | ]. split; [rewrite B1; ring | ]. split; [rewrite Eq; apply bpow_gt_0 | ].
    split; [rewrite B1, Rabs_R1; lra | ]. split; [intros; lra | intros; reflexivity].
  - assert (P : 2 <= / 2 ^ 52 * B x).
    { apply Rle_trans with (/ 2 ^ 52 * bpow radix2 53); [rewrite B53'; replace (/ 2 ^ 52 * (2 ^ 52 * 2)) with 2 by (field; apply pow_nonzero; lra); lra | ].
      apply Rmult_le_compat_l; lra. }
    assert (0 < B x) by (apply Rlt_trans with (2 := Gt); apply bpow_gt_0).
    assert (P' : 1.0001 <= 1.0001 / 9007199254740992 * B x).
    { assert (9007199254740992 <= B x) by (rewrite B53' in Gt; replace (2 ^ 52 * 2) with 9007199254740992 in Gt by (simpl; ring); lra).
      lra. }
    split; [exact Fx | ]. split; [exact F1 | ]. split; [rewrite B1; ring | ]. split; [lra | ].
    split; [rewrite B1, Rabs_R1; lra | ]. split; [intros; lra | intros; reflexivity].
Qed.

Lemma nz_mul_pow2 x k : NZ x -> NZ (Q128.mul_pow2 x k).
Proof. unfold Q128.mul_pow2. destruct (Q128.m x =? 0)%Z; [auto | intros H; exact H]. Qed.

(** [|ln a − ln b| <= |a − b| / m] for [a, b >= m > 0]. *)
Lemma ln_lip a b m : 0 < m -> m <= a -> m <= b -> Rabs (ln a - ln b) <= Rabs (a - b) / m.
Proof.
  intros Pm Ha Hb.
  assert (Le : forall u v, 0 < u -> 0 < v -> ln u - ln v <= (u - v) / v).
  { intros u v Pu Pv. replace (ln u - ln v) with (ln (u / v)).
    - pose proof (exp_ineq1_le (ln (u / v))) as E. rewrite exp_ln in E by (apply Rdiv_lt_0_compat; lra).
      replace ((u - v) / v) with (u / v - 1) by (field; lra). lra.
    - unfold Rdiv. rewrite ln_mult, ln_Rinv by (try apply Rinv_0_lt_compat; lra). ring. }
  pose proof (Le a b ltac:(lra) ltac:(lra)) as A. pose proof (Le b a ltac:(lra) ltac:(lra)) as C.
  assert (Q : forall u v w, 0 < m <= v -> Rabs u <= w -> u / v <= w / m).
  { intros u v w [P1 P2] Hu. apply Rabs_le_inv in Hu.
    unfold Rdiv. destruct (Rle_or_lt 0 u).
    - apply Rle_trans with (u * / m); [apply Rmult_le_compat_l; [lra | apply Rinv_le_contravar; lra] | ].
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | lra].
    - apply Rle_trans with 0; [ | apply Rmult_le_pos; [pose proof (Rabs_pos u); lra | apply Rlt_le, Rinv_0_lt_compat; lra]].
      assert (0 < / v) by (apply Rinv_0_lt_compat; lra). nra. }
  apply Rabs_le. split.
  - assert ((b - a) / a <= Rabs (a - b) / m) by (apply Q; [lra | rewrite Rabs_minus_sym; apply Rle_refl]). lra.
  - apply Rle_trans with (1 := A). apply Q; [lra | apply Rle_refl].
Qed.

(** [h], from [|x| >= 2^-7], is at least [2^-7] away from 1. *)
Lemma h_far x h : finite x -> -1 < B x -> bpow radix2 (-7) <= Rabs (B x) ->
  (B x < bpow radix2 53 -> B h = rndF (1 + B x)) -> (bpow radix2 53 <= B x -> B h = B x) ->
  1 + / 128 <= B h \/ B h <= 1 - / 128.
Proof.
  intros Fx Hx Ax H1 H2. change (bpow radix2 (-7)) with (/ 128) in Ax.
  assert (F1 : fmtF (1 + / 128)) by (apply generic_format_FLT; exists (Float radix2 129 (-7));
    [unfold F2R; cbn [Fnum Fexp]; change (bpow radix2 (-7)) with (/ 128); field | simpl; lia | simpl; unfold emin; lia]).
  assert (F2 : fmtF (1 - / 128)) by (apply generic_format_FLT; exists (Float radix2 127 (-7));
    [unfold F2R; cbn [Fnum Fexp]; change (bpow radix2 (-7)) with (/ 128); field | simpl; lia | simpl; unfold emin; lia]).
  destruct (Rlt_or_le (B x) (bpow radix2 53)) as [Lt | Ge].
  - rewrite (H1 Lt). destruct (Rle_or_lt 0 (B x)) as [P | N].
    + left. rewrite Rabs_pos_eq in Ax by lra. apply round_ge_generic; [exact _ | exact _ | exact F1 | lra].
    + right. rewrite Rabs_left in Ax by lra. apply round_le_generic; [exact _ | exact _ | exact F2 | lra].
  - left. rewrite (H2 Ge). apply Rle_trans with (2 := Ge).
    apply Rle_trans with (bpow radix2 1); [simpl; lra | apply bpow_le; lia].
Qed.

(** [ln_1p]'s accurate path: on both branches, the 128-bit value is within
    [2^-123] relatively of [ln(1 + x)], and [Q128::to_f64] rounds it once. *)
Theorem ln_1p_acc_ok x : finite x -> -1 < B x -> bpow radix2 (-54) <= Rabs (B x) ->
  QSpec.normalized 128 (Q128.m (ln_1p_acc x)) /\
  Rabs (Q128.qval (ln_1p_acc x) - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) /\
  B (Q128.to_f64 (ln_1p_acc x)) = rndF (Q128.qval (ln_1p_acc x)).
Proof.
  intros Fx Hx Ax.
  assert (Nx : B x <> 0) by (intros Z0; rewrite Z0, Rabs_R0 in Ax; pose proof (bpow_gt_0 radix2 (-54)); lra).
  assert (Nl : ln (1 + B x) <> 0).
  { intros Z0. apply Nx. assert (1 + B x = 1) by (rewrite <- (exp_ln (1 + B x)) by lra; rewrite Z0; apply exp_0). lra. }
  set (lx := ln (1 + B x)) in *.
  assert (Norm : forall a, NZ a -> Rabs (Q128.qval a - lx) <= / 2 ^ 123 * Rabs lx -> QSpec.normalized 128 (Q128.m a)).
  { intros a [Za | Na] Ha; [ | exact Na]. exfalso. rewrite (qval_zero a Za), Rminus_0_l, Rabs_Ropp in Ha.
    assert (/ 2 ^ 123 < 1) by interval with (i_prec 64). pose proof (Rabs_pos_lt _ Nl). nra. }
  unfold ln_1p_acc. destruct (small7 x) eqn:S.
  - (* |x| < 2^-7: z = x exactly *)
    apply (small7_ok x Fx) in S. change (bpow radix2 (-7)) with (/ 128) in S.
    pose proof (from_f64_nz (bits_of_b64 x)) as Nz. fold (qf x) in Nz.
    assert (Vz : Q128.qval (qf x) = B x) by (unfold qf; rewrite from_f64_b64 by exact Fx; reflexivity).
    destruct (lnz_ok (qf x) Nz ltac:(rewrite Vz; lra)) as [NL [X1 [E1 [mz [HX1 [HE1 [Hmz EL]]]]]]].
    rewrite Vz in EL. fold lx in EL.
    assert (Bd : Rabs (Q128.qval (lnz (qf x)) - lx) <= / 2 ^ 123 * Rabs lx).
    { rewrite EL. replace (lx * (1 + E1 / X1) * (1 + mz) - lx) with (lx * ((X1 + E1) * (1 + mz) / X1 - 1))
        by (field; lra).
      rewrite Rabs_mult, Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | ].
      exact (LnAccurateLevels.sum_a X1 E1 mz HX1 HE1 Hmz). }
    pose proof (Norm _ NL Bd) as Nn.
    split; [exact Nn | split; [exact Bd | ]].
    apply to_f64_small; [exact Nn | ]. apply (small_value _ lx Bd).
    unfold lx. apply Rabs_le. split; interval with (i_prec 64).
  - (* |x| >= 2^-7: 1 + x = h + l, h reduced *)
    assert (Ax7 : bpow radix2 (-7) <= Rabs (B x))
      by (apply Rnot_lt_le; intros Lt; apply (small7_ok x Fx) in Lt; rewrite Lt in S; discriminate).
    pose proof (split_ok x Fx Hx) as SO. destruct (split x) as [h l].
    destruct SO as [Fh [Fl [Ehl [Ph [Hl [H1 H2]]]]]].
    pose proof (h_far x h Fx Hx Ax7 H1 H2) as Far.
    pose proof (LnReduction.reduce_ok h Fh Ph) as RO.
    destruct (LnReduction.reduce h) as [[[e i] y] r].
    destruct RO as [Hi [Er [Fy [Iy [Gy [Eh He]]]]]]. subst r.
    destruct (LnReduction.z_exact_ok y i Hi Fy Iy) as [Nz Vz].
    destruct (LnReduction.ln_range i Hi) as [L1 [L2 _]].
    pose proof (LnReduction.z_range y i Hi Iy Gy) as [PR [Zb _]].
    destruct (ln_r_finite i Hi) as [Fr [R1 R2]].
    set (R := B (ln_r i)) in *.
    set (t := B l * bpow radix2 (- e)).
    assert (Pe : 0 < bpow radix2 e) by apply bpow_gt_0.
    assert (Ht : Rabs t <= 1.0001 / 9007199254740992 * B y).
    { unfold t. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- e))) by apply bpow_ge_0.
      rewrite Eh in Hl. replace (B y) with (bpow radix2 e * B y * bpow radix2 (- e))
        by (rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l; simpl; ring).
      rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
    set (Y := B y + t).
    assert (EY : 1 + B x = bpow radix2 e * Y).
    { unfold Y, t. rewrite Rmult_plus_distr_l, <- Eh, <- Rmult_assoc, (Rmult_comm (bpow radix2 e)), Rmult_assoc,
        <- bpow_plus, Z.add_opp_diag_r, Rmult_1_r. lra. }
    assert (Tb : Rabs t <= 1.0001 / 9007199254740992 * 1.4140625) by (apply Rle_trans with (1 := Ht); lra).
    assert (HY : ln_lo i - / 2 ^ 52 <= Y <= ln_hi i + / 2 ^ 52).
    { assert (/ 2 ^ 52 = 2 / 9007199254740992) by (simpl; field). apply Rabs_le_inv in Tb. unfold Y. lra. }
    assert (PY : 0 < Y) by (unfold Y; apply Rabs_le_inv in Tb; lra).
    assert (Lx : lx = IZR e * ln 2 + ln Y) by (unfold lx; rewrite EY; apply ln_pow2; exact PY).
    (* the low part, R·l·2^-E in Q128 *)
    pose proof (from_f64_nz (bits_of_b64 (ln_r i))) as Nr. fold (qf (ln_r i)) in Nr.
    pose proof (from_f64_nz (bits_of_b64 l)) as Nl'. fold (qf l) in Nl'.
    destruct (mul_any _ _ Nr Nl') as [NM [m [Hm EM]]].
    change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hm. rewrite bpow_m in Hm.
    unfold qf in EM. rewrite !from_f64_b64 in EM by assumption. fold R in EM.
    pose proof (nz_mul_pow2 _ (- e) NM) as NLo.
    set (low := Q128.mul_pow2 (Q128.mul (qf (ln_r i)) (qf l)) (- e)) in *.
    assert (Vlow : Q128.qval low = R * t * (1 + m)).
    { unfold low. rewrite Q128.mul_pow2_ok. fold (qf (ln_r i)) (qf l) in EM |- *. unfold qf in *. rewrite EM. unfold t. ring. }
    destruct (add_any _ _ Nz NLo) as [NZp EZp].
    change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in EZp. rewrite bpow_m in EZp.
    set (zc := Q128.qval (z_prime e y (ln_r i) l)).
    assert (Ezc : zc = Q128.qval (Q128.add (LnReduction.z_exact y (ln_r i)) low)) by reflexivity.
    rewrite <- Ezc, Vz, Vlow in EZp.
    set (zp := Y * R - 1).
    assert (Ezp : zp = (B y * R - 1) + R * t) by (unfold zp, Y; ring).
    assert (U : 0 < / 2 ^ 127 <= / 10 ^ 38) by (split; interval with (i_prec 64)).
    assert (Rt : Rabs (R * t) <= / 10 ^ 15) by (rewrite Rabs_mult, (Rabs_pos_eq R) by lra; pose proof (Rabs_pos t); nra).
    assert (Rtm : Rabs (R * t * (1 + m)) <= / 10 ^ 15).
    { rewrite Rabs_mult. assert (Rabs (1 + m) <= 1) by (apply Rabs_le; lra). pose proof (Rabs_pos (R * t)).
      pose proof (Rabs_pos (1 + m)). nra. }
    assert (Dz : Rabs (zc - zp) <= / 2 ^ 133 + / 2 ^ 170).
    { rewrite Ezp. replace (zc - (B y * R - 1 + R * t))
        with ((zc - (B y * R - 1 + R * t * (1 + m))) + R * t * m) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat.
      - apply Rle_trans with (1 := EZp).
        replace (/ 2 ^ 133) with (/ 2 ^ 126 * / 128) by (simpl; field).
        apply Rmult_le_compat_l; [lra | apply Rmax_lub; [exact Zb | lra]].
      - rewrite Rabs_mult. apply Rle_trans with (/ 10 ^ 15 * / 2 ^ 127);
          [apply Rmult_le_compat; try apply Rabs_pos; [exact Rt | apply Rabs_le; lra] | interval with (i_prec 64)]. }
    assert (Zp : Rabs zp <= / 128 + / 10 ^ 15).
    { rewrite Ezp. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
    assert (Zc : Rabs zc <= 0.0078126).
    { replace zc with (zp + (zc - zp)) by ring. apply Rle_trans with (1 := Rabs_triang _ _).
      assert (/ 128 + / 10 ^ 15 + (/ 2 ^ 133 + / 2 ^ 170) <= 0.0078126) by interval with (i_prec 64). lra. }
    (* no case A: h is at least 2^-7 from 1 *)
    assert (Hex : e = 0%Z -> R = 1 -> zc = Y * R - 1).
    { intros E0 R1'. exfalso. subst e. destruct (LnTableCheck.ln_r_one i Hi R1') as [I | I]; subst i;
        unfold ln_lo, ln_hi in Iy; cbn [Nat.ltb Nat.leb INR] in Iy;
        rewrite Eh in Far; simpl bpow in Far; rewrite Rmult_1_l in Far; lra. }
    (* the computed z' moves ln(1 + z') by little, against |ln(1 + x)| >= ln(1 + 2^-7) *)
    assert (Lb : ln (1 + / 128) <= Rabs lx).
    { change (bpow radix2 (-7)) with (/ 128) in Ax7. unfold lx.
      destruct (Rle_or_lt 0 (B x)) as [P | N].
      - rewrite Rabs_pos_eq in Ax7 by lra.
        assert (ln (1 + / 128) <= ln (1 + B x)) by (apply LnTableCheck.ln_le_mono; lra).
        assert (0 < ln (1 + / 128)) by interval with (i_prec 64). rewrite Rabs_pos_eq; lra.
      - rewrite Rabs_left in Ax7 by lra.
        assert (ln (1 + B x) <= ln (1 - / 128)) by (apply LnTableCheck.ln_le_mono; lra).
        assert (ln (1 + / 128) <= - ln (1 - / 128)) by interval with (i_prec 64).
        assert (ln (1 - / 128) < 0) by interval with (i_prec 64). rewrite Rabs_left; lra. }
    assert (Hdz : Rabs (ln (1 + zc) - ln (Y * R)) * (1 + / 2 ^ 100) <= 524 * / 2 ^ 135 * Rabs (IZR e * ln 2 + ln Y)).
    { rewrite <- Lx. replace (Y * R) with (1 + zp) by (unfold zp; ring).
      assert (M0 : 0 < 1 - 0.0078126) by lra.
      pose proof (ln_lip (1 + zc) (1 + zp) (1 - 0.0078126) M0
                    ltac:(apply Rabs_le_inv in Zc; lra) ltac:(apply Rabs_le_inv in Zp; lra)) as LL.
      replace (1 + zc - (1 + zp)) with (zc - zp) in LL by ring.
      assert (Q : (/ 2 ^ 133 + / 2 ^ 170) / (1 - 0.0078126) * (1 + / 2 ^ 100) <= 524 * / 2 ^ 135 * ln (1 + / 128))
        by interval with (i_prec 100).
      assert (Rabs (zc - zp) / (1 - 0.0078126) <= (/ 2 ^ 133 + / 2 ^ 170) / (1 - 0.0078126))
        by (unfold Rdiv; apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Dz]).
      assert (0 < 1 + / 2 ^ 100) by (assert (0 < / 2 ^ 100) by interval with (i_prec 64); lra).
      assert (0 <= 524 * / 2 ^ 135) by (apply Rlt_le; interval with (i_prec 64)).
      pose proof (Rabs_pos (ln (1 + zc) - ln (1 + zp))). nra. }
    destruct (acc_value_ok e i Y (z_prime e y (ln_r i) l) Hi ltac:(lia) HY NZp Zc Hex Hdz ltac:(rewrite <- Lx; exact Nl))
      as [Nn Bd].
    rewrite <- Lx in Bd.
    split; [exact Nn | split; [exact Bd | ]].
    apply to_f64_small; [exact Nn | ]. apply (small_value _ lx Bd). rewrite Lx.
    apply lx_small; [lia | apply Rabs_le_inv in Tb; unfold Y; lra].
Qed.
