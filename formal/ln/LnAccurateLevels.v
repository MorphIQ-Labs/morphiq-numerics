(** The accurate path's certificates over reals (docs/ln.md, section 6),
    written by generators/ln_certificates.py with the same bounds it writes
    into formal/ln/accurate_level_*.g and accurate_sum_*.g; do not edit. Each
    theorem is its certificate's, applied through the Coq proof Gappa writes
    for it. *)

From Coq Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Gappa Require Gappa_definitions Gappa_pred_bnd.
Require ln_accurate_level_01 ln_accurate_level_02 ln_accurate_level_03 ln_accurate_level_04 ln_accurate_level_05 ln_accurate_level_06 ln_accurate_level_07 ln_accurate_level_08 ln_accurate_level_09 ln_accurate_level_10 ln_accurate_level_11 ln_accurate_level_12 ln_accurate_level_13 ln_accurate_level_14 ln_accurate_level_15 ln_accurate_level_16 ln_accurate_level_17 ln_accurate_sum_a ln_accurate_sum_b ln_accurate_sum_c.

Open Scope R_scope.

(** Reduces a Gappa interval to numerals, leaving the real operators. *)
Ltac gappa_num := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult].
Ltac gappa_num_in H := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult] in H.

(** A certificate [l1 : hypotheses /\ ~ conclusion -> False], read as
    [hypotheses -> conclusion]. *)
Ltac bridge l1 bound :=
  apply Rnot_lt_le; intros Hlt; apply l1;
  repeat split; try (gappa_num; simpl; lra);
  intros Hb; gappa_num_in Hb; cbv [Gappa_pred_bnd.Float1] in Hb;
  apply (Rlt_irrefl bound); apply Rlt_le_trans with (1 := Hlt);
  apply Rabs_le; simpl in Hb |- *; lra.

(** Level 17: [G_17 = (1/17)(1 + kk) − (z·G_18)(1 + m) + s] against
    [X_17 = 1/17 − z·X_18]. *)
Theorem level_17 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.054592922 <= Xn <= 0.056526412 -> Rabs En <= 920 * / 2 ^ 141 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 17 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 17 - z * Xn))
    <= 533 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_17.l1 kk z Xn En m s) (533 * / 2 ^ 135).
Qed.

(** Level 16: [G_16 = (1/16)(1 + kk) − (z·G_17)(1 + m) + s] against
    [X_16 = 1/16 − z·X_17]. *)
Theorem level_16 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.057805601 <= Xn <= 0.059850138 -> Rabs En <= 533 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 16 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 16 - z * Xn))
    <= 538 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_16.l1 kk z Xn En m s) (538 * / 2 ^ 135).
Qed.

(** Level 15: [G_15 = (1/15)(1 + kk) − (z·G_16)(1 + m) + s] against
    [X_15 = 1/15 − z·X_16]. *)
Theorem level_15 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.061420031 <= Xn <= 0.063589160 -> Rabs En <= 538 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 15 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 15 - z * Xn))
    <= 539 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_15.l1 kk z Xn En m s) (539 * / 2 ^ 135).
Qed.

(** Level 14: [G_14 = (1/14)(1 + kk) − (z·G_15)(1 + m) + s] against
    [X_14 = 1/14 − z·X_15]. *)
Theorem level_14 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.065516595 <= Xn <= 0.067826504 -> Rabs En <= 539 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 14 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 14 - z * Xn))
    <= 540 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_14.l1 kk z Xn En m s) (540 * / 2 ^ 135).
Qed.

(** Level 13: [G_13 = (1/13)(1 + kk) − (z·G_14)(1 + m) + s] against
    [X_13 = 1/13 − z·X_14]. *)
Theorem level_13 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.070198654 <= Xn <= 0.072668906 -> Rabs En <= 540 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 13 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 13 - z * Xn))
    <= 542 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_13.l1 kk z Xn En m s) (542 * / 2 ^ 135).
Qed.

(** Level 12: [G_12 = (1/12)(1 + kk) − (z·G_13)(1 + m) + s] against
    [X_12 = 1/12 − z·X_13]. *)
Theorem level_12 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.075601384 <= Xn <= 0.078255931 -> Rabs En <= 542 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 12 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 12 - z * Xn))
    <= 544 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_12.l1 kk z Xn En m s) (544 * / 2 ^ 135).
Qed.

(** Level 11: [G_11 = (1/11)(1 + kk) − (z·G_12)(1 + m) + s] against
    [X_11 = 1/11 − z·X_12]. *)
Theorem level_11 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.081905040 <= Xn <= 0.084773646 -> Rabs En <= 544 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 11 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 11 - z * Xn))
    <= 546 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_11.l1 kk z Xn En m s) (546 * / 2 ^ 135).
Qed.

(** Level 10: [G_10 = (1/10)(1 + kk) − (z·G_11)(1 + m) + s] against
    [X_10 = 1/10 − z·X_11]. *)
Theorem level_10 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.089355460 <= Xn <= 0.092475742 -> Rabs En <= 546 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 10 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 10 - z * Xn))
    <= 548 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_10.l1 kk z Xn En m s) (548 * / 2 ^ 135).
Qed.

(** Level 9: [G_9 = (1/9)(1 + kk) − (z·G_10)(1 + m) + s] against
    [X_9 = 1/9 − z·X_10]. *)
Theorem level_09 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.098296866 <= Xn <= 0.101717339 -> Rabs En <= 548 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 9 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 9 - z * Xn))
    <= 551 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_09.l1 kk z Xn En m s) (551 * / 2 ^ 135).
Qed.

(** Level 8: [G_8 = (1/8)(1 + kk) − (z·G_9)(1 + m) + s] against
    [X_8 = 1/8 − z·X_9]. *)
Theorem level_08 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.109226553 <= Xn <= 0.113011295 -> Rabs En <= 551 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 8 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 8 - z * Xn))
    <= 555 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_08.l1 kk z Xn En m s) (555 * / 2 ^ 135).
Qed.

(** Level 7: [G_7 = (1/7)(1 + kk) − (z·G_8)(1 + m) + s] against
    [X_7 = 1/7 − z·X_8]. *)
Theorem level_07 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.122890614 <= Xn <= 0.127126747 -> Rabs En <= 555 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 7 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 7 - z * Xn))
    <= 559 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_07.l1 kk z Xn En m s) (559 * / 2 ^ 135).
Qed.

(** Level 6: [G_6 = (1/6)(1 + kk) − (z·G_7)(1 + m) + s] against
    [X_6 = 1/6 − z·X_7]. *)
Theorem level_06 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.140461762 <= Xn <= 0.145272055 -> Rabs En <= 559 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 6 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 6 - z * Xn))
    <= 565 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_06.l1 kk z Xn En m s) (565 * / 2 ^ 135).
Qed.

(** Level 5: [G_5 = (1/5)(1 + kk) − (z·G_6)(1 + m) + s] against
    [X_5 = 1/5 − z·X_6]. *)
Theorem level_05 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.163895075 <= Xn <= 0.169460580 -> Rabs En <= 565 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 5 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 5 - z * Xn))
    <= 574 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_05.l1 kk z Xn En m s) (574 * / 2 ^ 135).
Qed.

(** Level 4: [G_4 = (1/4)(1 + kk) − (z·G_5)(1 + m) + s] against
    [X_4 = 1/4 − z·X_5]. *)
Theorem level_04 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.196710921 <= Xn <= 0.203315121 -> Rabs En <= 574 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 4 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 4 - z * Xn))
    <= 587 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_04.l1 kk z Xn En m s) (587 * / 2 ^ 135).
Qed.

(** Level 3: [G_3 = (1/3)(1 + kk) − (z·G_4)(1 + m) + s] against
    [X_3 = 1/3 − z·X_4]. *)
Theorem level_03 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.245953105 <= Xn <= 0.254078145 -> Rabs En <= 587 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 3 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 3 - z * Xn))
    <= 609 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_03.l1 kk z Xn En m s) (609 * / 2 ^ 135).
Qed.

(** Level 2: [G_2 = (1/2)(1 + kk) − (z·G_3)(1 + m) + s] against
    [X_2 = 1/2 − z·X_3]. *)
Theorem level_02 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.328066382 <= Xn <= 0.338639348 -> Rabs En <= 609 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 2 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 2 - z * Xn))
    <= 652 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_02.l1 kk z Xn En m s) (652 * / 2 ^ 135).
Qed.

(** Level 1: [G_1 = (1/1)(1 + kk) − (z·G_2)(1 + m) + s] against
    [X_1 = 1/1 − z·X_2]. *)
Theorem level_01 kk z Xn En m s :
  Rabs z <= 0.0078126 -> 0.492421842 <= Xn <= 0.507630242 -> Rabs En <= 652 * / 2 ^ 135 ->
  Rabs kk <= / 2 ^ 127 -> - / 2 ^ 127 <= m <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 / 1 * (1 + kk) - z * (Xn + En) * (1 + m) + s - (1 / 1 - z * Xn))
    <= 782 * / 2 ^ 135.
Proof.
  intros Hz HX HE Hk Hm Hs.
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_level_01.l1 kk z Xn En m s) (782 * / 2 ^ 135).
Qed.

(** Case A: [ln x = z·X1]. *)
Theorem sum_a X1 E1 mz :
  0.995118 <= X1 <= 1.004931 -> Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 ->
  Rabs ((X1 + E1) * (1 + mz) / X1 - 1) <= / 2 ^ 123.
Proof.
  intros HX HE Hm. apply Rabs_le_inv in HE.
  bridge (ln_accurate_sum_a.l1 X1 E1 mz) (/ 2 ^ 123).
Qed.

(** Case B: [ln x = N + z·X1], [k3 = z·X1 / ln x]. *)
Theorem sum_b X1 k3 eN E1 mz dz s2 :
  0.995118 <= X1 <= 1.004931 -> Rabs k3 <= 533 * / 2 ^ 10 -> Rabs eN <= / 2 ^ 127 ->
  Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 -> Rabs dz <= 524 * / 2 ^ 135 ->
  Rabs s2 <= 784 * / 2 ^ 135 ->
  Rabs ((1 - k3) * (1 + eN) + k3 * (1 + E1 / X1) * (1 + mz) + dz + s2 - 1) <= / 2 ^ 123.
Proof.
  intros HX Hk HeN HE Hm Hdz Hs.
  apply Rabs_le_inv in Hk. apply Rabs_le_inv in HeN. apply Rabs_le_inv in HE.
  apply Rabs_le_inv in Hdz. apply Rabs_le_inv in Hs.
  bridge (ln_accurate_sum_b.l1 X1 k3 eN E1 mz dz s2) (/ 2 ^ 123).
Qed.

(** Case C: [ln x = E·ln 2 + N + z·X1], [k2 = N / ln x], [k3 = z·X1 / ln x]. *)
Theorem sum_c X1 k2 k3 eL mL eN s1 E1 mz dz s2 :
  0.995118 <= X1 <= 1.004931 -> Rabs k2 <= 514 * / 2 ^ 9 -> Rabs k3 <= 752 * / 2 ^ 16 ->
  Rabs eL <= / 2 ^ 127 -> - / 2 ^ 127 <= mL <= 0 -> Rabs eN <= / 2 ^ 127 ->
  Rabs s1 <= 518 * / 2 ^ 134 -> Rabs E1 <= 818 * / 2 ^ 135 -> - / 2 ^ 127 <= mz <= 0 ->
  Rabs dz <= 524 * / 2 ^ 135 -> Rabs s2 <= 523 * / 2 ^ 135 ->
  Rabs ((1 - k2 - k3) * (1 + eL) * (1 + mL) + k2 * (1 + eN) + s1 + k3 * (1 + E1 / X1) * (1 + mz) + dz + s2 - 1)
    <= / 2 ^ 123.
Proof.
  intros HX Hk2 Hk3 HeL HmL HeN Hs1 HE Hm Hdz Hs2.
  apply Rabs_le_inv in Hk2. apply Rabs_le_inv in Hk3. apply Rabs_le_inv in HeL. apply Rabs_le_inv in HeN.
  apply Rabs_le_inv in Hs1. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hdz. apply Rabs_le_inv in Hs2.
  bridge (ln_accurate_sum_c.l1 X1 k2 k3 eL mL eN s1 E1 mz dz s2) (/ 2 ^ 123).
Qed.
