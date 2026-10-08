(** The accurate path's certificates over reals, written by
    generators/exp_accurate_certificates.py with the same bounds it writes into
    formal/exp/accurate_level_*.g and accurate_y.g; do not edit. Each theorem is
    its certificate's, applied through the Coq proof Gappa writes for it. *)

From Coq Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Gappa Require Gappa_definitions Gappa_pred_bnd.
Require exp_accurate_level_01 exp_accurate_level_02 exp_accurate_level_03 exp_accurate_level_04 exp_accurate_level_05 exp_accurate_level_06 exp_accurate_level_07 exp_accurate_level_08 exp_accurate_level_09 exp_accurate_level_10 exp_accurate_level_11 exp_accurate_level_12 exp_accurate_y.

Open Scope R_scope.

(** Reduces a Gappa interval to numerals, leaving the real operators. *)
Ltac gappa_num := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult].
Ltac gappa_num_in H := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult] in H.

(** A certificate [l1 : hypotheses /\\ ~ conclusion -> False], read as
    [hypotheses -> conclusion]. *)
Ltac bridge l1 bound :=
  apply Rnot_lt_le; intros Hlt; apply l1;
  repeat split; try (gappa_num; simpl; lra);
  intros Hb; gappa_num_in Hb; cbv [Gappa_pred_bnd.Float1] in Hb;
  apply (Rlt_irrefl bound); apply Rlt_le_trans with (1 := Hlt);
  apply Rabs_le; simpl in Hb |- *; lra.

(** Level 12: [H_12 = 1 + (r·k_12)·H_13] against [X_12 = 1 + (r/12)·X_13]. *)
Theorem level_12 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 0 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 12 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 12 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_12.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 11: [H_11 = 1 + (r·k_11)·H_12] against [X_11 = 1 + (r/11)·X_12]. *)
Theorem level_11 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 11 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 11 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_11.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 10: [H_10 = 1 + (r·k_10)·H_11] against [X_10 = 1 + (r/10)·X_11]. *)
Theorem level_10 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 10 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 10 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_10.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 9: [H_9 = 1 + (r·k_9)·H_10] against [X_9 = 1 + (r/9)·X_10]. *)
Theorem level_09 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 9 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 9 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_09.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 8: [H_8 = 1 + (r·k_8)·H_9] against [X_8 = 1 + (r/8)·X_9]. *)
Theorem level_08 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 8 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 8 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_08.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 7: [H_7 = 1 + (r·k_7)·H_8] against [X_7 = 1 + (r/7)·X_8]. *)
Theorem level_07 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 7 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 7 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_07.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 6: [H_6 = 1 + (r·k_6)·H_7] against [X_6 = 1 + (r/6)·X_7]. *)
Theorem level_06 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 6 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 6 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_06.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 5: [H_5 = 1 + (r·k_5)·H_6] against [X_5 = 1 + (r/5)·X_6]. *)
Theorem level_05 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 5 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 5 * Xn))
    <= 518 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_05.l1 r k ma Xn En mb s) (518 * / 2 ^ 135).
Qed.

(** Level 4: [H_4 = 1 + (r·k_4)·H_5] against [X_4 = 1 + (r/4)·X_5]. *)
Theorem level_04 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 518 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 4 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 4 * Xn))
    <= 519 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_04.l1 r k ma Xn En mb s) (519 * / 2 ^ 135).
Qed.

(** Level 3: [H_3 = 1 + (r·k_3)·H_4] against [X_3 = 1 + (r/3)·X_4]. *)
Theorem level_03 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 519 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 3 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 3 * Xn))
    <= 519 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_03.l1 r k ma Xn En mb s) (519 * / 2 ^ 135).
Qed.

(** Level 2: [H_2 = 1 + (r·k_2)·H_3] against [X_2 = 1 + (r/2)·X_3]. *)
Theorem level_02 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 519 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 2 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 2 * Xn))
    <= 519 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_02.l1 r k ma Xn En mb s) (519 * / 2 ^ 135).
Qed.

(** Level 1: [H_1 = 1 + (r·k_1)·H_2] against [X_1 = 1 + (r/1)·X_2]. *)
Theorem level_01 r k ma Xn En mb s :
  Rabs r <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= 519 * / 2 ^ 135 ->
  Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
  Rabs (1 + (r * (1 / 1 * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + r / 1 * Xn))
    <= 521 * / 2 ^ 135.
Proof.
  intros Hr HX HE Hk Hma Hmb Hs.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
  bridge (exp_accurate_level_01.l1 r k ma Xn En mb s) (521 * / 2 ^ 135).
Qed.

(** [Y = T_j·H_1] against [T_j·X_1]: within [2^-124] relatively. *)
Theorem accurate_y_bound Tj X1 eT E1 mY :
  1 <= Tj <= 2 -> 0.997 <= X1 <= 1.003 -> Rabs eT <= / 2 ^ 127 ->
  Rabs E1 <= 521 * / 2 ^ 135 -> - / 2 ^ 127 <= mY <= 0 ->
  Rabs ((Tj * (1 + eT) * (X1 + E1) * (1 + mY) - Tj * X1) / (Tj * X1)) <= / 2 ^ 124.
Proof.
  intros HT HX He HE Hm.
  apply Rabs_le_inv in He. apply Rabs_le_inv in HE.
  bridge (exp_accurate_y.l1 Tj X1 eT E1 mY) (/ 2 ^ 124).
Qed.
