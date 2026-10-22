(** asinh's large form, [x >= 2^28]: the expansion against [arcsinh], and the
    transcription's fast value. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinhWithin.
Open Scope R_scope.

Definition E114 : R := / 20769187434139310514121985316880384.

Lemma G_plus t : 0 <= t <= / 72057594037927936 ->
  0 <= exp (t / 4 + E114) - (t / 4) * exp (- (t / 4 + E114)) - 1.
Proof.
  intros H. unfold E114. destruct H as [H0 H1].
  interval with (i_bisect t, i_taylor t, i_prec 300, i_degree 8, i_depth 30).
Qed.

Lemma G_minus t : 0 <= t <= / 72057594037927936 ->
  exp (t / 4 - E114) - (t / 4) * exp (- (t / 4 - E114)) - 1 <= 0.
Proof.
  intros H. unfold E114. destruct H as [H0 H1].
  interval with (i_bisect t, i_taylor t, i_prec 300, i_degree 8, i_depth 30).
Qed.

Lemma sinh_form X t u : 0 < X -> t = / (X * X) ->
  sinh (ln (2 * X) + u) = X * (exp u - (t / 4) * exp (- u)).
Proof.
  intros HX Ht. subst t. unfold sinh.
  assert (E1 : exp (ln (2 * X) + u) = 2 * X * exp u) by (rewrite exp_plus, exp_ln by lra; reflexivity).
  assert (E2 : exp (- (ln (2 * X) + u)) = / (2 * X) * exp (- u)).
  { replace (- (ln (2 * X) + u)) with (- ln (2 * X) + - u) by ring. rewrite exp_plus, exp_Ropp, exp_ln by lra. reflexivity. }
  rewrite E1, E2. field. lra.
Qed.

(** The large-argument expansion: [arcsinh X = ln 2 + ln X + 1/(4 X^2) + r], [|r| <= 2^-114]. *)
Theorem large_expansion X : 268435456 <= X ->
  Rabs (arcsinh X - (ln 2 + ln X + / (X * X) / 4)) <= E114.
Proof.
  intros HX. set (t := / (X * X)).
  assert (HX0 : 0 < X) by lra.
  assert (Ht : 0 <= t <= / 72057594037927936).
  { split; [unfold t; apply Rlt_le, Rinv_0_lt_compat; nra | ].
    unfold t. apply Rinv_le_contravar; [lra | nra]. }
  assert (Hln : ln (2 * X) = ln 2 + ln X) by (apply ln_mult; lra).
  assert (H1 : sinh (ln (2 * X) + t / 4 - E114) - X <= 0).
  { replace (ln (2 * X) + t / 4 - E114) with (ln (2 * X) + (t / 4 - E114)) by ring.
    rewrite (sinh_form X t) by (try exact HX0; reflexivity). pose proof (G_minus t Ht) as G.
    pose proof (Rmult_le_compat_l X _ _ ltac:(lra) G). lra. }
  assert (H2 : 0 <= sinh (ln (2 * X) + t / 4 + E114) - X).
  { replace (ln (2 * X) + t / 4 + E114) with (ln (2 * X) + (t / 4 + E114)) by ring.
    rewrite (sinh_form X t) by (try exact HX0; reflexivity). pose proof (G_plus t Ht) as G.
    pose proof (Rmult_le_compat_l X _ _ ltac:(lra) G). lra. }
  pose proof (asinh_within X (ln (2 * X) + t / 4) E114 H1 H2) as Hw.
  rewrite Hln in Hw. exact Hw.
Qed.

(** The pure-real composition of the large form's error. *)
Lemma large_final (A lnX l2 LN LN2 S1 ea1 c t4 ea2 r Y : R) :
  A = lnX + l2 + t4 + r -> Rabs r <= E114 -> 19.4 <= lnX -> lnX <= 710 -> 0.69 <= l2 <= 0.6932 ->
  Rabs (LN - lnX) <= / 18446744073709551616 * Rabs lnX -> Rabs (LN2 - l2) <= 1e-30 ->
  S1 = (LN + LN2) * (1 + ea1) -> Rabs ea1 <= 1e-31 ->
  0 <= t4 <= 4e-18 -> Rabs (c - t4) <= 1e-33 ->
  Y = (S1 + c) * (1 + ea2) -> Rabs ea2 <= 2.5e-32 ->
  Rabs (Y - A) <= / 9223372036854775808 * A.
Proof.
  intros HA Hr HlnXl HlnXh Hl2 HLN HLN2 HS1 Hea1 Ht4 Hc HY Hea2.
  assert (HE : E114 <= 1e-34) by (unfold E114; apply Rle_trans with (/ 10000000000000000000000000000000000); [apply Rinv_le_contravar; lra | lra]).
  rewrite (Rabs_pos_eq lnX) in HLN by lra.
  destruct Hl2 as [Hl21 Hl22]. destruct Ht4 as [Ht1 Ht2].
  apply Rabs_le_inv in HLN. destruct HLN as [HL1 HL2].
  apply Rabs_le_inv in HLN2. destruct HLN2 as [HN1 HN2].
  apply Rabs_le_inv in Hr. destruct Hr as [Hr1 Hr2].
  assert (Hlnb : / 18446744073709551616 * lnX <= 4e-17) by (assert (/ 18446744073709551616 * lnX <= / 18446744073709551616 * 710) by (apply Rmult_le_compat_l; lra); lra).
  set (T := LN + LN2).
  assert (HTd : T = LN + LN2) by reflexivity.
  assert (HT : Rabs (T - (lnX + l2)) <= 5e-17) by (apply Rabs_le; split; lra).
  assert (HTb : Rabs T <= 1.001 * (lnX + l2)).
  { apply Rabs_le_inv in HT. destruct HT as [Ha Hb]. apply Rabs_le. split; lra. }
  assert (Hp1 : Rabs (T * ea1) <= (1.001 * (lnX + l2)) * 1e-31).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  apply Rabs_le_inv in Hp1. destruct Hp1 as [Hp11 Hp12].
  apply Rabs_le_inv in Hc. destruct Hc as [Hc1 Hc2].
  assert (Hs1 : S1 = T + T * ea1) by (rewrite HS1; unfold T; ring).
  set (U := S1 + c).
  assert (HUb : Rabs U <= 1.001 * A).
  { apply Rabs_le. unfold U. split; lra. }
  assert (Hp2 : Rabs (U * ea2) <= (1.001 * A) * 2.5e-32).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  apply Rabs_le_inv in Hp2. destruct Hp2 as [Hp21 Hp22].
  assert (Hid : Y - A = (S1 + c - A) + U * ea2) by (rewrite HY; unfold U; ring).
  rewrite Hid. 
  apply Rabs_le. split; unfold U in *; lra.
Qed.
