(** The logarithmic form's square root: the double-word [root + c] is
    [sqrt (uh + ul)] to a relative [2^-90], by one Newton correction of
    [root = RN (sqrt uh)] (docs/asinh.md section 3; the bound is far looser than
    [root.g]'s [2^-100], which the fast path's budget does not need). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
Open Scope R_scope.

Lemma Rabs_div' a b : b <> 0 -> Rabs (a / b) = Rabs a / Rabs b.
Proof. intros H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact H. reflexivity. Qed.

(** A rounding: error at most [2^-53] of the value's bound plus [eta]. *)
Lemma rnd_step r v M eta :
  Rabs (r - v) <= / 9007199254740992 * Rabs v + eta -> Rabs v <= M -> Rabs (r - v) <= / 9007199254740992 * M + eta.
Proof. intros H1 H2. assert (/ 9007199254740992 * Rabs v <= / 9007199254740992 * M) by (apply Rmult_le_compat_l; lra). lra. Qed.

(** [|a / (2 r)|] from [|a| <= K x^2] and [r >= 0.99999 x]. *)
Lemma div_lem a x r K : 0 < x -> 0.99999 * x <= r -> 0 <= K -> Rabs a <= K * (x * x) -> Rabs (a / (2 * r)) <= K * x.
Proof.
  intros Hx Hr HK Ha. assert (Hrp : 0 < r) by lra.
  rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq (2 * r)) by lra.
  apply Rmult_le_reg_r with (2 * r); [lra | ].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
  assert (K * (x * x) <= K * x * (2 * r)).
  { assert (x * x <= x * (2 * r)) by nra. nra. }
  lra.
Qed.

(** Products near [w^2]. *)
Lemma sq_near w root rho : 1 <= w -> Rabs (root - w) <= rho * w -> 0 <= rho -> rho <= / 1000000 ->
  Rabs (w * w - root * root) <= 2.00001 * rho * (w * w) /\ root * root <= 1.00003 * (w * w) /\ 0.99999 * w <= root.
Proof.
  intros W1 H R0 R1. apply Rabs_le_inv in H.
  assert (Hlo : 0.999999 * w <= root).
  { assert (rho * w <= / 1000000 * w) by (apply Rmult_le_compat_r; lra). lra. }
  assert (Hhi : root <= 1.000001 * w).
  { assert (rho * w <= / 1000000 * w) by (apply Rmult_le_compat_r; lra). lra. }
  assert (Hr0 : 0 <= root) by nra.
  repeat split.
  - assert (E : w * w - root * root = (w - root) * (w + root)) by ring. rewrite E, Rabs_mult.
    apply Rle_trans with ((rho * w) * (2.00001 * w)).
    + apply Rmult_le_compat; try apply Rabs_pos; [rewrite Rabs_minus_sym; apply Rabs_le; lra | ].
      rewrite Rabs_pos_eq by lra. lra.
    + nra.
  - assert (root * root <= (1.000001 * w) * (1.000001 * w)) by (apply Rmult_le_compat; lra). nra.
  - lra.
Qed.

(** The real-number core: [w^2 = uh + ul], [root] within [2^-51] of [w]
    relatively, [rs + rse = root^2], and four roundings, each within [2^-53] of
    its result plus [eta]. *)
Lemma root_real (w root uh ul rs rse r1 r2 r3 c eta : R) :
  1 <= w <= 1073741824 -> w * w = uh + ul -> rs + rse = root * root ->
  Rabs (root - w) <= / 2251799813685248 * w ->
  0 < uh -> Rabs ul <= / 4503599627370496 * uh -> 0 < rs -> Rabs rse <= / 4503599627370496 * rs ->
  0 < eta <= 1e-30 ->
  Rabs (r1 - (uh - rs)) <= / 9007199254740992 * Rabs (uh - rs) + eta ->
  Rabs (r2 - (r1 - rse)) <= / 9007199254740992 * Rabs (r1 - rse) + eta ->
  Rabs (r3 - (r2 + ul)) <= / 9007199254740992 * Rabs (r2 + ul) + eta ->
  Rabs (c - r3 / (2 * root)) <= / 9007199254740992 * Rabs (r3 / (2 * root)) + eta ->
  Rabs (root + c - w) <= / 1237940039285380274899124224 * w.
Proof.
  intros [W1 W2] Hw Hr Hroot Huh Hul Hrs Hrse [Heta0 Heta1] H1 H2 H3 H4.
  assert (Hw2 : 1 <= w * w) by nra.
  assert (Hrho : / 2251799813685248 <= / 1000000) by (apply Rinv_le_contravar; lra).
  destruct (sq_near w root (/ 2251799813685248) W1 Hroot ltac:(lra) Hrho) as [HR [HP Hroot1]].
  apply Rabs_le_inv in HR.
  assert (Hk : 2.00001 * / 2251799813685248 * (w * w) <= 8.9e-16 * (w * w)) by (apply Rmult_le_compat_r; [lra | lra]).
  set (W := w * w) in *. set (P := root * root) in *.
  apply Rabs_le_inv in Hul. apply Rabs_le_inv in Hrse.
  assert (Huh1 : uh <= 1.0001 * W) by lra.
  assert (Hrs1 : rs <= 1.0001 * W) by lra.
  assert (Hul1 : Rabs ul <= 2.3e-16 * W).
  { apply Rabs_le. split; lra. }
  assert (Hrse1 : Rabs rse <= 2.3e-16 * W).
  { apply Rabs_le. split; lra. }
  apply Rabs_le_inv in Hul1. apply Rabs_le_inv in Hrse1.
  assert (Hd1 : Rabs (uh - rs) <= 2e-15 * W) by (apply Rabs_le; split; lra).
  assert (E1 : Rabs (r1 - (uh - rs)) <= 1.3e-30 * W).
  { pose proof (rnd_step _ _ _ _ H1 Hd1) as S. lra. }
  apply Rabs_le_inv in E1. apply Rabs_le_inv in Hd1.
  assert (Hr1r : Rabs (r1 - rse) <= 2.4e-15 * W) by (apply Rabs_le; split; lra).
  assert (E2 : Rabs (r2 - (r1 - rse)) <= 1.3e-30 * W).
  { pose proof (rnd_step _ _ _ _ H2 Hr1r) as S. lra. }
  apply Rabs_le_inv in E2. apply Rabs_le_inv in Hr1r.
  assert (Hr2u : Rabs (r2 + ul) <= 2.7e-15 * W) by (apply Rabs_le; split; lra).
  assert (E3 : Rabs (r3 - (r2 + ul)) <= 1.4e-30 * W).
  { pose proof (rnd_step _ _ _ _ H3 Hr2u) as S. lra. }
  apply Rabs_le_inv in E3.
  set (E := (r1 - (uh - rs)) + (r2 - (r1 - rse)) + (r3 - (r2 + ul))).
  assert (Hr3 : r3 = (W - P) + E) by (unfold E; lra).
  assert (HE : Rabs E <= 4e-30 * W) by (apply Rabs_le; unfold E; split; lra).
  assert (Hr3b : Rabs r3 <= 9e-16 * W) by (apply Rabs_le; apply Rabs_le_inv in HE; split; lra).
  pose proof (div_lem r3 w root 9e-16 ltac:(lra) Hroot1 ltac:(lra) Hr3b) as Hq.
  assert (E4 : Rabs (c - r3 / (2 * root)) <= 1.2e-30 * w).
  { pose proof (rnd_step _ _ _ _ H4 Hq) as S. lra. }
  assert (Hid : root + c - w = (root - w) * (root - w) / (2 * root) + E / (2 * root) + (c - r3 / (2 * root))).
  { rewrite Hr3. unfold W, P. field. lra. }
  rewrite Hid.
  assert (Q1 : Rabs ((root - w) * (root - w) / (2 * root)) <= 2e-31 * w).
  { apply div_lem; [lra | exact Hroot1 | lra | ].
    rewrite Rabs_mult.
    assert (Rabs (root - w) * Rabs (root - w) <= (/ 2251799813685248 * w) * (/ 2251799813685248 * w))
      by (apply Rmult_le_compat; try apply Rabs_pos; exact Hroot).
    nra. }
  assert (Q2 : Rabs (E / (2 * root)) <= 4e-30 * w) by (apply div_lem; [lra | exact Hroot1 | lra | exact HE]).
  apply Rle_trans with (Rabs ((root - w) * (root - w) / (2 * root)) + Rabs (E / (2 * root)) + Rabs (c - r3 / (2 * root))).
  { pose proof (Rabs_triang ((root - w) * (root - w) / (2 * root) + E / (2 * root)) (c - r3 / (2 * root))).
    pose proof (Rabs_triang ((root - w) * (root - w) / (2 * root)) (E / (2 * root))). lra. }
  lra.
Qed.
