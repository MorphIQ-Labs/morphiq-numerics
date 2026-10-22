(** The exact Newton step for [sinh y = x]: from [y] within [delta] of the root,
    [y + (x - sinh y)/cosh y] is within [4 delta^2] of it. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import AsinhWithin AsinhRoot AsinhExpRed.
Open Scope R_scope.

Lemma rabs_sub_r a b : Rabs a <= Rabs (a - b) + Rabs b.
Proof. apply Rle_trans with (Rabs ((a - b) + b)); [right; f_equal; ring | apply Rabs_triang]. Qed.

(** [0 <= exp u - 1 - u <= 2 u^2] for [|u| <= 1/2]. *)
Lemma exp_second u : Rabs u <= / 2 -> 0 <= exp u - 1 - u <= 2 * (u * u).
Proof.
  intros H. apply Rabs_le_inv in H. destruct H as [H1 H2].
  pose proof (exp_pos u) as P.
  assert (L : 1 + u <= exp u).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite exp_0; lra | pose proof (exp_ineq1 u N); lra]. }
  assert (L' : 1 + - u <= exp (- u)).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite Ropp_0, exp_0; lra | pose proof (exp_ineq1 (- u) ltac:(lra)); lra]. }
  assert (E : exp u = / exp (- u)) by (rewrite exp_Ropp, Rinv_involutive; [reflexivity | apply Rgt_not_eq, P]).
  assert (U : exp u <= / (1 - u)) by (rewrite E; apply Rinv_le_contravar; lra).
  assert (U2 : / (1 - u) <= 1 + u + 2 * (u * u)).
  { apply (Rmult_le_reg_l (1 - u)); [lra | ]. rewrite Rinv_r by lra. nra. }
  split; lra.
Qed.

Lemma sinh_plus_form y d : sinh (y + d) = sinh y * cosh d + cosh y * sinh d.
Proof.
  unfold sinh, cosh.
  assert (Hy : exp y <> 0) by (apply Rgt_not_eq, exp_pos).
  assert (Hd : exp d <> 0) by (apply Rgt_not_eq, exp_pos).
  assert (E1 : exp (y + d) = exp y * exp d) by apply exp_plus.
  assert (E2 : exp (- (y + d)) = / exp y * / exp d).
  { replace (- (y + d)) with (- y + - d) by ring. rewrite exp_plus, exp_Ropp, exp_Ropp. reflexivity. }
  assert (E3 : exp (- y) = / exp y) by apply exp_Ropp.
  assert (E4 : exp (- d) = / exp d) by apply exp_Ropp.
  rewrite E1, E2, E3, E4. field. split; assumption.
Qed.

Lemma cosh_pos y : 1 <= cosh y.
Proof.
  unfold cosh. pose proof (exp_pos y). 
  assert (E : exp (- y) = / exp y) by apply exp_Ropp.
  assert (Hp : exp y * exp (- y) = 1) by (rewrite E; field; apply Rgt_not_eq; assumption).
  pose proof (exp_pos (- y)). pose proof (pow2_ge_0 (exp y - exp (- y))). nra.
Qed.

Lemma sinh_le_cosh y : Rabs (sinh y) <= cosh y.
Proof.
  unfold sinh, cosh. pose proof (exp_pos y). pose proof (exp_pos (- y)).
  apply Rabs_le. split; lra.
Qed.

(** The exact correction is [sinh d + tanh y (cosh d - 1)]. *)
Lemma newton_exact y d : Rabs d <= / 50 ->
  Rabs ((sinh (y + d) - sinh y) / cosh y - d) <= 4 * (d * d) /\ Rabs ((sinh (y + d) - sinh y) / cosh y) <= 1.1 * Rabs d.
Proof.
  intros Hd.
  assert (Hc : 1 <= cosh y) by apply cosh_pos.
  assert (Hdh : Rabs d <= / 2) by lra.
  assert (E : (sinh (y + d) - sinh y) / cosh y = sinh d + (sinh y / cosh y) * (cosh d - 1)).
  { rewrite sinh_plus_form. field. lra. }
  pose proof (exp_second d Hdh) as [A1 A2].
  assert (Hdn : Rabs (- d) <= / 2) by (rewrite Rabs_Ropp; exact Hdh).
  pose proof (exp_second (- d) Hdn) as [B1 B2].
  assert (Hs : sinh d - d = ((exp d - 1 - d) - (exp (- d) - 1 - - d)) / 2) by (unfold sinh; lra).
  assert (Hch : cosh d - 1 = ((exp d - 1 - d) + (exp (- d) - 1 - - d)) / 2) by (unfold cosh; lra).
  assert (Hch0 : 0 <= cosh d - 1 <= 2 * (d * d)) by (split; nra).
  assert (Hsd : Rabs (sinh d - d) <= 2 * (d * d)) by (apply Rabs_le; split; nra).
  assert (Hq : Rabs (sinh y / cosh y) <= 1).
  { rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq (cosh y)) by lra.
    apply Rmult_le_reg_r with (cosh y); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
    pose proof (sinh_le_cosh y). lra. }
  assert (Ht : Rabs ((sinh y / cosh y) * (cosh d - 1)) <= 2 * (d * d)).
  { rewrite Rabs_mult, (Rabs_pos_eq (cosh d - 1)) by lra.
    apply Rle_trans with (1 * (cosh d - 1)); [apply Rmult_le_compat_r; lra | lra]. }
  split.
  - rewrite E. replace (sinh d + sinh y / cosh y * (cosh d - 1) - d) with ((sinh d - d) + sinh y / cosh y * (cosh d - 1)) by ring.
    apply Rle_trans with (Rabs (sinh d - d) + Rabs (sinh y / cosh y * (cosh d - 1))); [apply Rabs_triang | lra].
  - rewrite E. apply Rle_trans with (Rabs (sinh d) + Rabs (sinh y / cosh y * (cosh d - 1))); [apply Rabs_triang | ].
    assert (Hsa : Rabs (sinh d) <= Rabs d + 2 * (d * d)).
    { pose proof (rabs_sub_r (sinh d) d). lra. }
    assert (Hdd : d * d <= / 50 * Rabs d).
    { assert (Hsq : d * d = Rabs d * Rabs d) by (rewrite <- Rabs_mult; symmetry; apply Rabs_pos_eq; nra).
      rewrite Hsq. apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
    lra.
Qed.
