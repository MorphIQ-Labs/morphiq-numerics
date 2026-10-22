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
