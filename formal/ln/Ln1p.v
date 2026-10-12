(** [ln_1p]'s fast path returns today's bits (docs/ln.md, section 9). Stage H
    and stage B, when their tests pass, return [v = RN(ln(1 + x))] and every
    real within [2^-123] of [ln(1 + x)] relatively rounds to [v]
    ([stage_h_ok], [stage_b_ok]). [ln_1p]'s accurate value is such a real and
    its accurate path rounds it once (LnAccurate.v, [ln_1p_acc_ok]); so that
    path returns [v] too, bit for bit. Today's double-word path, when its own
    test passes, returns [RN(ln(1 + x))] by its contract, which is [v]: every
    path [ln_1p] took before returns the bits the stages return.
    [ln_1p_stages] runs the screens (Ln1pScreen.v) and the stages as [ln_1p]
    runs them, and [ln_1p_stages_ok] states this for whatever it returns. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
From Q Require QSpec Q128.
Require LnAccurate.
Require Import Ln1pLemmas Ln1pApprox Ln1pScreen Ln1pStageH Ln1pStageB.

Open Scope R_scope.

(** [ln(1 + x)] keeps away from zero: at least [2^-55] for [|x| >= 2^-54]. *)
Lemma ln1p_away x : -1 < x -> bpow radix2 (-54) <= Rabs x -> bpow radix2 (-55) <= Rabs (ln (1 + x)).
Proof.
  intros H1 H2.
  assert (P54 : bpow radix2 (-55) = / 2 * bpow radix2 (-54)) by (change (/ 2) with (bpow radix2 (-1)); rewrite <- bpow_plus; reflexivity).
  pose proof (bpow_gt_0 radix2 (-54)) as P.
  destruct (Rle_lt_dec (Rabs x) (/ 4)) as [S | L].
  - pose proof (ln1p_linear x ltac:(lra)) as T. set (a := Rabs x) in *.
    assert (Xa : x * x = a * a) by (unfold a; rewrite <- Rabs_mult, Rabs_pos_eq by apply Rle_0_sqr; reflexivity).
    assert (I : / (1 - a) <= 4 / 3) by (replace (4 / 3) with (/ (3 / 4)) by field; apply Rinv_le_contravar; lra).
    assert (A0 : 0 <= a) by apply Rabs_pos.
    assert (Q : x * x / (1 - a) <= a / 3).
    { unfold Rdiv. rewrite Xa. apply Rle_trans with (a * a * (4 / 3)); [apply Rmult_le_compat_l; [nra | exact I] | nra]. }
    pose proof (Rabs_triang_inv x (x - ln (1 + x))) as R. replace (x - (x - ln (1 + x))) with (ln (1 + x)) in R by ring.
    rewrite Rabs_minus_sym in R. fold a in R. lra.
  - destruct (Rlt_le_dec 0 x) as [Xp | Xn].
    + rewrite Rabs_pos_eq in L by lra.
      assert (ln (5 / 4) < ln (1 + x)) by (apply ln_increasing; lra).
      assert (/ 5 <= ln (5 / 4)) by interval with (i_prec 64).
      rewrite Rabs_pos_eq by lra. assert (bpow radix2 (-55) <= / 5) by (simpl; lra). lra.
    + rewrite Rabs_left1 in L by lra.
      assert (ln (1 + x) < ln (3 / 4)) by (apply ln_increasing; lra).
      assert (ln (3 / 4) <= - / 4) by interval with (i_prec 64).
      rewrite Rabs_left1 by lra. assert (bpow radix2 (-55) <= / 4) by (simpl; lra). lra.
Qed.

Lemma strict_of_nonzero (v : f64) : B v <> 0 -> is_finite_strict 53 1024 v = true.
Proof. intros H. destruct v; try reflexivity; exfalso; apply H; reflexivity. Qed.

(** Equal nonzero values from the stage and from the accurate path. *)
Lemma same_bits x v : finite x -> -1 < B x -> bpow radix2 (-54) <= Rabs (B x) ->
  B v = rndF (ln (1 + B x)) ->
  (forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) -> rndF w = B v) ->
  v = Q128.to_f64 (LnAccurate.ln_1p_acc x).
Proof.
  intros Fx H1 H2 Bv All.
  destruct (LnAccurate.ln_1p_acc_ok x Fx H1 H2) as [_ [Acc Rnd]].
  assert (Eq : B (Q128.to_f64 (LnAccurate.ln_1p_acc x)) = B v) by (rewrite Rnd; apply All; exact Acc).
  assert (Nz : B v <> 0).
  { rewrite Bv. intros Z0. pose proof (ln1p_away (B x) H1 H2) as A.
    assert (bpow radix2 (-55) <= Rabs (rndF (ln (1 + B x))))
      by (apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-55)); lia | exact A]).
    rewrite Z0, Rabs_R0 in H. pose proof (bpow_gt_0 radix2 (-55)). lra. }
  apply B2R_inj; [apply strict_of_nonzero, Nz | apply strict_of_nonzero; rewrite Eq; exact Nz | symmetry; exact Eq].
Qed.

(** Stage H returns [RN(ln(1 + x))], which is what [ln_1p]'s accurate path returns. *)
Theorem ln_1p_stage_h_bits x v : finite x -> bpow radix2 (-46) <= Rabs (B x) -> -1 < B x < bpow radix2 53 ->
  stage_h x = Some v ->
  B v = rndF (ln (1 + B x)) /\ v = Q128.to_f64 (LnAccurate.ln_1p_acc x).
Proof.
  intros Fx Hx Hr Hd. destruct (stage_h_ok x v Fx Hx Hr Hd) as [_ [Bv All]].
  split; [exact Bv | apply (same_bits x v Fx (proj1 Hr)); [ | exact Bv | exact All]].
  apply Rle_trans with (2 := Hx). apply bpow_le. lia.
Qed.

(** Stage B returns [RN(ln(1 + x))], which is what [ln_1p]'s accurate path returns. *)
Theorem ln_1p_stage_b_bits x v : finite x -> bpow radix2 (-54) <= Rabs (B x) -> -1 < B x < bpow radix2 1020 ->
  stage_b x = Some v ->
  B v = rndF (ln (1 + B x)) /\ v = Q128.to_f64 (LnAccurate.ln_1p_acc x).
Proof.
  intros Fx Hx Hr Hd. destruct (stage_b_ok x v Fx Hx Hr Hd) as [_ [Bv All]].
  split; [exact Bv | exact (same_bits x v Fx (proj1 Hr) Hx Bv All)].
Qed.

(** [ln_1p]'s stages as [ln_1p] runs them (ln/mod.rs): stage H behind its
    screen, then stage B behind its own; [None] sends [x] to
    [ln_1p_reference]. *)
Definition ln_1p_stages (x : f64) : option f64 :=
  match (if h_screen x then stage_h x else None) with
  | Some v => Some v
  | None => if b_screen x then stage_b x else None
  end.

(** Whatever the stages return is [RN(ln(1 + x))] and the bits of [ln_1p]'s
    accurate path, for every [x]. *)
Theorem ln_1p_stages_ok x v : ln_1p_stages x = Some v ->
  finite x /\ B v = rndF (ln (1 + B x)) /\ v = Q128.to_f64 (LnAccurate.ln_1p_acc x).
Proof.
  unfold ln_1p_stages. intros H.
  assert (Bpart : (if b_screen x then stage_b x else None) = Some v ->
                  finite x /\ B v = rndF (ln (1 + B x)) /\ v = Q128.to_f64 (LnAccurate.ln_1p_acc x)).
  { intros Hb. destruct (b_screen x) eqn:Sb; [ | discriminate].
    destruct (b_screen_ok x Sb) as [Fx [Hx Hr]].
    destruct (ln_1p_stage_b_bits x v Fx Hx Hr Hb) as [B1 B2]. auto. }
  destruct (h_screen x) eqn:Sh; [ | exact (Bpart H)].
  destruct (stage_h x) as [w | ] eqn:Hh; [ | exact (Bpart H)].
  injection H as E. subst w.
  destruct (h_screen_ok x Sh) as [Fx [Hx Hr]].
  destruct (ln_1p_stage_h_bits x v Fx Hx Hr Hh) as [B1 B2]. auto.
Qed.
