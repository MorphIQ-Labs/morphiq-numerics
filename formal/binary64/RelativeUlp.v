(** Relative approximation followed by nearest-even binary64 rounding.
    The ULP is measured at the exact result, including a crossed binade. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps.
Open Scope R_scope.

Lemma relative_ulp_positive_normal eps v w : 0<=eps<bpow radix2 (-54) ->
  bpow radix2 (-1022) <= v ->
  Rabs (w - v) <= eps * v ->
  Rabs (rndF w - v) <= (/ 2 + eps*bpow radix2 53) * ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros Pe V E.
  assert (Pv : 0 < v) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  assert (We : - (eps * v) <= w - v <= eps * v) by (apply Rabs_le_inv; exact E).
  assert (Pw : 0 < w) by (assert (eps < 1) by (assert (bpow radix2 (-54)<1) by (change 1 with (bpow radix2 0); apply bpow_lt; lia); lra); nra).
  set (e := mag radix2 v).
  assert (Ge : (-1021 <= e)%Z).
  { unfold e. apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. exact V. }
  assert (Top : v < bpow radix2 e).
  { unfold e. pose proof (bpow_mag_gt radix2 v); rewrite Rabs_pos_eq in H by lra; exact H. }
  assert (U : ulp radix2 (FLT_exp emin prec) v = bpow radix2 (e - 53)).
  { rewrite ulp_neq_0 by lra. unfold cexp, FLT_exp, emin, prec. fold e.
    rewrite Z.max_l by lia. reflexivity. }
  assert (Budget : eps * v <= eps*bpow radix2 53 * bpow radix2 (e - 53)).
  { apply Rle_trans with ((eps) * bpow radix2 e).
    - apply Rmult_le_compat_l; lra.
    - right. rewrite Rmult_assoc,<-bpow_plus.
      f_equal; f_equal; lia. }
  rewrite U.
  destruct (Rlt_le_dec w (bpow radix2 e)) as [Inside | Across].
  - assert (Mw : (mag radix2 w <= e)%Z).
    { apply mag_le_bpow; [lra | rewrite Rabs_pos_eq by lra; exact Inside]. }
    assert (Uw : ulp radix2 (FLT_exp emin prec) w <= bpow radix2 (e - 53)).
    { rewrite ulp_neq_0 by lra. apply bpow_le. unfold cexp, FLT_exp, emin, prec. lia. }
    pose proof (@error_le_half_ulp radix2 (FLT_exp emin prec) ltac:(exact _) ne w) as Round.
    change (Rabs (rndF w - w) <= / 2 * ulp radix2 (FLT_exp emin prec) w) in Round.
    replace (rndF w - v) with ((rndF w - w) + (w - v)) by ring.
    eapply Rle_trans; [apply Rabs_triang | nra].
  - assert (Rounded : rndF w = bpow radix2 e).
    { apply round_relative_close; [apply generic_format_bpow; unfold FLT_exp,emin,prec; lia | apply Rgt_not_eq, bpow_gt_0 | ].
      rewrite Rabs_pos_eq by lra.
      rewrite (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
      apply Rle_lt_trans with ((eps) * v); [lra | ].
      assert (0 < bpow radix2 e) by apply bpow_gt_0.
      unfold Rdiv. replace (/2^54) with (bpow radix2 (-54)) by (rewrite pow_IZR; reflexivity).
      nra. }
    rewrite Rounded, Rabs_pos_eq by lra.
    pose proof (bpow_gt_0 radix2 (e - 53)). nra.
Qed.


Lemma relative_ulp_small z : 0<z<bpow radix2 (-1021) ->
  ulp radix2 (FLT_exp emin prec) z=bpow radix2 (-1074).
Proof.
  intro Z. rewrite ulp_neq_0 by lra. unfold cexp,FLT_exp,emin,prec.
  assert ((mag radix2 z<= -1021)%Z).
  { apply mag_le_bpow; [lra|rewrite Rabs_pos_eq by lra; lra]. }
  rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma relative_ulp_positive eps v w : 0<=eps<bpow radix2 (-54) -> 0<v ->
  Rabs(w-v)<=eps*v ->
  Rabs(rndF w-v)<=(/2+eps*bpow radix2 53)*ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros Pe Pv E. destruct (Rle_lt_dec (bpow radix2 (-1022)) v) as [Normal|Small].
  - apply relative_ulp_positive_normal; assumption.
  - assert (Pe1:eps<1).
    { assert (bpow radix2 (-54)<1) by (change 1 with (bpow radix2 0); apply bpow_lt; lia). lra. }
    assert (Twice:2*bpow radix2 (-1022)=bpow radix2 (-1021)).
    { change 2 with (bpow radix2 1). rewrite <-bpow_plus; reflexivity. }
    pose proof (Rabs_le_inv _ _ E) as Bounds.
    assert (Pw:0<w) by nra.
    assert (W:w<bpow radix2 (-1021)) by (rewrite <-Twice; nra).
    assert (V:v<bpow radix2 (-1021)) by (rewrite <-Twice; nra).
    rewrite (relative_ulp_small v ltac:(lra)).
    pose proof (@error_le_half_ulp radix2 (FLT_exp emin prec) ltac:(exact _) ne w) as Round.
    change (Rabs(rndF w-w)<=/2*ulp radix2 (FLT_exp emin prec) w) in Round.
    rewrite (relative_ulp_small w ltac:(lra)) in Round.
    assert (Budget:eps*v<=eps*bpow radix2 53*bpow radix2 (-1074)).
    { rewrite Rmult_assoc,<-bpow_plus. change (53 + -1074)%Z with (-1021)%Z.
      apply Rmult_le_compat_l; lra. }
    replace (rndF w-v) with ((rndF w-w)+(w-v)) by ring.
    eapply Rle_trans; [apply Rabs_triang|nra].
Qed.

Theorem relative_ulp_error eps v w : 0<=eps<bpow radix2 (-54) ->
  Rabs(w-v)<=eps*Rabs v ->
  Rabs(rndF w-v)<=(/2+eps*bpow radix2 53)*ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros Pe E. destruct (Rtotal_order 0 v) as [Pos|[Zero|Neg]].
  - rewrite (Rabs_pos_eq v) in E by lra. apply relative_ulp_positive; assumption.
  - subst v. rewrite Rabs_R0,Rmult_0_r,Rminus_0_r in E.
    assert (W:w=0) by (apply Rabs_le_inv in E; lra). subst w.
    rewrite round_0,Rminus_0_r,Rabs_R0 by exact _.
    apply Rmult_le_pos; [pose proof (bpow_gt_0 radix2 53); nra|apply ulp_ge_0].
  - rewrite (Rabs_left v) in E by exact Neg.
    assert (Opp:Rabs(-w- -v)<=eps*(-v)).
    { replace (-w- -v) with (-(w-v)) by ring. rewrite Rabs_Ropp; exact E. }
    pose proof (relative_ulp_positive eps (-v) (-w) Pe ltac:(lra) Opp) as Bound.
    unfold ne in Bound. rewrite round_NE_opp in Bound.
    replace (-round radix2 (FLT_exp emin prec) ZnearestE w- -v)
      with (-(round radix2 (FLT_exp emin prec) ZnearestE w-v)) in Bound by ring.
    rewrite Rabs_Ropp,ulp_opp in Bound. exact Bound.
Qed.
