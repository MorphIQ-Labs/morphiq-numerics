(** The rounding facts the bivariate budget uses, for binary64 round to
    nearest even (Flocq's FLT model with radix 2, precision 53 and minimum
    exponent -1074, the same [rndF] as formal/binary64):

    - [rnd_rel_z]: relative error at most [2^-53], plus the half-unit of the
      least subnormal ([2^-1075]) where the result is subnormal;
    - [rnd_pow]: below [2^k] the error is at most [2^(k-54)], which is half
      the spacing of the top binade and so sharper than the relative bound
      for a value just above [2^(k-1)];
    - [rnd_opp]: rounding is odd. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core Relative Plus_error.
Open Scope R_scope.

Notation rndF := (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n)))).

#[export] Instance prec53_gt_0 : Prec_gt_0 53.
Proof. unfold Prec_gt_0. lia. Qed.

Definition u : R := bpow radix2 (-53).
Definition z : R := bpow radix2 (-1075).

Lemma u_val : u = / 9007199254740992.
Proof. unfold u. reflexivity. Qed.

Lemma Rabs_sq x : Rabs x * Rabs x = x * x.
Proof.
  rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma Rabs_le_between x y : Rabs x <= y <-> -y <= x <= y.
Proof.
  split; [apply Rabs_le_inv | apply Rabs_le].
Qed.

Lemma Rabs_div_pos T D : 0 < D -> Rabs (T / D) = Rabs T / D.
Proof.
  intros H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq D) by lra. reflexivity.
Qed.

Lemma Rabs_lt_between x y : Rabs x < y <-> -y < x < y.
Proof.
  split; intros H.
  - destruct (Rabs_def2 x y H) as [H1 H2]. lra.
  - apply Rabs_def1; lra.
Qed.

Lemma exp_mono a b : a <= b -> exp a <= exp b.
Proof.
  intros H. destruct H as [H | H]; [left; apply exp_increasing; exact H | right; rewrite H; reflexivity].
Qed.

Lemma u_pos : 0 < u.
Proof. unfold u. apply bpow_gt_0. Qed.

Lemma z_pos : 0 < z.
Proof. unfold z. apply bpow_gt_0. Qed.

Lemma rnd_opp x : rndF (- x) = - rndF x.
Proof.
  apply round_NE_opp.
Qed.

Lemma rnd_rel_z x : Rabs (rndF x - x) <= u * Rabs x + z.
Proof.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs x)) as [H | H].
  - pose proof (relative_error_N_FLT radix2 (-1074) 53 ltac:(lia) (fun n => negb (Z.even n)) x) as R.
    replace (-1074 + 53 - 1)%Z with (-1022)%Z in R by reflexivity. specialize (R H).
    assert (E : / 2 * bpow radix2 (- (53) + 1) = u).
    { unfold u. replace (- (53) + 1)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. field. }
    rewrite E in R. pose proof z_pos. lra.
  - pose proof (error_le_half_ulp radix2 (FLT_exp (-1074) 53) (fun n => negb (Z.even n)) x) as E.
    assert (Hu : ulp radix2 (FLT_exp (-1074) 53) x <= bpow radix2 (-1074)).
    { destruct (Req_dec x 0) as [H0 | H0].
      - subst x. rewrite ulp_FLT_0; [apply Rle_refl | apply prec53_gt_0].
      - rewrite ulp_neq_0 by exact H0. unfold cexp. apply bpow_le.
        assert (mag radix2 x <= -1022)%Z.
        { apply mag_le_bpow; assumption. }
        unfold FLT_exp. apply Z.max_lub; lia. }
    assert (Ez : / 2 * bpow radix2 (-1074) = z).
    { unfold z. replace (-1074)%Z with (-1075 + 1)%Z by reflexivity. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. field. }
    pose proof (Rabs_pos x). pose proof u_pos.
    assert (0 <= u * Rabs x) by (apply Rmult_le_pos; lra).
    lra.
Qed.

(** Below [2^k] (with [k] at least [-1021]) the error is at most [2^(k-54)]. *)
Lemma rnd_pow k x : (-1021 <= k)%Z -> Rabs x <= bpow radix2 k ->
  Rabs (rndF x - x) <= bpow radix2 (k - 54).
Proof.
  intros Hk Hx.
  destruct (Rle_lt_or_eq_dec _ _ Hx) as [Hl | Heq].
  - pose proof (error_le_half_ulp radix2 (FLT_exp (-1074) 53) (fun n => negb (Z.even n)) x) as E.
    assert (Hu : ulp radix2 (FLT_exp (-1074) 53) x <= bpow radix2 (k - 53)).
    { destruct (Req_dec x 0) as [H0 | H0].
      - subst x. rewrite ulp_FLT_0; [apply bpow_le; lia | apply prec53_gt_0].
      - rewrite ulp_neq_0 by exact H0. unfold cexp. apply bpow_le.
        assert (mag radix2 x <= k)%Z by (apply mag_le_bpow; assumption).
        unfold FLT_exp. apply Z.max_lub; lia. }
    assert (Ez : / 2 * bpow radix2 (k - 53) = bpow radix2 (k - 54)).
    { replace (k - 53)%Z with ((k - 54) + 1)%Z by lia. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. field. }
    lra.
  - assert (Hf : generic_format radix2 (FLT_exp (-1074) 53) (Rabs x)).
    { rewrite Heq. apply generic_format_bpow. unfold FLT_exp. apply Z.max_lub; lia. }
    assert (Hx2 : generic_format radix2 (FLT_exp (-1074) 53) x).
    { destruct (Rcase_abs x) as [Hn | Hp].
      - rewrite (Rabs_left _ Hn) in Hf. replace x with (- - x) by ring.
        apply generic_format_opp. exact Hf.
      - rewrite (Rabs_right _ Hp) in Hf. exact Hf. }
    rewrite round_generic by (auto with typeclass_instances || exact Hx2).
    replace (x - x) with 0 by ring. rewrite Rabs_R0. left. apply bpow_gt_0.
Qed.

Notation fmtF := (generic_format radix2 (FLT_exp (-1074) 53)).

Lemma fmtF_rnd x : fmtF (rndF x).
Proof. apply generic_format_round; auto with typeclass_instances. Qed.

(** Away from underflow rounding is a relative perturbation. *)
Lemma rnd_delta x : x = 0 \/ bpow radix2 (-1022) <= Rabs x ->
  exists d, Rabs d <= u /\ rndF x = x * (1 + d).
Proof.
  intros [H | H].
  - subst x. exists 0. split; [rewrite Rabs_R0; apply Rlt_le, u_pos |].
    rewrite round_0 by auto with typeclass_instances. ring.
  - pose proof (relative_error_N_FLT_ex radix2 (-1074) 53 ltac:(lia) (fun n => negb (Z.even n)) x) as R.
    replace (-1074 + 53 - 1)%Z with (-1022)%Z in R by reflexivity. specialize (R H).
    destruct R as [e [He Hr]]. exists e. split; [| exact Hr].
    assert (E : / 2 * bpow radix2 (- (53) + 1) = u).
    { unfold u. replace (- (53) + 1)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. field. }
    rewrite E in He. exact He.
Qed.

(** The difference of two binary64 numbers rounds with a relative error, or
    exactly when it is subnormal. *)
Lemma rnd_sub_delta a b : fmtF a -> fmtF b ->
  exists d, Rabs d <= u /\ rndF (a - b) = (a - b) * (1 + d).
Proof.
  intros Fa Fb.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (a - b))) as [H | H].
  - apply rnd_delta. right. exact H.
  - exists 0. split; [rewrite Rabs_R0; apply Rlt_le, u_pos |].
    assert (Fs : fmtF (a - b)).
    { unfold Rminus.
      assert (Fb' : fmtF (- b)) by (apply generic_format_opp; exact Fb).
      assert (Hs : Rabs (a + - b) <= bpow radix2 (53 + -1074)).
      { unfold Rminus in H. left. eapply Rlt_le_trans; [exact H |]. apply bpow_le. lia. }
      exact (FLT_format_plus_small radix2 (-1074) 53 a (- b) Fa Fb' Hs). }
    rewrite round_generic by (auto with typeclass_instances || exact Fs). ring.
Qed.

(** Halving a normal binary64 number is exact. *)
Lemma rnd_half w : fmtF w -> bpow radix2 (-1021) <= Rabs w -> rndF (w / 2) = w / 2.
Proof.
  intros Fw Hw.
  pose proof (FLT_format_generic radix2 (-1074) 53 w Fw) as Fw'.
  destruct Fw' as [[m e] E1 E2 E3]. simpl in E1, E2, E3.
  assert (He : (-1073 <= e)%Z).
  { destruct (Z_le_dec (-1073) e) as [H | H]; [exact H |].
    assert (e = -1074)%Z by lia. subst e. exfalso.
    assert (Hm : Rabs (IZR m) < bpow radix2 53).
    { rewrite <- abs_IZR. change (bpow radix2 53) with (IZR (Zpower radix2 53)).
      apply IZR_lt. exact E2. }
    assert (Hw2 : Rabs w < bpow radix2 (-1021)).
    { rewrite E1. unfold F2R; cbn [Fnum Fexp]. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-1074))) by (apply Rlt_le, bpow_gt_0).
      replace (-1021)%Z with (53 + -1074)%Z by reflexivity. rewrite bpow_plus.
      apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hm]. }
    lra. }
  apply round_generic; [auto with typeclass_instances |].
  apply generic_format_FLT. exists (Float radix2 m (e - 1)).
  - rewrite E1. unfold F2R; cbn [Fnum Fexp]. replace (e - 1)%Z with (e + -1)%Z by lia. rewrite bpow_plus.
    change (bpow radix2 (-1)) with (/ 2). field.
  - simpl. exact E2.
  - simpl. lia.
Qed.

(** The sum of two binary64 numbers rounds with a relative error, or exactly
    when it is subnormal. *)
Lemma rnd_add_delta a b : fmtF a -> fmtF b ->
  exists d, Rabs d <= u /\ rndF (a + b) = (a + b) * (1 + d).
Proof.
  intros Fa Fb.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (a + b))) as [H | H].
  - apply rnd_delta. right. exact H.
  - exists 0. split; [rewrite Rabs_R0; apply Rlt_le, u_pos |].
    assert (Hs : Rabs (a + b) <= bpow radix2 (53 + -1074)).
    { left. eapply Rlt_le_trans; [exact H |]. apply bpow_le. lia. }
    assert (Fs : fmtF (a + b)) by exact (FLT_format_plus_small radix2 (-1074) 53 a b Fa Fb Hs).
    rewrite round_generic by (auto with typeclass_instances || exact Fs). ring.
Qed.

Lemma rnd_nonneg x : 0 <= x -> 0 <= rndF x.
Proof.
  intros H. apply round_ge_generic; [auto with typeclass_instances | auto with typeclass_instances | |  exact H].
  apply generic_format_0.
Qed.
