(** Rounding of the high-correlation quadrature's nodes: a relative-error
    calculus over Flocq's binary64, and its application to the node term
    [hw * (w * (exp(-phi) / rs))] of the kernel (docs/bivariate_normal_high.md
    section 4).  Everything is real arithmetic; the float operations enter as
    [rnd] and as the two library contracts [expT] and [sqrtT]. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly.
Open Scope R_scope.

Definition u : R := bpow radix2 (-53).

Lemma u_value : u = 1 / 9007199254740992.
Proof.
  unfold u.
  assert (H : bpow radix2 53 * bpow radix2 (-53) = 1).
  { rewrite <- bpow_plus. replace (53 + -53)%Z with 0%Z by lia. reflexivity. }
  assert (H2 : bpow radix2 53 = 9007199254740992).
  { cbv [bpow]. cbn. unfold IZR. cbn. lra. }
  rewrite H2 in H. lra.
Qed.

Lemma u_pos : 0 < u. Proof. unfold u. apply bpow_gt_0. Qed.
Lemma u_small : u < 1112 / 10 ^ 19. Proof. rewrite u_value. lra. Qed.
Lemma u_c54 : c54 = u / 2.
Proof. unfold c54, u. replace (-53)%Z with (-54 + 1)%Z by lia. rewrite bpow_plus. cbv [bpow]. cbn. lra. Qed.

Lemma bpow_m1022 : bpow radix2 (-1022) <= / 10 ^ 300.
Proof.
  cbv [bpow]. cbn [radix2 radix_val Z.pow_pos].
  apply Rinv_le_contravar.
  - apply pow_lt; lra.
  - replace ((10:R) ^ 300) with (IZR (10 ^ 300)%Z) by (rewrite pow_IZR; reflexivity).
    apply IZR_le. vm_compute. discriminate.
Qed.

(** A float is [nrm] when it is zero or its magnitude is at least [1e-300]. *)
Definition nrm (x : R) : Prop := x = 0 \/ / 10 ^ 300 <= Rabs x.

(** One rounding, relative, above the subnormal range. *)
Lemma rnd_rel_big x : bpow radix2 (-1022) <= Rabs x -> Rabs (rnd x - x) <= u * Rabs x.
Proof.
  intros Hb.
  - assert (Hn : bpow radix2 (-1074 + 53 - 1) <= Rabs x).
    { replace (-1074 + 53 - 1)%Z with (-1022)%Z by lia. exact Hb. }
    pose proof (ulp_FLT_le radix2 (-1074) 53 x Hn) as Hu.
    destruct (Req_dec x 0) as [->|Hne].
    + rewrite rnd_0. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
    + pose proof (@error_le_half_ulp radix2 fexp fexp_valid (fun z => negb (Z.even z)) x) as He.
      change (Znearest (fun z => negb (Z.even z))) with ZnearestE in He.
      unfold rnd. unfold fexp in *.
      replace (bpow radix2 (1 - 53)) with (2 * u) in Hu.
      2: { unfold u. replace (1 - 53)%Z with (-52)%Z by lia. replace (-53)%Z with (-52 + -1)%Z by lia.
           rewrite bpow_plus. cbv [bpow]. cbn. lra. }
      nra.
Qed.

Lemma rnd_rel x : nrm x -> Rabs (rnd x - x) <= u * Rabs x.
Proof.
  intros [->|H].
  - rewrite rnd_0. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - apply rnd_rel_big. pose proof bpow_m1022. lra.
Qed.

Definition eta : R := bpow radix2 (-1075).

(** One rounding, anywhere: a relative part and the half least subnormal. *)
Lemma rnd_abs x : Rabs (rnd x - x) <= u * Rabs x + eta.
Proof.
  destruct (Rlt_le_dec (Rabs x) (bpow radix2 (-1022))) as [Hs|Hb].
  - pose proof (@error_le_half_ulp radix2 fexp fexp_valid (fun z => negb (Z.even z)) x) as He.
    change (Znearest (fun z => negb (Z.even z))) with ZnearestE in He.
    assert (Hs' : Rabs x < bpow radix2 (-1074 + 53)).
    { eapply Rlt_le_trans; [exact Hs|]. apply bpow_le. lia. }
    pose proof (@ulp_FLT_small radix2 (-1074) 53 prec53 x Hs') as Hu.
    unfold rnd. unfold fexp in *. rewrite Hu in He.
    assert (Hb2 : bpow radix2 (-1074) = 2 * eta).
    { unfold eta. replace (-1074)%Z with (-1075 + 1)%Z by lia. rewrite bpow_plus. cbv [bpow]. cbn. lra. }
    pose proof (Rabs_pos x). pose proof u_pos.
    assert (0 <= u * Rabs x) by nra. lra.
  - pose proof (rnd_rel_big x Hb). unfold eta. pose proof (bpow_gt_0 radix2 (-1075)). lra.
Qed.

(** Relative closeness: [y] approximates [x] within [th |x|]. *)
Definition rel (x y th : R) : Prop := Rabs (y - x) <= th * Rabs x.

Lemma rel_rnd x y th : nrm y -> 0 <= th -> rel x y th -> rel x (rnd y) (th + u + u * th).
Proof.
  intros Hn Hth H. unfold rel in *.
  pose proof (rnd_rel y Hn) as Hr.
  pose proof (Rabs_triang (rnd y - y) (y - x)) as Ht.
  replace (rnd y - y + (y - x)) with (rnd y - x) in Ht by ring.
  assert (Rabs y <= (1 + th) * Rabs x).
  { pose proof (Rabs_triang (y - x) x) as H2. replace (y - x + x) with y in H2 by ring. nra. }
  assert (Hu : u * Rabs y <= u * ((1 + th) * Rabs x)) by (apply Rmult_le_compat_l; [left; apply u_pos | assumption]).
  nra.
Qed.

Lemma rel_mul a a' b b' t1 t2 :
  0 <= t1 -> 0 <= t2 -> rel a a' t1 -> rel b b' t2 -> rel (a * b) (a' * b') (t1 + t2 + t1 * t2).
Proof.
  intros H1 H2 Ha Hb. unfold rel in *.
  replace (a' * b' - a * b) with ((a' - a) * b' + a * (b' - b)) by ring.
  pose proof (Rabs_triang ((a' - a) * b') (a * (b' - b))) as Ht.
  rewrite !Rabs_mult in Ht. rewrite Rabs_mult.
  assert (Hb' : Rabs b' <= (1 + t2) * Rabs b).
  { pose proof (Rabs_triang (b' - b) b) as H3. replace (b' - b + b) with b' in H3 by ring. nra. }
  pose proof (Rabs_pos a). pose proof (Rabs_pos b). pose proof (Rabs_pos (a' - a)). pose proof (Rabs_pos (b' - b)). pose proof (Rabs_pos b').
  nra.
Qed.

Lemma rel_inv b b' t : b <> 0 -> 0 <= t -> t < 1 -> rel b b' t -> rel (/ b) (/ b') (t / (1 - t)).
Proof.
  intros Hb Ht0 Ht1 H. unfold rel in *.
  set (A := Rabs b). set (B := Rabs b'). set (D := Rabs (b - b')).
  assert (HA : 0 < A) by (apply Rabs_pos_lt; exact Hb).
  assert (HD : D <= t * A) by (unfold D, A; rewrite Rabs_minus_sym; exact H).
  assert (HB : (1 - t) * A <= B).
  { pose proof (Rabs_triang_inv b b') as H1. rewrite Rabs_minus_sym in H. unfold A, B. nra. }
  assert (HB0 : 0 < B) by nra.
  assert (Hb'0 : b' <> 0).
  { intro H0. unfold B in HB0. rewrite H0, Rabs_R0 in HB0. lra. }
  replace (/ b' - / b) with ((b - b') * / b * / b') by (field; split; assumption).
  rewrite !Rabs_mult, !Rabs_Rinv by assumption.
  fold A B D.
  assert (E : t / (1 - t) * / A - D * / A * / B = (t * B - D * (1 - t)) / ((1 - t) * A * B)).
  { field. repeat split; intro Hz; nra. }
  assert (Hn : 0 <= (t * B - D * (1 - t)) / ((1 - t) * A * B)).
  { unfold Rdiv. apply Rmult_le_pos.
    - pose proof (Rmult_le_compat_l t _ _ Ht0 HB). pose proof (Rmult_le_compat_r (1 - t) _ _ ltac:(lra) HD). nra.
    - left. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | exact HB0]. }
  lra.
Qed.

Lemma rel_div a a' b b' t1 t2 :
  b <> 0 -> 0 <= t1 -> 0 <= t2 -> t2 < 1 -> rel a a' t1 -> rel b b' t2 ->
  rel (a / b) (a' / b') ((t1 + t2) / (1 - t2)).
Proof.
  intros Hb H1 H2 H3 Ha Hb'.
  pose proof (rel_inv b b' t2 Hb H2 H3 Hb') as Hi.
  pose proof (rel_mul a a' (/ b) (/ b') t1 (t2 / (1 - t2)) H1 ltac:(apply Rmult_le_pos; [exact H2 | left; apply Rinv_0_lt_compat; lra]) Ha Hi) as Hm.
  unfold Rdiv in *.
  replace ((t1 + t2) * / (1 - t2)) with (t1 + t2 * / (1 - t2) + t1 * (t2 * / (1 - t2))); [exact Hm|].
  field. lra.
Qed.
