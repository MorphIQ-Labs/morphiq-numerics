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
From Flocq Require Import Core Relative.
Open Scope R_scope.

Notation rndF := (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n)))).

Definition u : R := bpow radix2 (-53).
Definition z : R := bpow radix2 (-1075).

Lemma u_val : u = / 9007199254740992.
Proof. unfold u. reflexivity. Qed.

Lemma u_pos : 0 < u.
Proof. unfold u. apply bpow_gt_0. Qed.

Lemma z_pos : 0 < z.
Proof. unfold z. apply bpow_gt_0. Qed.

Lemma rnd_opp x : rndF (- x) = - rndF x.
Proof.
  apply round_N_opp. auto with typeclass_instances.
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
      - subst x. rewrite ulp_FLT_0 by lia. apply Rle_refl.
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
      - subst x. rewrite ulp_FLT_0 by lia. apply bpow_le. lia.
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
