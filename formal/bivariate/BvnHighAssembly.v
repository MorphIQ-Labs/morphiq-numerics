(** The binary64 rounding model of the high-correlation branch (Flocq [FLT(-1074, 53)],
    nearest-even), the clamp to [[0, 1]], and the rounding lemmas the branch's proofs
    share (docs/bivariate_normal_high.md section 4). *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Flocq Require Import Core Sterbenz.
Open Scope R_scope.

Definition fexp : Z -> Z := FLT_exp (-1074) 53.
Definition rnd (x : R) : R := round radix2 fexp ZnearestE x.
Definition clamp (y : R) : R := Rmax 0 (Rmin 1 y).
Definition c54 : R := bpow radix2 (-54).

Lemma prec53 : Prec_gt_0 53. Proof. unfold Prec_gt_0. lia. Qed.
Lemma fexp_valid : Valid_exp fexp. Proof. apply FLT_exp_valid. exact prec53. Qed.
Lemma fexp_mono : Monotone_exp fexp. Proof. apply FLT_exp_monotone. Qed.

Lemma c54_pos : 0 < c54. Proof. apply bpow_gt_0. Qed.

Lemma c54_double : bpow radix2 (-53) = 2 * c54.
Proof.
  unfold c54. replace (-53)%Z with (-54 + 1)%Z by lia.
  rewrite bpow_plus. simpl. lra.
Qed.

Lemma c54_half : bpow radix2 (-55) = c54 / 2.
Proof.
  unfold c54. replace (-54)%Z with (-55 + 1)%Z by lia.
  rewrite bpow_plus. simpl. lra.
Qed.

Lemma rnd_format x : generic_format radix2 fexp (rnd x).
Proof. apply generic_format_round; [apply fexp_valid | apply valid_rnd_N]. Qed.

Lemma rnd_le x y : x <= y -> rnd x <= rnd y.
Proof. intros H. apply round_le; [apply fexp_valid | apply valid_rnd_N | exact H]. Qed.

Lemma rnd_fix x : generic_format radix2 fexp x -> rnd x = x.
Proof. intros H. apply round_generic; [apply valid_rnd_N | exact H]. Qed.

Lemma rnd_0 : rnd 0 = 0.
Proof. unfold rnd. apply round_0. apply valid_rnd_N. Qed.

Lemma format_bpow e : (-1021 <= e)%Z -> generic_format radix2 fexp (bpow radix2 e).
Proof.
  intros He. apply generic_format_bpow. unfold fexp, FLT_exp. lia.
Qed.

Lemma rnd_one : rnd 1 = 1.
Proof.
  apply rnd_fix. replace 1 with (bpow radix2 0) by reflexivity.
  apply format_bpow. lia.
Qed.

Lemma rnd_half : rnd (/ 2) = / 2.
Proof.
  apply rnd_fix.
  replace (/ 2) with (bpow radix2 (-1)) by (simpl; lra).
  apply format_bpow. lia.
Qed.

(** The half-ulp bound, in the form the proofs use: below [2^e] (and above the
    subnormal range) the error of one rounding is at most [2^(e - 54)]. *)
Lemma rnd_err_below x e :
  (-1021 <= e)%Z -> Rabs x < bpow radix2 e -> Rabs (rnd x - x) <= bpow radix2 (e - 54).
Proof.
  intros He Hx. destruct (Req_dec x 0) as [->|Hne].
  - rewrite rnd_0. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. left. apply bpow_gt_0.
  - eapply Rle_trans; [apply error_le_half_ulp; apply fexp_valid | ].
    rewrite ulp_neq_0 by exact Hne. unfold cexp, fexp, FLT_exp.
    assert (Hm : (mag radix2 x <= e)%Z) by (apply mag_le_bpow; assumption).
    assert (Hb : bpow radix2 (Z.max (mag radix2 x - 53) (-1074)) <= bpow radix2 (e - 53)).
    { apply bpow_le. lia. }
    replace (e - 54)%Z with ((e - 53) + (-1))%Z by lia. rewrite bpow_plus.
    replace (bpow radix2 (-1)) with (/ 2) by (simpl; lra). lra.
Qed.

(** A value in [[0, 1]] rounds with error at most [2^-54]: below one the bound is
    [2^(0 - 54)], and one itself is representable. *)
Lemma rnd_err_unit x : 0 <= x <= 1 -> Rabs (rnd x - x) <= c54.
Proof.
  intros [H0 H1]. destruct (Req_dec x 1) as [->|Hne].
  - rewrite rnd_one. replace (1 - 1) with 0 by ring. rewrite Rabs_R0. left. apply c54_pos.
  - assert (Hlt : Rabs x < bpow radix2 0) by (rewrite Rabs_right by lra; simpl; lra).
    pose proof (rnd_err_below x 0 ltac:(lia) Hlt) as H.
    replace (0 - 54)%Z with (-54)%Z in H by lia. exact H.
Qed.

Lemma rnd_err_half x : 0 <= x < / 2 -> Rabs (rnd x - x) <= c54 / 2.
Proof.
  intros [H0 H1].
  assert (Hlt : Rabs x < bpow radix2 (-1)) by (rewrite Rabs_right by lra; simpl; lra).
  pose proof (rnd_err_below x (-1) ltac:(lia) Hlt) as H.
  replace (-1 - 54)%Z with (-55)%Z in H by lia. rewrite c54_half in H. exact H.
Qed.

(** Below one eighth, the error is at most [2^-57]. *)
Lemma rnd_err_eighth x : Rabs x < / 8 -> Rabs (rnd x - x) <= c54 / 8.
Proof.
  intros H.
  assert (Hlt : Rabs x < bpow radix2 (-3)) by (simpl; lra).
  pose proof (rnd_err_below x (-3) ltac:(lia) Hlt) as Hr.
  replace (-3 - 54)%Z with (-57)%Z in Hr by lia.
  replace (bpow radix2 (-57)) with (c54 / 8) in Hr; [exact Hr|].
  unfold c54. replace (-54)%Z with (-57 + 3)%Z by lia. rewrite bpow_plus. simpl. lra.
Qed.

Lemma Rmax0_lipschitz a b : Rabs (Rmax 0 a - Rmax 0 b) <= Rabs (a - b).
Proof.
  pose proof (Rle_abs (a - b)) as H1. pose proof (Rle_abs (b - a)) as H2.
  rewrite (Rabs_minus_sym b a) in H2.
  unfold Rmax. destruct (Rle_dec 0 a), (Rle_dec 0 b); apply Rabs_le; split; lra.
Qed.

Lemma abs3 x y z : Rabs (x + y - z) <= Rabs x + Rabs y + Rabs z.
Proof.
  pose proof (Rabs_triang (x + y) (- z)) as H1. pose proof (Rabs_triang x y) as H2.
  rewrite Rabs_Ropp in H1. unfold Rminus. lra.
Qed.

Lemma abs3p x y z : Rabs (x + y + z) <= Rabs x + Rabs y + Rabs z.
Proof.
  pose proof (Rabs_triang (x + y) z) as H1. pose proof (Rabs_triang x y) as H2. lra.
Qed.

Lemma abs2m x y : Rabs (x - y) <= Rabs x + Rabs y.
Proof.
  pose proof (Rabs_triang x (- y)) as H. rewrite Rabs_Ropp in H. unfold Rminus. lra.
Qed.

Lemma clamp_low y : y <= 0 -> clamp y = 0.
Proof.
  intros H. unfold clamp. rewrite Rmin_right by lra. apply Rmax_left. lra.
Qed.

Lemma clamp_high y : 1 <= y -> clamp y = 1.
Proof.
  intros H. unfold clamp. rewrite Rmin_left by lra. apply Rmax_right. lra.
Qed.

Lemma clamp_mid y : 0 <= y <= 1 -> clamp y = y.
Proof.
  intros [H0 H1]. unfold clamp. rewrite Rmin_right by lra. apply Rmax_right. lra.
Qed.

(** The clamp to [[0, 1]] never increases the distance between two values. *)
Lemma clamp_lipschitz a b : Rabs (clamp a - clamp b) <= Rabs (a - b).
Proof.
  pose proof (Rle_abs (a - b)) as H1. pose proof (Rle_abs (b - a)) as H2.
  rewrite (Rabs_minus_sym b a) in H2.
  destruct (Rle_dec a 0) as [Ha0|Ha0]; [rewrite (clamp_low a Ha0)|];
  destruct (Rle_dec 1 a) as [Ha1|Ha1]; try rewrite (clamp_high a Ha1);
  destruct (Rle_dec b 0) as [Hb0|Hb0]; try rewrite (clamp_low b Hb0);
  destruct (Rle_dec 1 b) as [Hb1|Hb1]; try rewrite (clamp_high b Hb1);
  try (rewrite clamp_mid in * by lra); try (rewrite (clamp_mid a) by lra); try (rewrite (clamp_mid b) by lra);
  apply Rabs_le; split; lra.
Qed.

Lemma clamp_in P : 0 <= P <= 1 -> clamp P = P.
Proof. exact (clamp_mid P). Qed.

(** The final rounding and clamp: whatever [x] is, the clamped rounded value is
    within [2^-54] of [x] in its distance to a probability. *)
Lemma round_clamp x P :
  0 <= P <= 1 -> Rabs (clamp (rnd x) - P) <= Rabs (x - P) + c54.
Proof.
  intros HP. pose proof c54_pos as Hc.
  pose proof (Rle_abs (x - P)) as H1. pose proof (Rle_abs (P - x)) as H2.
  rewrite (Rabs_minus_sym P x) in H2.
  destruct (Rlt_le_dec x 0) as [Hx|Hx].
  - assert (rnd x <= 0) by (rewrite <- rnd_0; apply rnd_le; lra).
    rewrite (clamp_low _ H). rewrite Rabs_minus_sym. rewrite Rabs_right by lra. lra.
  - destruct (Rlt_le_dec 1 x) as [Hx1|Hx1].
    + assert (1 <= rnd x) by (rewrite <- rnd_one; apply rnd_le; lra).
      rewrite (clamp_high _ H). rewrite Rabs_right by lra. lra.
    + pose proof (rnd_err_unit x (conj Hx Hx1)) as Hr.
      pose proof (clamp_lipschitz (rnd x) P) as Hl. rewrite (clamp_in P HP) in Hl.
      replace (rnd x - P) with ((rnd x - x) + (x - P)) in Hl by ring.
      pose proof (Rabs_triang (rnd x - x) (x - P)) as Ht. lra.
Qed.

Lemma c54_small : c54 <= / 100.
Proof.
  unfold c54.
  assert (bpow radix2 (-54) <= bpow radix2 (-10)) by (apply bpow_le; lia).
  assert (bpow radix2 (-10) = / 1024) by (simpl; lra). lra.
Qed.
