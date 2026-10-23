(** The last lines of the high-correlation branch, over Flocq's binary64:
    [bvn = -bvn / TAU], then [bvn + norm_cdf(-max)] for positive correlation and
    [-bvn + max(norm_cdf(-dh) - norm_cdf(dk), 0)] for negative
    (docs/bivariate_normal_high.md section 5).

    The accumulated integral enters through one hypothesis, [|g - G| <= D] for
    the computed [g] and the exact [G = J / (2 pi)]: everything proved here is
    the rounding of the assembly, with [norm_cdf] correctly rounded (the strong
    model) or within a relative [2^-53] (the documented contract, the weak
    model). *)
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

(** Positive correlation: [res = clamp (rnd (g + p))], [p] the computed
    [norm_cdf(-max)], [g] the computed [-J / tau], and the exact value
    [Pm - G] with [Pm = Phi(-max)] and [G = J / (2 pi)]. *)
Theorem pos_assembly Pm G g D :
  0 <= Pm <= 1 -> 0 <= Pm - G <= 1 -> Rabs (g + G) <= D ->
  Rabs (clamp (rnd (g + rnd Pm)) - (Pm - G)) <= D + 2 * c54.
Proof.
  intros HPm HP Hg.
  pose proof (round_clamp (g + rnd Pm) (Pm - G) HP) as H.
  pose proof (rnd_err_unit Pm HPm) as Hp.
  assert (Rabs (g + rnd Pm - (Pm - G)) <= D + c54).
  { replace (g + rnd Pm - (Pm - G)) with ((g + G) + (rnd Pm - Pm)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  lra.
Qed.

(** The same under the documented [norm_cdf] contract, [|p - Pm| <= 2^-53]. *)
Theorem pos_assembly_weak Pm G g p D :
  0 <= Pm - G <= 1 -> Rabs (g + G) <= D -> Rabs (p - Pm) <= 2 * c54 ->
  Rabs (clamp (rnd (g + p)) - (Pm - G)) <= D + 3 * c54.
Proof.
  intros HP Hg Hp.
  pose proof (round_clamp (g + p) (Pm - G) HP) as H.
  assert (Rabs (g + p - (Pm - G)) <= D + 2 * c54).
  { replace (g + p - (Pm - G)) with ((g + G) + (p - Pm)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  lra.
Qed.

(** Negative correlation as shipped: both [norm_cdf] results rounded, their
    difference rounded, the clamp at zero, the sum rounded.  The exact value is
    [G + max(0, P1 - P2)]. *)
Theorem neg_assembly P1 P2 G g D :
  0 <= P1 <= 1 -> 0 <= P2 <= 1 -> 0 <= G -> Rabs (g - G) <= D ->
  0 <= G + Rmax 0 (P1 - P2) <= 1 ->
  Rabs (clamp (rnd (g + Rmax 0 (rnd (rnd P1 - rnd P2)))) - (G + Rmax 0 (P1 - P2)))
  <= D + 7 / 2 * c54.
Proof.
  intros H1 H2 HG Hg HP.
  pose proof c54_pos as Hc.
  set (p1 := rnd P1). set (p2 := rnd P2).
  assert (Hp1 : Rabs (p1 - P1) <= c54) by (apply rnd_err_unit; lra).
  assert (Hp1u : p1 <= 1) by (rewrite <- rnd_one; apply rnd_le; lra).
  assert (Hp2l : 0 <= p2) by (rewrite <- rnd_0; apply rnd_le; lra).
  assert (Hp2 : Rabs (p2 - P2) <= c54) by (apply rnd_err_unit; lra).
  assert (Ht : Rabs (Rmax 0 (rnd (p1 - p2)) - Rmax 0 (P1 - P2)) <= 5 / 2 * c54).
  { destruct (Rlt_le_dec p1 p2) as [Hlt|Hge].
    - assert (P1 < P2).
      { destruct (Rlt_le_dec P1 P2) as [|Hb]; [assumption|]. exfalso.
        pose proof (rnd_le P2 P1 Hb) as H. unfold p1, p2 in Hlt. lra. }
      assert (rnd (p1 - p2) <= 0) by (rewrite <- rnd_0; apply rnd_le; lra).
      assert (Rmax 0 (rnd (p1 - p2)) = 0) by (unfold Rmax; destruct (Rle_dec 0 (rnd (p1 - p2))); lra).
      assert (Rmax 0 (P1 - P2) = 0) by (unfold Rmax; destruct (Rle_dec 0 (P1 - P2)); lra).
      rewrite H3, H4.
      replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
    - destruct (Rle_dec (p1 / 2) p2) as [Hs|Hns].
      + assert (Hf : generic_format radix2 fexp (p1 - p2)).
        { apply sterbenz; [apply fexp_valid | apply fexp_mono | apply rnd_format | apply rnd_format | lra]. }
        rewrite (rnd_fix _ Hf).
        eapply Rle_trans; [apply Rmax0_lipschitz|].
        replace (p1 - p2 - (P1 - P2)) with ((p1 - P1) - (p2 - P2)) by ring.
        eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra.
      + assert (HP2 : P2 < / 2).
        { destruct (Rlt_le_dec P2 (/ 2)) as [|Hb]; [assumption|]. exfalso.
          pose proof (rnd_le (/ 2) P2 Hb) as H. rewrite rnd_half in H. unfold p2 in Hns. lra. }
        pose proof (rnd_err_half P2 (conj (proj1 H2) HP2)) as Hp2h.
        assert (Hsub : Rabs (rnd (p1 - p2) - (p1 - p2)) <= c54) by (apply rnd_err_unit; lra).
        eapply Rle_trans; [apply Rmax0_lipschitz|].
        replace (rnd (p1 - p2) - (P1 - P2)) with ((rnd (p1 - p2) - (p1 - p2)) + (p1 - P1) - (p2 - P2)) by ring.
        pose proof (abs3 (rnd (p1 - p2) - (p1 - p2)) (p1 - P1) (p2 - P2)) as H3.
        change (rnd P2) with p2 in Hp2h. lra. }
  pose proof (round_clamp (g + Rmax 0 (rnd (p1 - p2))) (G + Rmax 0 (P1 - P2)) HP) as H.
  assert (Rabs (g + Rmax 0 (rnd (p1 - p2)) - (G + Rmax 0 (P1 - P2))) <= D + 5 / 2 * c54).
  { replace (g + Rmax 0 (rnd (p1 - p2)) - (G + Rmax 0 (P1 - P2)))
      with ((g - G) + (Rmax 0 (rnd (p1 - p2)) - Rmax 0 (P1 - P2))) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  lra.
Qed.

Lemma c54_small : c54 <= / 100.
Proof.
  unfold c54.
  assert (bpow radix2 (-54) <= bpow radix2 (-10)) by (apply bpow_le; lia).
  assert (bpow radix2 (-10) = / 1024) by (simpl; lra). lra.
Qed.

(** Negative correlation with the difference of the two [norm_cdf] results kept as
    a double-word: [s = rnd (p1 - p2)], its exact error [e = (p1 - p2) - s], and the
    sum [rnd (s + rnd (e + g))] -- one rounding of the result plus a rounding of
    the small [e + g], for [p2 <= p1] and a float [g] of size at most [1/10]. *)
Theorem neg_assembly_dw P1 P2 G g D :
  0 <= P1 <= 1 -> 0 <= P2 <= 1 -> 0 <= G -> Rabs (g - G) <= D ->
  generic_format radix2 fexp g -> 0 <= g <= / 10 ->
  0 <= G + Rmax 0 (P1 - P2) <= 1 -> rnd P2 <= rnd P1 ->
  let p1 := rnd P1 in let p2 := rnd P2 in
  let s := rnd (p1 - p2) in let e := (p1 - p2) - s in
  Rabs (clamp (rnd (s + rnd (e + g))) - (G + Rmax 0 (P1 - P2))) <= D + 3 * c54.
Proof.
  intros H1 H2 HG Hg Gf Hg01 HP Hle p1 p2 s e.
  pose proof c54_pos as Hc. pose proof c54_small as Hsm.
  assert (Hp1 : Rabs (p1 - P1) <= c54) by (apply rnd_err_unit; lra).
  assert (Hp1u : p1 <= 1) by (unfold p1; rewrite <- rnd_one; apply rnd_le; lra).
  assert (Hp2l : 0 <= p2) by (unfold p2; rewrite <- rnd_0; apply rnd_le; lra).
  assert (Hp2 : Rabs (p2 - P2) <= c54) by (apply rnd_err_unit; lra).
  assert (Hle' : p2 <= p1) by exact Hle.
  assert (Hm0 : Rmax 0 (p1 - p2) = p1 - p2) by (apply Rmax_right; lra).
  assert (Hmax : Rabs (p1 - p2 - Rmax 0 (P1 - P2)) <= Rabs ((p1 - P1) - (p2 - P2))).
  { rewrite <- Hm0. eapply Rle_trans; [apply Rmax0_lipschitz|]. right. f_equal. ring. }
  pose proof (abs2m (p1 - P1) (p2 - P2)) as Hm2.
  set (P := G + Rmax 0 (P1 - P2)) in *.
  pose proof (round_clamp (s + rnd (e + g)) P HP) as Hfin.
  assert (Hx : Rabs (s + rnd (e + g) - P) <= D + 2 * c54).
  { destruct (Rle_dec (p1 / 2) p2) as [Hs|Hns].
    - assert (Hf : generic_format radix2 fexp (p1 - p2)).
      { apply sterbenz; [apply fexp_valid | apply fexp_mono | apply rnd_format | apply rnd_format | lra]. }
      assert (Hs' : s = p1 - p2) by (unfold s; apply rnd_fix; exact Hf).
      assert (He : e = 0) by (unfold e; rewrite Hs'; ring).
      rewrite He, Rplus_0_l, (rnd_fix g Gf), Hs'.
      replace (p1 - p2 + g - P) with ((g - G) + (p1 - p2 - Rmax 0 (P1 - P2))) by (unfold P; ring).
      pose proof (Rabs_triang (g - G) (p1 - p2 - Rmax 0 (P1 - P2))) as H4.
      lra.
    - assert (HP2 : P2 < / 2).
      { destruct (Rlt_le_dec P2 (/ 2)) as [|Hb]; [assumption|]. exfalso.
        pose proof (rnd_le (/ 2) P2 Hb) as H. rewrite rnd_half in H. fold p2 in H. lra. }
      pose proof (rnd_err_half P2 (conj (proj1 H2) HP2)) as Hp2h. change (rnd P2) with p2 in Hp2h.
      assert (He : Rabs e <= c54).
      { unfold e. replace (p1 - p2 - s) with (-(s - (p1 - p2))) by ring. rewrite Rabs_Ropp.
        unfold s. apply rnd_err_unit. lra. }
      assert (Heg : Rabs (e + g) < / 8).
      { apply Rabs_lt. pose proof (Rabs_le_inv _ _ He) as [He1 He2]. lra. }
      pose proof (rnd_err_eighth (e + g) Heg) as Hy.
      assert (Hv : s + rnd (e + g) - P
        = (g - G) + (p1 - p2 - Rmax 0 (P1 - P2)) + (rnd (e + g) - (e + g))).
      { unfold e, P. ring. }
      rewrite Hv.
      pose proof (abs3p (g - G) (p1 - p2 - Rmax 0 (P1 - P2)) (rnd (e + g) - (e + g))) as H3.
      lra. }
  lra.
Qed.

