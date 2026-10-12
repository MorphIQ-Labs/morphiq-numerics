(** The approximations of [ln_1p]'s stages H and B (docs/ln.md, section 7).

    [ln(1 + z)] is its series [z − z^2/2 + z^3/3 − …] to [n] terms within
    [|z|^(n+1)/(1 − |z|)] ([ln1p_series], by the mean value theorem: the
    difference's derivative is [(−t)^n/(1 + t)]). With enough terms, each
    stage's polynomial error is then a polynomial in [z] with rational
    coefficients, which CoqInterval bounds on [|z| <= 2^-9]: stage H's within
    [2^-50.79·z^2] ([h_approx]), stage B's within [2^-55.57·|z|^3]
    ([b_approx]), the bounds formal/ln/stage_h_gz.g and stage_b_small.g assume
    and generators/ln_poly.sollya's [supnorm] certifies. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pCertificates.

Open Scope R_scope.

Fixpoint lser (n : nat) (z : R) : R :=
  match n with
  | O => 0
  | S k => lser k z + (-1) ^ k / INR (S k) * z ^ (S k)
  end.

Fixpoint dlser (n : nat) (t : R) : R :=
  match n with
  | O => 0
  | S k => dlser k t + (- t) ^ k
  end.

Lemma lim_eq f x l l' : derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros H E. rewrite <- E. exact H. Qed.

Lemma lser_deriv n t : derivable_pt_lim (lser n) t (dlser n t).
Proof.
  induction n as [|k IH].
  - change (lser 0) with (fct_cte 0). apply derivable_pt_lim_const.
  - change (lser (S k)) with (plus_fct (lser k) (mult_real_fct ((-1) ^ k / INR (S k)) (fun t => t ^ (S k)))).
    eapply lim_eq.
    + apply derivable_pt_lim_plus; [exact IH | apply derivable_pt_lim_scal, derivable_pt_lim_pow].
    + cbn [dlser]. replace (Init.Nat.pred (S k)) with k by lia.
      assert (0 < INR (S k)) by (apply lt_0_INR; lia).
      replace ((- t) ^ k) with ((-1) ^ k * t ^ k) by (rewrite <- Rpow_mult_distr; f_equal; ring).
      field. lra.
Qed.

Lemma dlser_closed n t : (1 + t) * dlser n t = 1 - (- t) ^ n.
Proof.
  induction n as [|k IH].
  - simpl. ring.
  - cbn [dlser]. rewrite Rmult_plus_distr_l, IH. simpl. ring.
Qed.

Definition lgap (n : nat) (t : R) : R := ln (1 + t) - lser n t.

Lemma lgap_deriv n t : -1 < t -> derivable_pt_lim (lgap n) t ((- t) ^ n / (1 + t)).
Proof.
  intros H.
  assert (D1 : derivable_pt_lim (fun t => ln (1 + t)) t (/ (1 + t) * 1)).
  { apply (derivable_pt_lim_comp (fun t => 1 + t) ln t 1 (/ (1 + t))).
    - eapply lim_eq; [apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id] | ring].
    - apply derivable_pt_lim_ln. lra. }
  change (lgap n) with (minus_fct (fun t => ln (1 + t)) (lser n)).
  eapply lim_eq; [apply derivable_pt_lim_minus; [exact D1 | apply lser_deriv] | ].
  apply Rmult_eq_reg_l with (1 + t); [ | lra].
  replace ((1 + t) * (/ (1 + t) * 1 - dlser n t)) with (1 - (1 + t) * dlser n t) by (field; lra).
  rewrite dlser_closed. field. lra.
Qed.

Lemma lgap_0 n : lgap n 0 = 0.
Proof.
  unfold lgap. rewrite Rplus_0_r, ln_1.
  induction n as [|k IH]; [simpl; ring | ].
  cbn [lser]. simpl pow at 2. rewrite Rmult_0_l, Rmult_0_r. lra.
Qed.

(** [ln(1 + z)] is its series to [n] terms within [|z|^(n+1)/(1 − |z|)]. *)
Theorem ln1p_series n z : Rabs z <= / 2 ->
  Rabs (ln (1 + z) - lser n z) <= Rabs z ^ (n + 1) / (1 - Rabs z).
Proof.
  intros Hz. apply Rabs_le_inv in Hz as Hz'.
  assert (Bd : forall c, Rabs c <= Rabs z -> Rabs ((- c) ^ n / (1 + c)) <= Rabs z ^ n / (1 - Rabs z)).
  { intros c Hc.
    assert (Hc2 : Rabs c <= / 2) by lra. apply Rabs_le_inv in Hc2. assert (Nz : 1 + c <> 0) by lra.
    unfold Rdiv. rewrite Rabs_mult, <- RPow_abs, Rabs_Ropp, Rabs_Rinv by exact Nz.
    assert (Pc : 1 - Rabs z <= Rabs (1 + c)).
    { apply Rabs_le_inv in Hc. rewrite (Rabs_pos_eq (1 + c)) by lra.
      destruct (Rcase_abs z) as [N | P]; [rewrite Rabs_left in Hc |- * by exact N | rewrite Rabs_pos_eq in Hc |- * by lra]; lra. }
    apply Rmult_le_compat; [apply pow_le, Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | | ].
    - apply pow_incr. split; [apply Rabs_pos | exact Hc].
    - apply Rinv_le_contravar; lra. }
  replace (ln (1 + z) - lser n z) with (lgap n z) by reflexivity.
  assert (Zb : 0 <= Rabs z <= / 2) by (split; [apply Rabs_pos | exact Hz]).
  assert (MV : exists c, Rabs c <= Rabs z /\ lgap n z = (- c) ^ n / (1 + c) * z).
  { destruct (Rtotal_order z 0) as [N | [E | P]].
    - destruct (MVT_cor2 (lgap n) (fun t => (- t) ^ n / (1 + t)) z 0 N
                  ltac:(intros c Hc; apply lgap_deriv; lra)) as [c [Ec [C0 C1]]].
      exists c. split.
      + rewrite (Rabs_left z) by exact N. rewrite Rabs_left by lra. lra.
      + rewrite lgap_0 in Ec. replace (0 - z) with (- z) in Ec by ring.
        rewrite <- Ropp_mult_distr_r in Ec. lra.
    - exists 0. subst z. rewrite lgap_0, Rmult_0_r. split; [rewrite Rabs_R0; lra | reflexivity].
    - destruct (MVT_cor2 (lgap n) (fun t => (- t) ^ n / (1 + t)) 0 z P
                  ltac:(intros c Hc; apply lgap_deriv; lra)) as [c [Ec [C0 C1]]].
      exists c. split.
      + rewrite (Rabs_pos_eq z) by lra. rewrite Rabs_pos_eq by lra. lra.
      + rewrite lgap_0, Rminus_0_r, Rminus_0_r in Ec. exact Ec. }
  destruct MV as [c [Hc E]]. rewrite E, Rabs_mult.
  pose proof (Bd c Hc) as B.
  replace (Rabs z ^ (n + 1) / (1 - Rabs z)) with (Rabs z ^ n / (1 - Rabs z) * Rabs z)
    by (rewrite pow_add, pow_1; field; lra).
  apply Rmult_le_compat_r; [apply Rabs_pos | exact B].
Qed.

(** [|ln(1 + u) − u| <= u^2/(1 − |u|)]. *)
Corollary ln1p_linear u : Rabs u <= / 2 -> Rabs (ln (1 + u) - u) <= u * u / (1 - Rabs u).
Proof.
  intros H. pose proof (ln1p_series 1 u H) as S. cbn [lser] in S.
  replace (0 + (-1) ^ 0 / INR 1 * u ^ 1) with u in S by (simpl; field).
  assert (E : Rabs u ^ (1 + 1) = u * u).
  { replace (1 + 1)%nat with 2%nat by reflexivity. rewrite RPow_abs, Rabs_pos_eq by (apply pow2_ge_0). ring. }
  rewrite E in S. exact S.
Qed.

Lemma bpow_m (k : nat) : bpow radix2 (- Z.of_nat k) = / 2 ^ k.
Proof. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. Qed.

(** Stage H: [|ln(1 + z) − z − z^2 P(z)| <= 592·2^-60·z^2] on [|z| <= 2^-9]. *)
Theorem h_approx z : Rabs z <= / 2 ^ 9 ->
  Rabs (ln (1 + z) - z - z * z * h_Pz z) <= 592 * / 2 ^ 60 * (z * z).
Proof.
  intros Hz.
  assert (H2 : Rabs z <= / 2) by (apply Rle_trans with (1 := Hz); interval with (i_prec 64)).
  pose proof (ln1p_series 9 z H2) as S.
  assert (D : Rabs ((1 / 3 - h3) * z + (- (1 / 4) - h4) * z ^ 2 + (1 / 5 - h5) * z ^ 3 + (- (1 / 6) - h6) * z ^ 4
                    + z ^ 5 / 7 - z ^ 6 / 8 + z ^ 7 / 9) <= 4730 * / 2 ^ 63).
  { unfold h3, h4, h5, h6. change (-52)%Z with (- Z.of_nat 52)%Z. change (-55)%Z with (- Z.of_nat 55)%Z.
    change (-54)%Z with (- Z.of_nat 54)%Z. rewrite !bpow_m.
    apply Rabs_le_inv in Hz.
    interval with (i_bisect z, i_taylor z, i_degree 8, i_prec 100, i_depth 12). }
  assert (E : ln (1 + z) - z - z * z * h_Pz z
              = z * z * ((1 / 3 - h3) * z + (- (1 / 4) - h4) * z ^ 2 + (1 / 5 - h5) * z ^ 3 + (- (1 / 6) - h6) * z ^ 4
                         + z ^ 5 / 7 - z ^ 6 / 8 + z ^ 7 / 9) + (ln (1 + z) - lser 9 z)).
  { assert (Hh : IZR 1 * bpow radix2 (-1) = / 2) by (change (bpow radix2 (-1)) with (/ IZR 2); apply Rmult_1_l).
    unfold h_Pz. rewrite Hh. cbn [lser INR]. simpl pow. field. }
  rewrite E. apply Rle_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_mult, (Rabs_pos_eq (z * z)) by nra.
  assert (R : Rabs z ^ (9 + 1) / (1 - Rabs z) <= / 2 ^ 70 * (z * z)).
  { assert (A : 0 <= Rabs z <= / 2 ^ 9) by (split; [apply Rabs_pos | exact Hz]).
    assert (P2 : Rabs z ^ (9 + 1) = Rabs z ^ 8 * (z * z)).
    { replace (9 + 1)%nat with (8 + 2)%nat by reflexivity. rewrite pow_add. f_equal.
      rewrite RPow_abs, Rabs_pos_eq by apply pow2_ge_0. ring. }
    assert (A8 : Rabs z ^ 8 / (1 - Rabs z) <= / 2 ^ 70).
    { set (a := Rabs z) in *. clear - A. interval with (i_prec 80). }
    rewrite P2. replace (Rabs z ^ 8 * (z * z) / (1 - Rabs z)) with (Rabs z ^ 8 / (1 - Rabs z) * (z * z))
      by (field; interval with (i_prec 64)).
    apply Rmult_le_compat_r; [nra | exact A8]. }
  assert (Z2 : 0 <= z * z) by nra.
  assert (C : 4730 * / 2 ^ 63 + / 2 ^ 70 <= 592 * / 2 ^ 60) by interval with (i_prec 64).
  pose proof (Rle_trans _ _ _ S R) as SR.
  apply Rmult_le_compat_r with (r := z * z) in D; [ | exact Z2].
  nra.
Qed.

(** Stage B: [|ln(1 + z) − z + z^2/2 − z^3 W(z)| <= 691·2^-65·|z|^3] on [|z| <= 2^-9]. *)
Theorem b_approx z : Rabs z <= / 2 ^ 9 ->
  Rabs (ln (1 + z) - z + z * z / 2 - z * z * z * b_W z) <= 691 * / 2 ^ 65 * Rabs (z * z * z).
Proof.
  intros Hz.
  assert (H2 : Rabs z <= / 2) by (apply Rle_trans with (1 := Hz); interval with (i_prec 64)).
  pose proof (ln1p_series 11 z H2) as S.
  assert (D : Rabs ((1 / 3 - b3) + (- (1 / 4) - b4) * z + (1 / 5 - b5) * z ^ 2 + (- (1 / 6) - b6) * z ^ 3
                    + (1 / 7 - b7) * z ^ 4 + (- (1 / 8) - b8) * z ^ 5 + z ^ 6 / 9 - z ^ 7 / 10 + z ^ 8 / 11)
              <= 690 * / 2 ^ 65).
  { unfold b3, b4, b5, b6, b7, b8. change (-54)%Z with (- Z.of_nat 54)%Z. change (-2)%Z with (- Z.of_nat 2)%Z.
    change (-53)%Z with (- Z.of_nat 53)%Z. change (-56)%Z with (- Z.of_nat 56)%Z. rewrite !bpow_m.
    apply Rabs_le_inv in Hz.
    interval with (i_bisect z, i_taylor z, i_degree 9, i_prec 100, i_depth 12). }
  assert (E : ln (1 + z) - z + z * z / 2 - z * z * z * b_W z
              = z * z * z * ((1 / 3 - b3) + (- (1 / 4) - b4) * z + (1 / 5 - b5) * z ^ 2 + (- (1 / 6) - b6) * z ^ 3
                    + (1 / 7 - b7) * z ^ 4 + (- (1 / 8) - b8) * z ^ 5 + z ^ 6 / 9 - z ^ 7 / 10 + z ^ 8 / 11)
                + (ln (1 + z) - lser 11 z)).
  { unfold b_W. cbn [lser INR]. simpl pow. field. }
  rewrite E. apply Rle_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_mult.
  assert (Z3 : 0 <= Rabs (z * z * z)) by apply Rabs_pos.
  assert (R : Rabs z ^ (11 + 1) / (1 - Rabs z) <= / 2 ^ 80 * Rabs (z * z * z)).
  { assert (A : 0 <= Rabs z <= / 2 ^ 9) by (split; [apply Rabs_pos | exact Hz]).
    assert (P3 : Rabs z ^ (11 + 1) = Rabs z ^ 9 * Rabs (z * z * z)).
    { replace (11 + 1)%nat with (9 + 3)%nat by reflexivity. rewrite pow_add. f_equal.
      rewrite !Rabs_mult. simpl. ring. }
    assert (A9 : Rabs z ^ 9 / (1 - Rabs z) <= / 2 ^ 80).
    { set (a := Rabs z) in *. clear - A. interval with (i_prec 80). }
    rewrite P3. replace (Rabs z ^ 9 * Rabs (z * z * z) / (1 - Rabs z)) with (Rabs z ^ 9 / (1 - Rabs z) * Rabs (z * z * z))
      by (field; interval with (i_prec 64)).
    apply Rmult_le_compat_r; [exact Z3 | exact A9]. }
  assert (C : 690 * / 2 ^ 65 + / 2 ^ 80 <= 691 * / 2 ^ 65) by interval with (i_prec 64).
  pose proof (Rle_trans _ _ _ S R) as SR.
  apply Rmult_le_compat_l with (r := Rabs (z * z * z)) in D; [ | exact Z3].
  nra.
Qed.
