(** What follows the accumulated integral in the high-correlation branch, and the
    proved parts of the integral's own rounding (docs/bivariate_normal_high.md
    sections 4 and 5).

    Proved here: the constants [TAU] and [SQRT_TAU]; the rounding of the plain
    sum of the node terms in a local; the magnitude that sum's terms can have;
    the division by [TAU]; and the composition of these with the assembly of
    [BvnHighAssembly.v] into the branch's bound for either sign, as a function of
    one hypothesis, [|Jt - J| <= 521e-18], on the computed integral.  That
    hypothesis is the sum of the truncation budget proved in [BvnHighPanels.v]
    (below [21e-18]) and a rounding budget of [5e-16] for [A1], [A2], the setup
    and the node brackets, which is a sampled first-order running bound, not a
    theorem; the document says so. *)
From Coq Require Import Reals Lra Psatz ZArith List.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighPanels.
Open Scope R_scope.

(** The two constants of the source, as the rationals their bits denote. *)
Definition TAU : R := 884279719003555 / 140737488355328.
Definition SQRT_TAU : R := 2822212540896131 / 1125899906842624.

Lemma tau_error : Rabs (TAU - 2 * PI) <= 4 / 10 ^ 17 * (2 * PI).
Proof. unfold TAU. interval with (i_prec 90). Qed.

Lemma sqrt_tau_error : Rabs (SQRT_TAU - sqrt (2 * PI)) <= 74 / 10 ^ 18 * sqrt (2 * PI).
Proof. unfold SQRT_TAU. interval with (i_prec 90). Qed.

Lemma tau_bounds : 628 / 100 <= TAU <= 629 / 100.
Proof. unfold TAU. split; interval. Qed.

(** The plain sum of the node terms, in a local, one rounding per addition.  If
    the partial sums stay below [2^-7] each rounds by at most [2^-61]. *)
Fixpoint sumabs (l : list R) : R := match l with nil => 0 | t :: l' => Rabs t + sumabs l' end.
Fixpoint rsum (l : list R) : R := match l with nil => 0 | t :: l' => t + rsum l' end.
Fixpoint fsum (acc : R) (l : list R) : R :=
  match l with nil => acc | t :: l' => fsum (rnd (acc + t)) l' end.

Lemma sumabs_nonneg l : 0 <= sumabs l.
Proof. induction l as [|t l IH]; simpl; [lra|]. pose proof (Rabs_pos t). lra. Qed.

Lemma fsum_error l : forall acc,
  Rabs acc + sumabs l + INR (length l) * bpow radix2 (-61) < bpow radix2 (-7) ->
  Rabs (fsum acc l - (acc + rsum l)) <= INR (length l) * bpow radix2 (-61).
Proof.
  induction l as [|t l IH]; intros acc H; cbn [fsum rsum sumabs length] in *.
  - replace (acc - (acc + 0)) with 0 by ring. rewrite Rabs_R0. cbn [INR]. lra.
  - pose proof (Rabs_pos t) as Ht. pose proof (sumabs_nonneg l) as Hs.
    assert (Hn : 0 <= INR (length l)) by apply pos_INR.
    rewrite S_INR in *.
    pose proof (bpow_gt_0 radix2 (-61)) as Hb.
    assert (Hnb : 0 <= INR (length l) * bpow radix2 (-61)) by (apply Rmult_le_pos; lra).
    assert (Hx : Rabs (acc + t) < bpow radix2 (-7)).
    { pose proof (Rabs_triang acc t). rewrite Rmult_plus_distr_r in H. lra. }
    pose proof (rnd_err_below (acc + t) (-7) ltac:(lia) Hx) as Hr.
    replace (-7 - 54)%Z with (-61)%Z in Hr by lia.
    set (acc' := rnd (acc + t)) in *.
    assert (Hacc' : Rabs acc' <= Rabs (acc + t) + bpow radix2 (-61)).
    { pose proof (Rabs_triang (acc' - (acc + t)) (acc + t)).
      replace (acc' - (acc + t) + (acc + t)) with acc' in H0 by ring. lra. }
    pose proof (Rabs_triang acc t) as Hat.
    assert (Hih : Rabs acc' + sumabs l + INR (length l) * bpow radix2 (-61) < bpow radix2 (-7)).
    { rewrite Rmult_plus_distr_r in H. lra. }
    specialize (IH acc' Hih).
    replace (fsum acc' l - (acc + (t + rsum l)))
      with ((fsum acc' l - (acc' + rsum l)) + (acc' - (acc + t))) by ring.
    pose proof (Rabs_triang (fsum acc' l - (acc' + rsum l)) (acc' - (acc + t))) as H2.
    rewrite Rmult_plus_distr_r. lra.
Qed.

Lemma c54_value : c54 = 1 / 18014398509481984.
Proof.
  unfold c54.
  assert (H : bpow radix2 54 * bpow radix2 (-54) = 1).
  { rewrite <- bpow_plus. replace (54 + -54)%Z with 0%Z by lia. reflexivity. }
  assert (H2 : bpow radix2 54 = 18014398509481984).
  { cbv [bpow]. cbn. unfold IZR. cbn. lra. }
  rewrite H2 in H. lra.
Qed.

Lemma bpow61_value : bpow radix2 (-61) = c54 / 128.
Proof.
  unfold c54. replace (-54)%Z with (-61 + 7)%Z by lia. rewrite bpow_plus.
  replace (bpow radix2 7) with 128 by (cbv [bpow]; cbn; unfold IZR; cbn; lra). lra.
Qed.

(** The magnitude the node terms can have: on the real axis [|E V| <= kappa x^6]
    (claim K of the document), so the terms of the panels [s_i / 2, s_i] sum, in
    absolute value, to at most [kappa sum_i (s_i / 2) s_i^6]. *)
Definition remainder_magnitude : R :=
  72 / 10 * (scale 0 / 2 * scale 0 ^ 6 + scale 1 / 2 * scale 1 ^ 6 + scale 2 / 2 * scale 2 ^ 6
    + scale 3 / 2 * scale 3 ^ 6 + scale 4 / 2 * scale 4 ^ 6 + scale 5 / 2 * scale 5 ^ 6
    + scale 6 / 2 * scale 6 ^ 6).

Lemma remainder_magnitude_bound : remainder_magnitude <= 43 / 10000.
Proof. unfold remainder_magnitude, scale. simpl. interval with (i_prec 60). Qed.

(** The 63 node terms summed in a local: at most [3e-17] of rounding, provided
    their absolute sum is at most [5e-3] (the bound above, plus the terms'
    own tiny computed deviations). *)
Theorem remainder_sum_error (l : list R) :
  length l = 63%nat -> sumabs l <= 5 / 1000 ->
  Rabs (fsum 0 l - rsum l) <= 3 / 10 ^ 17.
Proof.
  intros Hl Hs.
  assert (Hb : INR (length l) * bpow radix2 (-61) <= 3 / 10 ^ 17).
  { rewrite Hl, bpow61_value, c54_value. replace (INR 63) with 63 by (simpl; lra). lra. }
  assert (Hb0 : 0 <= INR (length l) * bpow radix2 (-61)).
  { apply Rmult_le_pos; [apply pos_INR | apply Rlt_le; apply bpow_gt_0]. }
  assert (Hlt : Rabs 0 + sumabs l + INR (length l) * bpow radix2 (-61) < bpow radix2 (-7)).
  { replace (bpow radix2 (-7)) with (/ 128) by (cbv [bpow]; cbn; unfold IZR; cbn; lra).
    rewrite Rabs_R0. lra. }
  pose proof (fsum_error l 0 Hlt) as H. rewrite Rplus_0_l in H. lra.
Qed.

(** Division by [TAU] and its rounding.  [J] is the integral, [Jt] its computed
    value within [dJ]; the result is [g = rnd (-Jt / TAU)] against [-J / (2 pi)]. *)
Theorem division_step Jt J dJ :
  0 <= J <= 21 / 50 -> Rabs (Jt - J) <= dJ -> dJ <= 1 / 1000 ->
  Rabs (rnd (- Jt / TAU) - (- (J / (2 * PI)))) <= 1593 / 10000 * dJ + 1 / 10 ^ 17.
Proof.
  intros HJ Hd HdJ.
  pose proof tau_bounds as [Tl Tu]. pose proof tau_error as Te. pose proof PI_RGT_0 as Hpi.
  pose proof (Rabs_pos (Jt - J)) as Hd0.
  pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  assert (HT : 0 < TAU) by lra.
  set (iT := / TAU).
  assert (HiT : TAU * iT = 1) by (unfold iT; field; lra).
  assert (HiT0 : 0 < iT) by (unfold iT; apply Rinv_0_lt_compat; lra).
  assert (HiT1 : iT <= 1593 / 10000) by nra.
  set (i2 := / (2 * PI)).
  assert (Hi2 : (2 * PI) * i2 = 1) by (unfold i2; field; lra).
  assert (Hi20 : 0 < i2) by (unfold i2; apply Rinv_0_lt_compat; lra).
  assert (Hx : Rabs (- Jt / TAU) < / 8).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_lt. split; nra. }
  pose proof (rnd_err_eighth _ Hx) as Hr.
  assert (Hc : c54 / 8 <= 7 / 10 ^ 18).
  { rewrite c54_value. lra. }
  assert (Hdiv : Rabs (- Jt / TAU - (- (J / (2 * PI)))) <= 1593 / 10000 * dJ + 3 / 10 ^ 18).
  { replace (- Jt / TAU - (- (J / (2 * PI)))) with (- (Jt - J) * iT + J * (TAU - 2 * PI) * (iT * i2)).
    2: { unfold iT, i2. field. split; lra. }
    pose proof (Rabs_triang (- (Jt - J) * iT) (J * (TAU - 2 * PI) * (iT * i2))) as Ht.
    assert (H1 : Rabs (- (Jt - J) * iT) <= 1593 / 10000 * dJ).
    { rewrite Rabs_mult, Rabs_Ropp, (Rabs_right iT) by lra. nra. }
    assert (H2 : Rabs (J * (TAU - 2 * PI) * (iT * i2)) <= 3 / 10 ^ 18).
    { rewrite !Rabs_mult. rewrite (Rabs_right J) by lra. rewrite (Rabs_right iT) by lra. rewrite (Rabs_right i2) by lra.
      assert (Hq : Rabs (TAU - 2 * PI) * i2 <= 4 / 10 ^ 17) by nra.
      assert (Hq0 : 0 <= Rabs (TAU - 2 * PI) * i2) by (apply Rmult_le_pos; [apply Rabs_pos | lra]).
      replace (J * Rabs (TAU - 2 * PI) * (iT * i2)) with (J * iT * (Rabs (TAU - 2 * PI) * i2)) by ring.
      assert (HJiT : J * iT <= 21 / 50 * (1593 / 10000)) by nra.
      assert (0 <= J * iT) by nra.
      nra. }
    lra. }
  pose proof (Rabs_triang (rnd (- Jt / TAU) - (- Jt / TAU)) (- Jt / TAU - (- (J / (2 * PI))))) as Hf.
  replace (rnd (- Jt / TAU) - (- Jt / TAU) + (- Jt / TAU - (- (J / (2 * PI)))))
    with (rnd (- Jt / TAU) - (- (J / (2 * PI)))) in Hf by ring.
  lra.
Qed.

Lemma design_total_small : design_total <= 21 / 10 ^ 18.
Proof. unfold design_total, tail_bound, panel_bound, scale. simpl. interval with (i_prec 60). Qed.

(** The hypothesis on the computed integral, in the integral's units: the
    rounding budget [5e-16] (sampled, see the header) plus the proved truncation
    budget [21e-18]. *)
Definition dJ_bound : R := 521 / 10 ^ 18.

Lemma g_small Jt J dJ :
  0 <= J <= 21 / 50 -> Rabs (Jt - J) <= dJ -> dJ <= 1 / 1000 ->
  Rabs (rnd (- Jt / TAU)) <= 1 / 10.
Proof.
  intros HJ Hd HdJ.
  pose proof tau_bounds as [Tl Tu]. pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  set (iT := / TAU).
  assert (HiT : TAU * iT = 1) by (unfold iT; field; lra).
  assert (HiT0 : 0 < iT) by (unfold iT; apply Rinv_0_lt_compat; lra).
  assert (HiT1 : iT <= 1593 / 10000) by nra.
  assert (Hx : Rabs (- Jt / TAU) < / 8).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_lt. split; nra. }
  pose proof (rnd_err_eighth _ Hx) as Hr.
  assert (Hc : c54 / 8 <= 7 / 10 ^ 18) by (rewrite c54_value; lra).
  assert (Hx2 : Rabs (- Jt / TAU) <= 7 / 100).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_le. split; nra. }
  pose proof (Rabs_triang (rnd (- Jt / TAU) - (- Jt / TAU)) (- Jt / TAU)) as Ht.
  replace (rnd (- Jt / TAU) - (- Jt / TAU) + (- Jt / TAU)) with (rnd (- Jt / TAU)) in Ht by ring.
  lra.
Qed.

(** The branch's bound for [rho > 0]: [Pm = Phi(-max(dh, dk))] and [J] the integral. *)
Theorem high_pos_bound Pm J Jt :
  0 <= Pm <= 1 -> 0 <= J <= 21 / 50 -> 0 <= Pm - J / (2 * PI) <= 1 ->
  Rabs (Jt - J) <= dJ_bound ->
  Rabs (clamp (rnd (rnd (- Jt / TAU) + rnd Pm)) - (Pm - J / (2 * PI))) <= 21 / 10 ^ 17.
Proof.
  intros HPm HJ HP Hd.
  assert (HdJ : dJ_bound <= 1 / 1000) by (unfold dJ_bound; lra).
  pose proof (division_step Jt J dJ_bound HJ Hd HdJ) as Hdiv.
  assert (Hg : Rabs (rnd (- Jt / TAU) + J / (2 * PI)) <= 1593 / 10000 * dJ_bound + 1 / 10 ^ 17).
  { replace (rnd (- Jt / TAU) + J / (2 * PI)) with (rnd (- Jt / TAU) - (- (J / (2 * PI)))) by ring. exact Hdiv. }
  pose proof (pos_assembly Pm (J / (2 * PI)) (rnd (- Jt / TAU)) _ HPm HP Hg) as H.
  assert (Hc : 2 * c54 = 2 / 18014398509481984) by (rewrite c54_value; lra).
  unfold dJ_bound in *. lra.
Qed.

(** The branch's bound for [rho < 0]: [P1 = Phi(-dh)], [P2 = Phi(dk)], the
    thresholds ordered [dh >= dk]. *)
Theorem high_neg_bound P1 P2 J Jt :
  0 <= P1 <= 1 -> 0 <= P2 <= 1 -> 0 <= J <= 21 / 50 ->
  0 <= J / (2 * PI) + Rmax 0 (P1 - P2) <= 1 -> (/ 2 <= P2 -> P1 <= P2) ->
  Rabs (Jt - J) <= dJ_bound ->
  let g := - rnd (- Jt / TAU) in
  let p1 := rnd P1 in let p2 := rnd P2 in
  let s := rnd (p1 - p2) in let e := (p1 - p2) - s in
  Rabs (clamp (if Rlt_dec p2 p1 then rnd (s + rnd (e + g)) else g)
        - (J / (2 * PI) + Rmax 0 (P1 - P2))) <= 24 / 10 ^ 17.
Proof.
  intros H1 H2 HJ HP Hord Hd g p1 p2 s e.
  assert (HdJ : dJ_bound <= 1 / 1000) by (unfold dJ_bound; lra).
  pose proof (division_step Jt J dJ_bound HJ Hd HdJ) as Hdiv.
  pose proof (g_small Jt J dJ_bound HJ Hd HdJ) as Hgs.
  pose proof PI_RGT_0 as Hpi.
  assert (HG : 0 <= J / (2 * PI)) by (apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  assert (Hg : Rabs (g - J / (2 * PI)) <= 1593 / 10000 * dJ_bound + 1 / 10 ^ 17).
  { unfold g. replace (- rnd (- Jt / TAU) - J / (2 * PI)) with (- (rnd (- Jt / TAU) - (- (J / (2 * PI))))) by ring.
    rewrite Rabs_Ropp. exact Hdiv. }
  assert (Gf : generic_format radix2 fexp g) by (unfold g; apply generic_format_opp; apply rnd_format).
  assert (Hgb : - / 10 <= g <= / 10).
  { unfold g. pose proof (Rabs_le_inv _ _ Hgs) as [A B]. lra. }
  pose proof (neg_assembly_final P1 P2 (J / (2 * PI)) g _ H1 H2 HG Hg Gf Hgb HP Hord) as H.
  assert (Hc : 21 / 8 * c54 = 21 / 8 / 18014398509481984) by (rewrite c54_value; lra).
  eapply Rle_trans; [exact H|]. unfold dJ_bound in *. lra.
Qed.
