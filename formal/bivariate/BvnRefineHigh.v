(** The high-correlation kernel (formal/bivariate/BvnKernel.v) against the
    real-valued transcription its error proof is written over (BvnHighNode.v,
    BvnHighCF.v, BvnHighJ1.v, BvnHighSum.v, BvnHighEnd.v): each binary64 function of
    the kernel returns the value of the matching function of the proof, under the
    ranges the proof's own hypotheses give, so no operation overflows. The
    square root is the IEEE operation, [sqrtF = rndF (sqrt r)], so the
    proof's [sqrtT] is instantiated at it. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt IEEE64Div.
Require Import BvnKernel BvnLift BvnTableFacts.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighNode BvnHighCF BvnHighJ1 BvnHighSum.
Open Scope R_scope.

Local Opaque fadd fsub fmul fdiv fsqrt fneg fabs.

Definition sqrtF (r : R) : R := rndF (sqrt r).

(** The exponent argument [phi] of a node is not negative. *)
Lemma phi_nonneg bs hk xs D : fmtF hk -> 0 <= bs -> - (4 * hk) <= bs -> 0 < xs -> xs <= 1 / 4 -> 1 <= D ->
  0 <= rndF (rndF (bs / (2 * xs)) + rndF (hk / D)).
Proof.
  intros Fh Hb Hc Hx0 Hx1 HD.
  apply rnd_nonneg0.
  assert (HD0 : 0 < D) by lra.
  assert (Hq : 2 * bs <= bs / (2 * xs)).
  { assert (Hi : 2 <= / (2 * xs)).
    { replace 2 with (/ (/ 2)) by (field). apply Rinv_le_contravar; [lra | lra]. }
    unfold Rdiv. nra. }
  destruct (Rle_or_lt 0 hk) as [Hk | Hk].
  - apply Rplus_le_le_0_compat; apply rnd_nonneg0.
    + apply Rmult_le_pos; [exact Hb | left; apply Rinv_0_lt_compat; lra].
    + apply Rmult_le_pos; [exact Hk | left; apply Rinv_0_lt_compat; lra].
  - assert (A : - hk <= rndF (bs / (2 * xs))).
    { apply rnd_ge_fmt; [apply generic_format_opp; exact Fh | nra]. }
    assert (B1 : hk <= rndF (hk / D)).
    { apply rnd_ge_fmt; [exact Fh |]. unfold Rdiv.
      assert (Hi : / D <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
      assert (Hi0 : 0 < / D) by (apply Rinv_0_lt_compat; lra). nra. }
    lra.
Qed.

(** The closed form's exponent argument [bs / a + hk] is not negative. *)
Lemma sum_nonneg bs hk a : fmtF hk -> 0 <= bs -> - (4 * hk) <= bs -> 0 < a -> a <= 1 / 4 ->
  0 <= rndF (rndF (bs / a) + hk).
Proof.
  intros Fh Hb Hc Ha0 Ha1. apply rnd_nonneg0.
  assert (Hq : 4 * bs <= bs / a).
  { assert (Hi : 4 <= / a).
    { replace 4 with (/ (/ 4)) by field. apply Rinv_le_contravar; [lra | lra]. }
    unfold Rdiv. nra. }
  destruct (Rle_or_lt 0 hk) as [Hk | Hk].
  - assert (0 <= rndF (bs / a)) by (apply rnd_nonneg0; apply Rmult_le_pos; [exact Hb | left; apply Rinv_0_lt_compat; lra]). lra.
  - assert (A : - hk <= rndF (bs / a)).
    { apply rnd_ge_fmt; [apply generic_format_opp; exact Fh | nra]. }
    lra.
Qed.

(** The high proofs' [rnd] is the model's [rndF]; the facts here are stated in [rndF]. *)
Ltac rnd2F := repeat match goal with |- context [rnd ?x] => change (rnd x) with (rndF x) end.

Lemma fmtF_quarter : fmtF (1 / 4).
Proof. replace (1 / 4) with (bpow radix2 (-2)) by (simpl; lra). apply fmtF_bpow. lia. Qed.

Lemma fmtF_half : fmtF (1 / 2).
Proof. replace (1 / 2) with (bpow radix2 (-1)) by (simpl; lra). apply fmtF_bpow. lia. Qed.

Section HighNode.
Variables (L : lib) (expT : R -> R).
Hypothesis Hexp : lib_exp_rel L expT 1 2.

(** One node's term: the kernel's [node_value], at the panel scale [s], the node's
    unit square [xu] and weight [w], is the proof's [node_term] at [s2T = rndF (s s)]. *)
Lemma node_value_ok sf xuf wf bsf hkf s xu w bs hk :
  exb sf s 0 -> 3 / 1000 < s -> s <= 381 / 1000 ->
  exb xuf xu 0 -> 1 / 4 <= xu -> xu <= 1 -> exb wf w 0 ->
  exb bsf bs 14 -> 0 <= bs -> exb hkf hk 11 -> - (4 * hk) <= bs ->
  exb (node_value L (sf /f k4) (sf *f sf) xuf wf bsf hkf)
      (node_term expT sqrtF (rndF (s * s)) xu w bs hk (s / 4)) 3.
Proof.
  intros Hs Hs0 Hs1 Hxu Hxu0 Hxu1 Hw Hbs Hbs0 Hhk Hc.
  unfold node_term, node_phiT, node_rsT, node_xsT. rnd2F.
  assert (Hs2 : exb (sf *f sf) (rndF (s * s)) 0) by lift_to.
  set (s2 := rndF (s * s)) in *.
  assert (Hs2lo : bpow radix2 (-17) <= s2).
  { apply rnd_ge_fmt; [apply fmtF_bpow; lia |]. bnum. nra. }
  assert (Hs2hi : s2 <= 1 / 4).
  { apply rnd_le_fmt; [exact fmtF_quarter | nra]. }
  assert (Hxs : exb (sf *f sf *f xuf) (rndF (s2 * xu)) 0) by lift_to.
  set (xs := rndF (s2 * xu)) in *.
  assert (Hxs0 : bpow radix2 (-19) <= xs).
  { apply rnd_ge_fmt; [apply fmtF_bpow; lia |]. assert (bpow radix2 (-19) = bpow radix2 (-17) * (1 / 4)) by (bnum; lra). pose proof (bpow_ge_0 radix2 (-17)). nra. }
  assert (Hxs1 : xs <= 1 / 4).
  { apply rnd_le_fmt; [exact fmtF_quarter | nra]. }
  assert (Hom : exb (k1 -f (sf *f sf *f xuf)) (rndF (1 - xs)) 1) by lift_to.
  set (om := rndF (1 - xs)) in *.
  assert (Hom0 : 1 / 2 <= om).
  { apply rnd_ge_fmt; [exact fmtF_half | lra]. }
  assert (Hom1 : om <= 1).
  { apply rnd_le_fmt; [exact fmtF_one | pose proof (bpow_gt_0 radix2 (-19)); lra]. }
  assert (Hrs : exb (fsqrt (k1 -f (sf *f sf *f xuf))) (sqrtF om) 1).
  { unfold sqrtF. eapply exb_weak; [eapply exb_sqrt; [exact Hom | lra | lia] | lia]. }
  set (rs := sqrtF om) in *.
  assert (Hrs0 : 1 / 2 <= rs).
  { unfold rs, sqrtF. apply rnd_ge_fmt; [exact fmtF_half |].
    assert (Hq : sqrt (1 / 4) <= sqrt om) by (apply sqrt_le_1_alt; lra).
    assert (E : sqrt (1 / 4) = 1 / 2).
    { replace (1 / 4) with (1 / 2 * (1 / 2)) by lra. apply sqrt_square. lra. }
    rewrite E in Hq. exact Hq. }
  assert (HD : exb (k1 +f fsqrt (k1 -f (sf *f sf *f xuf))) (rndF (1 + rs)) 2) by lift_to.
  set (D := rndF (1 + rs)) in *.
  assert (HD1 : 1 <= D).
  { apply rnd_ge_fmt; [exact fmtF_one | lra]. }
  assert (Hphi0 : 0 <= rndF (rndF (bs / (2 * xs)) + rndF (hk / D))).
  { apply phi_nonneg; [ | exact Hbs0 | exact Hc | | exact Hxs1 | exact HD1].
    - rewrite <- (exb_val _ _ _ Hhk). apply B_fmt.
    - pose proof (bpow_gt_0 radix2 (-19)). lra. }
  set (phi := rndF (rndF (bs / (2 * xs)) + rndF (hk / D))) in *.
  (* the divisors *)
  assert (Dx : divlow (2 * xs) 19).
  { pose proof (bpow_gt_0 radix2 (-19)). unfold divlow. rewrite Rabs_pos_eq by lra. bnum. bnum_in Hxs0. lra. }
  assert (Dr : divlow rs 1).
  { unfold divlow. rewrite Rabs_pos_eq by lra. bnum. lra. }
  assert (H2x : exb (k2 *f (sf *f sf *f xuf)) (2 * xs) 1) by (eapply exb_weak; [apply (exb_double _ _ 0 Hxs); unfold cl; lia | unfold cl; lia]).
  assert (Hphik : exb (bsf /f (k2 *f (sf *f sf *f xuf)) +f hkf /f (k1 +f fsqrt (k1 -f (sf *f sf *f xuf)))) phi 40).
  { unfold phi. eapply exb_weak.
    - eapply exb_add.
      + eapply exb_div; [exact Hbs | exact H2x | unfold cl; lia | exact Dx | unfold cl; lia].
      + eapply exb_div_one; [exact Hhk | exact HD | unfold cl; lia | rewrite Rabs_pos_eq by lra; lra | unfold cl; lia].
      + unfold cl; lia.
    - unfold cl; lia. }
  assert (Hhw : exb (sf /f k4) (s / 4) 0).
  { eapply exb_weak; [apply (exb_quarter sf s 0 Hs); [right | unfold cl; lia] | unfold cl; lia].
    rewrite Rabs_pos_eq by lra.
    assert (bpow radix2 (-1000) <= bpow radix2 (-9)) by (apply bpow_le; lia).
    assert (bpow radix2 (-9) = 1 / 512) by (bnum; lra). lra. }
  unfold node_value, integrand_term. cbv zeta.
  destruct (Rlt_dec phi 700) as [Hlt | Hge].
  - assert (Hk : flt (bsf /f (k2 *f (sf *f sf *f xuf)) +f hkf /f (k1 +f fsqrt (k1 -f (sf *f sf *f xuf)))) kphi_cutoff = true).
    { apply flt_iff; [exact (exb_fin _ _ _ Hphik) | exact (proj1 exb_kphi_cutoff) |]. rewrite (exb_val _ _ _ Hphik), (proj1 (proj2 exb_kphi_cutoff)). exact Hlt. }
    rewrite Hk. lift_to.
  - assert (Hk : flt (bsf /f (k2 *f (sf *f sf *f xuf)) +f hkf /f (k1 +f fsqrt (k1 -f (sf *f sf *f xuf)))) kphi_cutoff = false).
    { destruct (flt (bsf /f (k2 *f (sf *f sf *f xuf)) +f hkf /f (k1 +f fsqrt (k1 -f (sf *f sf *f xuf)))) kphi_cutoff) eqn:E; [| reflexivity].
      exfalso. apply Hge. apply (flt_iff _ _ (exb_fin _ _ _ Hphik) (proj1 exb_kphi_cutoff)) in E.
      rewrite (exb_val _ _ _ Hphik), (proj1 (proj2 exb_kphi_cutoff)) in E. exact E. }
    rewrite Hk. eapply exb_weak.
    + eapply exb_cong; [eapply exb_mul; [exact Hhw | exact exb_k0 | cl_side] |].
      rewrite Rmult_0_r. apply round_0. exact _.
    + cl_side.
Qed.
End HighNode.

Section ClosedForm.
Variables (L : lib) (expT nc : R -> R).
Hypotheses (Hexp : lib_exp_rel L expT 1 2) (Hnc : lib_ncdf_rel L nc).

(** Genz's closed form on the last scale: the kernel's [closed_form] is the proof's
    [closed_k]. Its two exponent arguments are halves, [rnd (-x / 2)], which the
    proof writes [-(x / 2)]: the two are one number unless [x] is a nonzero binary64
    below [2^-1000] in magnitude, where the halving rounds (by under [2^-1075], and
    [exp] of so small an argument is 1 either way); the hypotheses [Hh1] and [Hh2]
    exclude that case, and are the only inputs on which the kernel and the proof's
    function are not proved equal. *)
Lemma closed_form_ok sf bsf hkf s bs hk :
  exb sf s 0 -> 1 / 10 ^ 8 <= s -> s <= 3 / 1000 ->
  exb bsf bs 0 -> 0 <= bs -> bs <= 4001 / 10 * (s * s) ->
  exb hkf hk 11 -> - (4 * hk) <= bs -> hk < 1400 ->
  (rndF (rndF (bs / rndF (s * s)) + hk) = 0 \/ bpow radix2 (-1000) <= Rabs (rndF (rndF (bs / rndF (s * s)) + hk))) ->
  (hk = 0 \/ bpow radix2 (-1000) <= Rabs hk) ->
  flt (fsqrt bsf) (k20 *f sf) = true ->
  exists E, exb (closed_form L sf bsf hkf) (closed_k expT sqrtF nc s bs hk) E.
Proof.
  intros Hs Hs0 Hs1 Hbs Hbs0 Hbs1 Hhk Hc Hk1400 Hh1 Hh2 Hg.
  unfold closed_k. rnd2F.
  assert (Hss : s * s <= 9 / 1000000) by nra.
  assert (Hss0 : 1 / 10 ^ 16 <= s * s) by nra.
  assert (Hass : exb (sf *f sf) (rndF (s * s)) 0) by lift_to.
  set (ass := rndF (s * s)) in *.
  assert (Hass0 : bpow radix2 (-54) <= ass).
  { apply rnd_ge_fmt; [apply fmtF_bpow; lia |]. bnum. lra. }
  assert (Hass1 : ass <= 1 / 4).
  { apply rnd_le_fmt; [exact fmtF_quarter | lra]. }
  assert (Dass : divlow ass 54).
  { pose proof (bpow_gt_0 radix2 (-54)). unfold divlow. rewrite Rabs_pos_eq by lra. exact Hass0. }
  assert (Ds : divlow s 27).
  { unfold divlow. pose proof (bpow_gt_0 radix2 (-27)). rewrite Rabs_pos_eq by (bnum_in Hs0; lra). bnum. bnum_in Hs0. lra. }
  assert (Fhk : fmtF hk) by (rewrite <- (exb_val _ _ _ Hhk); apply B_fmt).
  (* c, d, w, x, p1, p2 *)
  assert (Hcc : exb (gen_c hkf) (rndF (rndF (4 - hk) / 8)) 12).
  { unfold gen_c. lift_to. }
  set (c := rndF (rndF (4 - hk) / 8)) in *.
  assert (Hdd : exb (gen_d hkf) (rndF (rndF (12 - hk) / 16)) 12).
  { unfold gen_d. lift_to. }
  set (d := rndF (rndF (12 - hk) / 16)) in *.
  assert (Hww : exb (gen_w (gen_d hkf) bsf) (rndF (1 - rndF (rndF (d * bs) / 5))) 13).
  { unfold gen_w. lift_to. }
  set (w := rndF (1 - rndF (rndF (d * bs) / 5))) in *.
  assert (Hxx : exb (gen_x (gen_c hkf) bsf (sf *f sf) (gen_w (gen_d hkf) bsf))
                    (rndF (rndF (rndF (c * rndF (bs - ass)) * w) / 3)) 27).
  { unfold gen_x. lift_to. }
  set (x := rndF (rndF (rndF (c * rndF (bs - ass)) * w) / 3)) in *.
  assert (Hp1 : exb (gen_p1 (gen_c hkf) (gen_d hkf) (sf *f sf)
                      (gen_x (gen_c hkf) bsf (sf *f sf) (gen_w (gen_d hkf) bsf)))
                    (rndF (rndF (1 - x) + rndF (rndF (rndF (rndF (c * d) * ass) * ass) / 5))) 29).
  { unfold gen_p1. lift_to. }
  set (p1 := rndF (rndF (1 - x) + rndF (rndF (rndF (rndF (c * d) * ass) * ass) / 5))) in *.
  assert (Hp2 : exb (gen_p2 (gen_c hkf) bsf (gen_w (gen_d hkf) bsf))
                    (rndF (1 - rndF (rndF (rndF (c * bs) * w) / 3))) 27).
  { unfold gen_p2. lift_to. }
  set (p2 := rndF (1 - rndF (rndF (rndF (c * bs) * w) / 3))) in *.
  (* the exponent arguments *)
  assert (Hq : exb (bsf /f (sf *f sf)) (rndF (bs / ass)) 54).
  { lift_to. }
  assert (Hsg : exb (bsf /f (sf *f sf) +f hkf) (rndF (rndF (bs / ass) + hk)) 55).
  { lift_to. }
  set (sg := rndF (rndF (bs / ass) + hk)) in *.
  assert (Hsg0 : 0 <= sg).
  { apply sum_nonneg; [exact Fhk | exact Hbs0 | exact Hc | | exact Hass1]. eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hass0]. }
  assert (Hh1' : exb (fneg (bsf /f (sf *f sf) +f hkf) /f k2) (- (sg / 2)) 55).
  { eapply exb_cong; [ | apply Ropp_div].
    eapply exb_weak; [apply (exb_half _ _ 55 (exb_neg _ _ _ Hsg)); [ | unfold cl; lia] | unfold cl; lia].
    destruct Hh1 as [H | H]; [left; rewrite H; ring | right; rewrite Rabs_Ropp; exact H]. }
  assert (Hh2' : exb (fneg hkf /f k2) (- (hk / 2)) 11).
  { eapply exb_cong; [ | apply Ropp_div].
    eapply exb_weak; [apply (exb_half _ _ 11 (exb_neg _ _ _ Hhk)); [ | unfold cl; lia] | unfold cl; lia].
    destruct Hh2 as [H | H]; [left; rewrite H; ring | right; rewrite Rabs_Ropp; exact H]. }
  assert (Hhklo : - 1 <= hk) by nra.
  assert (Hb : exb (fsqrt bsf) (sqrtF bs) 0).
  { unfold sqrtF. eapply exb_weak; [eapply exb_sqrt; [exact Hbs | exact Hbs0 | lia] | lia]. }
  assert (He1 : exb (lib_exp L (fneg (bsf /f (sf *f sf) +f hkf) /f k2)) (expT (- (sg / 2))) 2).
  { eapply exb_lib_exp; [exact Hexp | exact Hh1' | lra]. }
  assert (He2 : exb (lib_exp L (fneg hkf /f k2)) (expT (- (hk / 2))) 2).
  { eapply exb_lib_exp; [exact Hexp | exact Hh2' | lra]. }
  assert (Hv : exb (fneg (fsqrt bsf) /f sf) (rndF (- sqrtF bs / s)) 27) by lift_to.
  assert (Hnn : exb (lib_norm_cdf L (fneg (fsqrt bsf) /f sf)) (nc (rndF (- sqrtF bs / s))) 0).
  { eapply exb_lib_ncdf; [exact Hnc | exact Hv]. }
  unfold closed_form. rewrite Hg. cbv zeta. unfold SQRT_TAU.
  eexists. lift.
Qed.
End ClosedForm.

(** The proof's two-sum, taken as exact ([Hts] of BvnHighSum.v, BvnHighJ2.v), which
    [two_sum_ieee] establishes for the kernel's [two_sum64] on these operands. *)
Definition ts_ideal (a b : R) : R * R := (rnd (a + b), a + b - rnd (a + b)).

Lemma ts_ideal_spec : forall a b, fst (ts_ideal a b) = rnd (a + b) /\ fst (ts_ideal a b) + snd (ts_ideal a b) = a + b.
Proof. intros a b. unfold ts_ideal. cbn [fst snd]. split; [reflexivity | ring]. Qed.

(** The panels' accumulation: the kernel's fold over a panel's nodes is the proof's
    [dwsum] over their terms. The running words' bounds grow by [2^5] per term,
    only to exclude overflow. *)
Section PanelFold.
Variables (L : lib) (hw s2 bs hk : f64) (Et : Z).

Definition value_rel (xw : f64 * f64) (t : R) : Prop :=
  exb (node_value L hw s2 (fst xw) (snd xw) bs hk) t Et.

Lemma panel_fold_ok nds ts : Forall2 value_rel nds ts -> forall hi lo rh rl E,
  exb hi rh E -> exb lo rl E -> (Et <= E)%Z -> (1 <= E)%Z -> (E + Z.of_nat (length nds) <= 900)%Z ->
  exb (fst (fold_left (panel_step L hw s2 bs hk) nds (hi, lo))) (fst (dwsum ts_ideal rh rl ts)) (E + Z.of_nat (length nds))
  /\ exb (snd (fold_left (panel_step L hw s2 bs hk) nds (hi, lo))) (snd (dwsum ts_ideal rh rl ts)) (E + Z.of_nat (length nds)).
Proof.
  intros HF. induction HF as [| xw t nds ts Hn Hrest IH]; intros hi lo rh rl E Hh Hl HEt HE1 HE.
  - simpl. split; (eapply exb_weak; [eassumption | simpl; lia]).
  - cbn [fold_left dwsum length].
    cbn [length] in HE. rewrite Nat2Z.inj_succ in HE.
    unfold value_rel in Hn.
    set (term := node_value L hw s2 (fst xw) (snd xw) bs hk) in *.
    destruct (exb_two_sum_ideal hi term rh t E Hh (exb_weak _ _ _ E Hn HEt) ltac:(lia)) as [Hs He].
    assert (Hlow : exb (lo +f snd (two_sum64 hi term)) (rndF (rl + (rh + t - rndF (rh + t)))) (E + 1)).
    { eapply exb_weak; [apply (exb_add lo _ rl _ E E Hl He ltac:(unfold cl; lia)) | unfold cl; lia]. }
    assert (Hstep : panel_step L hw s2 bs hk (hi, lo) xw = (let '(sum, err) := two_sum64 hi term in (sum, lo +f err))) by reflexivity.
    rewrite Hstep.
    revert Hs Hlow. generalize (two_sum64 hi term) as q. intros [sq eq] Hs Hlow. cbn [fst snd] in Hs, Hlow |- .
    pose proof (IH sq (lo +f eq) (rndF (rh + t)) (rndF (rl + (rh + t - rndF (rh + t)))) (E + 1)%Z Hs Hlow ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
    replace (E + Z.of_nat (S (length nds)))%Z with (E + 1 + Z.of_nat (length nds))%Z by (rewrite Nat2Z.inj_succ; ring).
    split; (eapply exb_cong; [eassumption | reflexivity]).
Qed.
End PanelFold.

(** The clamp, as the proof writes it. *)
Lemma clamp_alt y : clamp y = Rmin 1 (Rmax 0 y).
Proof.
  unfold clamp.
  destruct (Rle_dec y 0) as [H0 | H0].
  - rewrite (Rmin_right 1 y) by lra. rewrite (Rmax_left 0 y) by lra. rewrite (Rmin_right 1 0) by lra. reflexivity.
  - destruct (Rle_dec 1 y) as [H1 | H1].
    + rewrite (Rmin_left 1 y) by lra. rewrite (Rmax_right 0 y) by lra. rewrite (Rmax_right 0 1) by lra. rewrite (Rmin_left 1 y) by lra. reflexivity.
    + rewrite (Rmin_right 1 y) by lra. rewrite (Rmax_right 0 y) by lra. rewrite (Rmin_right 1 y) by lra. reflexivity.
Qed.

Lemma exb_clamp_hi a r E : exb a r E -> exb (clamp_to_probability a) (clamp r) 0.
Proof. intros H. rewrite clamp_alt. exact (exb_clamp a r E H). Qed.

Lemma exb_fmax a b ra rb E : exb a ra E -> exb b rb E -> exb (fmax a b) (B (fmax a b)) E.
Proof.
  intros Ha Hb. unfold fmax. destruct (flt a b).
  - rewrite (exb_val _ _ _ Hb). exact Hb.
  - rewrite (exb_val _ _ _ Ha). exact Ha.
Qed.

Section HighFinish.
Variables (L : lib) (nc : R -> R).
Hypothesis Hnc : lib_ncdf_rel L nc.

(** [rho > 0]: [clamp (rnd (rnd (-Jk / TAU) + nc xm))] ([high_pos_end], BvnHighEnd.v). *)
Lemma high_finish_pos dhf dkf rhof bvnf dh dk Jk E :
  exb bvnf Jk E -> (0 <= E <= 500)%Z -> exb dhf dh 6 -> exb dkf dk 6 -> fgt rhof k0 = true ->
  exb (high_finish L dhf dkf rhof bvnf)
      (clamp (rnd (rnd (- Jk / TAU) + nc (- B (fmax dhf dkf))))) 0.
Proof.
  intros Hj HE Hh Hk Hg.
  pose proof (exb_fmax _ _ _ _ _ Hh Hk) as Hm.
  unfold high_finish. rewrite Hg. rnd2F.
  eapply exb_clamp_hi. unfold TAU. lift.
Qed.

(** [rho < 0], [Phi(-dh) > Phi(dk)]: [g = - rnd (-Jk / TAU)] and the exact two-sum of the
    distribution functions ([high_neg_end_diff]). *)
Lemma high_finish_neg_diff dhf dkf rhof bvnf dh dk Jk E :
  exb bvnf Jk E -> (0 <= E <= 500)%Z -> exb dhf dh 6 -> exb dkf dk 6 -> fgt rhof k0 = false -> fgt (fneg dhf) dkf = true ->
  exb (high_finish L dhf dkf rhof bvnf)
      (clamp (rnd (fst (ts_ideal (nc (- dh)) (- nc dk)) +
                   rnd (snd (ts_ideal (nc (- dh)) (- nc dk)) + - rnd (- Jk / TAU))))) 0.
Proof.
  intros Hj HE Hh Hk Hg Hd.
  unfold high_finish. rewrite Hg, Hd.
  assert (Hn1 : exb (lib_norm_cdf L (fneg dhf)) (nc (- dh)) 0) by (eapply exb_lib_ncdf; [exact Hnc | apply exb_neg; exact Hh]).
  assert (Hn2 : exb (fneg (lib_norm_cdf L dkf)) (- nc dk) 0) by (apply exb_neg; eapply exb_lib_ncdf; [exact Hnc | exact Hk]).
  pose proof (exb_two_sum_ideal _ _ _ _ 0%Z Hn1 Hn2 ltac:(lia)) as [Hs He].
  revert Hs He. generalize (two_sum64 (lib_norm_cdf L (fneg dhf)) (fneg (lib_norm_cdf L dkf))) as p. intros [hi lo] Hs He.
  cbn [fst snd] in Hs, He |- .
  eapply exb_clamp_hi. rnd2F. unfold TAU, ts_ideal. cbn [fst snd]. rnd2F.
  lift.
Qed.

(** [rho < 0], [Phi(-dh) <= Phi(dk)]: [clamp (- rnd (-Jk / TAU))] ([high_neg_end_zero]). *)
Lemma high_finish_neg_zero dhf dkf rhof bvnf dh dk Jk E :
  exb bvnf Jk E -> (0 <= E <= 500)%Z -> exb dhf dh 6 -> exb dkf dk 6 -> fgt rhof k0 = false -> fgt (fneg dhf) dkf = false ->
  exb (high_finish L dhf dkf rhof bvnf) (clamp (- rnd (- Jk / TAU))) 0.
Proof.
  intros Hj HE Hh Hk Hg Hd.
  unfold high_finish. rewrite Hg, Hd. rnd2F.
  eapply exb_clamp_hi. unfold TAU. lift.
Qed.
End HighFinish.

(** [dwsum] over an appended list. *)
Lemma dwsum_app l1 l2 : forall hi lo,
  dwsum ts_ideal hi lo (l1 ++ l2) = let r := dwsum ts_ideal hi lo l1 in dwsum ts_ideal (fst r) (snd r) l2.
Proof.
  induction l1 as [| t l1 IH]; intros hi lo; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** The panels as the proof sees them: the [node_term] of each node of each panel, in
    order, the last scale, and the number of panels. A panel is taken while its scale
    exceeds [PANEL_FLOOR] ([kpanel_floor]), with 16 nodes above [0.095] and 15 below. *)
Definition rnodes (wide : bool) : list (R * R) :=
  map (fun xw => (B (fst xw), B (snd xw))) (panel_nodes (panel_rule_of wide)).

Fixpoint panel_terms (expT : R -> R) (fuel : nat) (s bs hk : R) : list R * R * nat :=
  match fuel with
  | O => ([], s, O)
  | S f =>
      if Rlt_dec (B kpanel_floor) s then
        let ts := map (fun xw => node_term expT sqrtF (rndF (s * s)) (fst xw) (snd xw) bs hk (s / 4))
                      (rnodes (if Rlt_dec (B kpanel_wide) s then true else false)) in
        let '(rest, sl, p) := panel_terms expT f (s / 2) bs hk in (ts ++ rest, sl, S p)
      else ([], s, O)
  end.

Lemma rnodes_len wide : (length (rnodes wide) <= 16)%nat.
Proof. unfold rnodes. rewrite map_length. destruct wide; vm_compute; repeat constructor. Qed.

Section Panels.
Variables (L : lib) (expT : R -> R).
Hypothesis Hexp : lib_exp_rel L expT 1 2.
Variables (bsf hkf : f64) (bs hk : R).
Hypotheses (Hbs : exb bsf bs 14) (Hbs0 : 0 <= bs) (Hhk : exb hkf hk 11) (Hc : - (4 * hk) <= bs).

(** A panel's nodes: each [node_value] is the proof's [node_term]. *)
Lemma values_ok sf s nds : exb sf s 0 -> 3 / 1000 < s -> s <= 381 / 1000 ->
  Forall (fun xw => fin_range (1 / 4) 1 (fst xw) /\ fin_range 0 1 (snd xw)) nds ->
  Forall2 (value_rel L (sf /f k4) (sf *f sf) bsf hkf 3) nds
    (map (fun xw => node_term expT sqrtF (rndF (s * s)) (B (fst xw)) (B (snd xw)) bs hk (s / 4)) nds).
Proof.
  intros Hs Hs0 Hs1 HF. induction HF as [| xw nds [[Fx [Hx0 Hx1]] [Fw [Hw0 Hw1]]] Hr IH]; simpl.
  - constructor.
  - constructor; [| exact IH].
    unfold value_rel.
    assert (Hxe : exb (fst xw) (B (fst xw)) 0).
    { split; [exact Fx | split; [reflexivity | rewrite Rabs_pos_eq by lra; change (bpow radix2 0) with 1; exact Hx1]]. }
    assert (Hwe : exb (snd xw) (B (snd xw)) 0).
    { split; [exact Fw | split; [reflexivity | rewrite Rabs_pos_eq by lra; change (bpow radix2 0) with 1; exact Hw1]]. }
    exact (node_value_ok L expT Hexp sf (fst xw) (snd xw) bsf hkf s (B (fst xw)) (B (snd xw)) bs hk
             Hs Hs0 Hs1 Hxe Hx0 Hx1 Hwe Hbs Hbs0 Hhk Hc).
Qed.
(** The loop of panels: the kernel's [panel_sum] is the proof's [dwsum] over the panels'
    [node_term]s, [panel_terms], and ends at the same last scale. [j] is the number of
    halvings so far, so the scale times [2^j] stays at most [0.381] and at most seven
    panels (112 nodes) run; the bounds on the running words grow by [2^1] per node and
    exist to exclude overflow. *)
Lemma panel_sum_ok fuel : forall j sf s hi lo rh rl E,
  exb sf s 0 -> 0 < s -> s * bpow radix2 (Z.of_nat j) <= 381 / 1000 ->
  exb hi rh E -> exb lo rl E -> (3 <= E)%Z -> (E + 16 * Z.max 0 (7 - Z.of_nat j) <= 850)%Z ->
  let '(l, sl, p) := panel_terms expT fuel s bs hk in
  exb (fst (fst (panel_sum L fuel sf bsf hkf hi lo))) (fst (dwsum ts_ideal rh rl l)) (E + Z.of_nat (length l))
  /\ exb (snd (fst (panel_sum L fuel sf bsf hkf hi lo))) (snd (dwsum ts_ideal rh rl l)) (E + Z.of_nat (length l))
  /\ exb (snd (panel_sum L fuel sf bsf hkf hi lo)) sl 0
  /\ (Z.of_nat p + Z.of_nat j <= Z.max 7 (Z.of_nat j))%Z /\ (length l <= 16 * p)%nat.
Proof.
  induction fuel as [| f IH]; intros j sf s hi lo rh rl E Hs Hs0 Hsj Hh Hl HE3 HEb.
  - cbn [panel_terms panel_sum]. cbn [fst snd length]. refine (conj _ (conj _ (conj _ (conj _ _)))).
    + refine (exb_weak _ _ _ _ Hh _). simpl; lia.
    + refine (exb_weak _ _ _ _ Hl _). simpl; lia.
    + exact Hs.
    + lia.
    + lia.
  - cbn [panel_terms panel_sum].
    destruct (Rlt_dec (B kpanel_floor) s) as [Hf | Hf].
    + (* a panel is taken *)
      assert (Hflo : (3 / 1000 < B kpanel_floor)).
      { rewrite (proj1 (proj2 exb_kpanel_floor)). lra. }
      assert (Hgt : fgt sf kpanel_floor = true).
      { apply (fgt_iff sf kpanel_floor (exb_fin _ _ _ Hs) (proj1 exb_kpanel_floor)).
        rewrite (exb_val _ _ _ Hs). exact Hf. }
      rewrite Hgt.
      assert (Hj6 : (Z.of_nat j <= 6)%Z).
      { destruct (Z_le_gt_dec (Z.of_nat j) 6) as [A | A]; [exact A |].
        exfalso. assert (bpow radix2 7 <= bpow radix2 (Z.of_nat j)) by (apply bpow_le; lia).
        assert (bpow radix2 7 = 128) by (bnum; lra).
        assert (3 / 1000 < s) by lra. nra. }
      assert (Hs1 : s <= 381 / 1000).
      { assert (1 <= bpow radix2 (Z.of_nat j)) by (replace 1 with (bpow radix2 0) by reflexivity; apply bpow_le; lia). nra. }
      set (wide := if Rlt_dec (B kpanel_wide) s then true else false).
      assert (Hwide : fgt sf kpanel_wide = wide).
      { unfold wide. destruct (Rlt_dec (B kpanel_wide) s) as [Hw | Hw].
        - apply (fgt_iff sf kpanel_wide (exb_fin _ _ _ Hs) (proj1 exb_kpanel_wide)). rewrite (exb_val _ _ _ Hs). exact Hw.
        - destruct (fgt sf kpanel_wide) eqn:Eq1; [| reflexivity]. exfalso. apply Hw.
          apply (fgt_iff sf kpanel_wide (exb_fin _ _ _ Hs) (proj1 exb_kpanel_wide)) in Eq1.
          rewrite (exb_val _ _ _ Hs) in Eq1. exact Eq1. }
      assert (Hrule : panel_rule sf = panel_rule_of wide) by (unfold panel_rule; rewrite Hwide; reflexivity).
      rewrite Hrule.
      pose proof (rnodes_len wide) as Hn16. unfold rnodes in Hn16. rewrite map_length in Hn16.
      assert (Hn16z : (Z.of_nat (length (panel_nodes (panel_rule_of wide))) <= 16)%Z) by exact (proj1 (Nat2Z.inj_le _ 16) Hn16).
      pose proof (values_ok sf s (panel_nodes (panel_rule_of wide)) Hs ltac:(lra) Hs1 (panel_nodes_ok wide)) as Hvals.
      pose proof (panel_fold_ok L (sf /f k4) (sf *f sf) bsf hkf 3 (panel_nodes (panel_rule_of wide))
        (map (fun xw => node_term expT sqrtF (rndF (s * s)) (B (fst xw)) (B (snd xw)) bs hk (s / 4)) (panel_nodes (panel_rule_of wide)))
        Hvals hi lo rh rl E Hh Hl ltac:(lia) ltac:(lia)
        ltac:(assert (0 <= 16 * Z.max 0 (7 - Z.of_nat j))%Z by lia; lia))
        as [Fh Fl].
      revert Fh Fl.
      generalize (fold_left (panel_step L (sf /f k4) (sf *f sf) bsf hkf) (panel_nodes (panel_rule_of wide)) (hi, lo)) as q.
      intros [hq lq] Fh Fl. cbn [fst snd] in Fh, Fl.
      set (nds := panel_nodes (panel_rule_of wide)) in *.
      set (ts := map (fun xw => node_term expT sqrtF (rndF (s * s)) (B (fst xw)) (B (snd xw)) bs hk (s / 4)) nds) in *.
      assert (Hhalf : exb (sf /f k2) (s / 2) 0).
      { eapply exb_weak; [apply (exb_half sf s 0 Hs); [right | unfold cl; lia] | unfold cl; lia].
        rewrite Rabs_pos_eq by lra.
        assert (bpow radix2 (-1000) <= bpow radix2 (-9)) by (apply bpow_le; lia).
        assert (bpow radix2 (-9) = 1 / 512) by (bnum; lra). lra. }
      set (r := dwsum ts_ideal rh rl ts) in *.
      pose proof (IH (S j) (sf /f k2) (s / 2) hq lq (fst r) (snd r) (E + Z.of_nat (length nds))%Z Hhalf ltac:(lra)
        ltac:(replace (Z.of_nat (S j)) with (Z.of_nat j + 1)%Z by lia; rewrite bpow_plus; change (bpow radix2 1) with 2; nra)
        Fh Fl ltac:(lia)
        ltac:(rewrite Nat2Z.inj_succ; lia))
        as IHr.
      destruct (panel_terms expT f (s / 2) bs hk) as [[rest sl] p] eqn:Ept.
      cbn [fst snd] in IHr |- *.
      destruct IHr as [I1 [I2 [I3 [I4 I5]]]].
      assert (Hmap : map (fun xw => node_term expT sqrtF (rndF (s * s)) (fst xw) (snd xw) bs hk (s / 4)) (rnodes wide) = ts)
        by (unfold ts, rnodes, nds; rewrite map_map; reflexivity).
      rewrite Hmap. rewrite dwsum_app. cbn [length]. rewrite app_length. cbn [fst snd].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * replace (E + Z.of_nat (length ts + length rest))%Z with (E + Z.of_nat (length nds) + Z.of_nat (length rest))%Z.
        -- exact I1.
        -- rewrite Nat2Z.inj_add. assert (length ts = length nds) by (unfold ts; apply map_length). rewrite H. ring.
      * replace (E + Z.of_nat (length ts + length rest))%Z with (E + Z.of_nat (length nds) + Z.of_nat (length rest))%Z.
        -- exact I2.
        -- rewrite Nat2Z.inj_add. assert (length ts = length nds) by (unfold ts; apply map_length). rewrite H. ring.
      * exact I3.
      * rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_succ in I4. lia.
      * assert (length ts = length nds) by (unfold ts; apply map_length). lia.
    + (* the loop ends *)
      assert (Hng : fgt sf kpanel_floor = false).
      { destruct (fgt sf kpanel_floor) eqn:Eq2; [| reflexivity]. exfalso. apply Hf.
        apply (fgt_iff sf kpanel_floor (exb_fin _ _ _ Hs) (proj1 exb_kpanel_floor)) in Eq2.
        rewrite (exb_val _ _ _ Hs) in Eq2. exact Eq2. }
      rewrite Hng. cbn [fst snd length]. refine (conj _ (conj _ (conj _ (conj _ _)))).
      * refine (exb_weak _ _ _ _ Hh _). simpl; lia.
      * refine (exb_weak _ _ _ _ Hl _). simpl; lia.
      * exact Hs.
      * lia.
      * lia.
Qed.
(** The branch's integral: the kernel's [high_integral] is [rnd (Cl + rnd (Pw + Pl))] for
    the panels' double-word [(Pw, Pl) = dwsum ts 0 0 l] and [Cl] the closed form on the
    last scale ([J_bound], BvnHighJ2.v), the scale [a] being [sqrtF (ass_k |rho|)]. *)
Lemma high_integral_ok rhof rho Cl Ec :
  exb rhof rho 0 -> Rabs rho <= 1 ->
  flt hkf khk_cutoff = true ->
  0 < sqrtF (ass_k (Rabs rho)) -> sqrtF (ass_k (Rabs rho)) <= 381 / 1000 ->
  (forall h l s, panel_sum L 64 (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof))) bsf hkf k0 k0 = (h, l, s) ->
     exb (closed_form L s bsf hkf) Cl Ec) -> (0 <= Ec <= 100)%Z ->
  let '(l, sl, p) := panel_terms expT 64 (sqrtF (ass_k (Rabs rho))) bs hk in
  exb (high_integral L hkf bsf rhof)
      (rnd (Cl + rnd (fst (dwsum ts_ideal 0 0 l) + snd (dwsum ts_ideal 0 0 l)))) 130.
Proof.
  intros Hr Hr1 Hflt Ha0 Ha1 Hcl HEc.
  assert (Hass : exb ((k1 -f fabs rhof) *f (k1 +f fabs rhof)) (ass_k (Rabs rho)) 2).
  { unfold ass_k. rnd2F. lift_to. }
  assert (Hass0 : 0 <= ass_k (Rabs rho)).
  { pose proof (Rabs_pos rho). unfold ass_k. rnd2F.
    apply rnd_nonneg0. apply Rmult_le_pos; apply rnd_nonneg0; lra. }
  assert (Ha : exb (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof))) (sqrtF (ass_k (Rabs rho))) 0).
  { assert (H2 : exb (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof))) (sqrtF (ass_k (Rabs rho))) 2).
    { unfold sqrtF. apply exb_sqrt; [exact Hass | exact Hass0 | lia]. }
    eapply exb_tight; [exact H2 |]. rewrite Rabs_pos_eq by lra. change (bpow radix2 0) with 1. lra. }
  unfold high_integral. rewrite Hflt. cbv zeta.
  pose proof (panel_sum_ok 64%nat 0%nat (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof))) (sqrtF (ass_k (Rabs rho))) k0 k0 0 0 3%Z
    Ha Ha0 ltac:(simpl; lra) ltac:(eapply exb_weak; [exact exb_k0 | lia]) ltac:(eapply exb_weak; [exact exb_k0 | lia]) ltac:(lia) ltac:(simpl; lia)) as Hps.
  destruct (panel_terms expT 64 (sqrtF (ass_k (Rabs rho))) bs hk) as [[l sl] p] eqn:Ept.
  destruct Hps as [P1 [P2 [P3 [P4 P5]]]].
  revert P1 P2 P3 Hcl. generalize (panel_sum L 64 (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof))) bsf hkf k0 k0) as ps.
  intros [[h lw] sq] P1 P2 P3 Hcl. cbn [fst snd] in P1, P2, P3 |- .
  assert (Hlen : (Z.of_nat (length l) <= 112)%Z).
  { apply (inj_le _ _) in P5. rewrite Nat2Z.inj_mul in P5. lia. }
  rnd2F.
  eapply exb_weak.
  - eapply exb_add; [exact (Hcl h lw sq eq_refl) | | ].
    + eapply exb_add; [exact P1 | exact P2 | ].
      unfold cl. lia.
    + unfold cl. lia.
  - unfold cl. lia.
Qed.
End Panels.

(** The reflected thresholds' [hk] and [bs]. *)
Lemma geom_hk dhf dkf dh dk : exb dhf dh 6 -> exb dkf dk 6 -> Rabs dh <= 39 -> Rabs dk <= 39 ->
  exb (dhf *f dkf) (rndF (dh * dk)) 11.
Proof.
  intros Hh Hk H1 H2.
  assert (H12 : exb (dhf *f dkf) (rndF (dh * dk)) 12) by lift_to.
  eapply exb_tight; [exact H12 |].
  apply rnd_bound; [ | lia].
  rewrite Rabs_mult. assert (bpow radix2 11 = 2048) by (bnum; lra).
  pose proof (Rabs_pos dh). pose proof (Rabs_pos dk). nra.
Qed.

Lemma geom_bs_pos dhf dkf dh dk : exb dhf dh 6 -> exb dkf dk 6 ->
  exb ((dhf -f dkf) *f (dhf -f dkf)) (rndF (rndF (dh - dk) * rndF (dh - dk))) 14.
Proof. intros Hh Hk. lift_to. Qed.

Lemma geom_bs_neg dhf dkf dh dk : exb dhf dh 6 -> exb dkf dk 6 ->
  exb ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (rndF (rndF (dh - - dk) * rndF (dh - - dk))) 14.
Proof. intros Hh Hk. lift_to. Qed.

Section HighCorrelation.
Variables (L : lib) (nc : R -> R).
Hypothesis Hnc : lib_ncdf_rel L nc.

(** [rho > 0] ([high_pos_end], BvnHighEnd.v). *)
Lemma high_corr_pos dhf dkf rhof dh dk Jk E :
  flt rhof k0 = false -> fgt rhof k0 = true -> exb dhf dh 6 -> exb dkf dk 6 ->
  exb (high_integral L (dhf *f dkf) ((dhf -f dkf) *f (dhf -f dkf)) rhof) Jk E -> (0 <= E <= 500)%Z ->
  exb (high_correlation L dhf dkf rhof)
      (clamp (rnd (rnd (- Jk / TAU) + nc (- B (fmax dhf dkf))))) 0.
Proof.
  intros Hn Hp Hh Hk HJ HE. unfold high_correlation. rewrite Hn. cbv zeta.
  exact (high_finish_pos L nc Hnc dhf dkf rhof _ dh dk Jk E HJ HE Hh Hk Hp).
Qed.

(** [rho < 0], [Phi(-dh) > Phi(dk)] ([high_neg_end_diff]). *)
Lemma high_corr_neg_diff dhf dkf rhof dh dk Jk E :
  flt rhof k0 = true -> fgt rhof k0 = false -> fgt (fneg dhf) dkf = true -> exb dhf dh 6 -> exb dkf dk 6 ->
  exb (high_integral L (fneg (dhf *f dkf)) ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) rhof) Jk E -> (0 <= E <= 500)%Z ->
  exb (high_correlation L dhf dkf rhof)
      (clamp (rnd (fst (ts_ideal (nc (- dh)) (- nc dk)) +
                   rnd (snd (ts_ideal (nc (- dh)) (- nc dk)) + - rnd (- Jk / TAU))))) 0.
Proof.
  intros Hn Hp Hd Hh Hk HJ HE. unfold high_correlation. rewrite Hn. cbv zeta.
  exact (high_finish_neg_diff L nc Hnc dhf dkf rhof _ dh dk Jk E HJ HE Hh Hk Hp Hd).
Qed.

(** [rho < 0], [Phi(-dh) <= Phi(dk)] ([high_neg_end_zero]). *)
Lemma high_corr_neg_zero dhf dkf rhof dh dk Jk E :
  flt rhof k0 = true -> fgt rhof k0 = false -> fgt (fneg dhf) dkf = false -> exb dhf dh 6 -> exb dkf dk 6 ->
  exb (high_integral L (fneg (dhf *f dkf)) ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) rhof) Jk E -> (0 <= E <= 500)%Z ->
  exb (high_correlation L dhf dkf rhof) (clamp (- rnd (- Jk / TAU))) 0.
Proof.
  intros Hn Hp Hd Hh Hk HJ HE. unfold high_correlation. rewrite Hn. cbv zeta.
  exact (high_finish_neg_zero L dhf dkf rhof _ dh dk Jk E HJ HE Hh Hk Hp Hd).
Qed.
End HighCorrelation.

(** The whole high branch for [rho > 0]: the kernel's [high_correlation] is the proof's
    [clamp (rnd (rnd (-J / TAU) + nc xm))] ([high_pos_end]), with [J = rnd (Cl + rnd (Pw + Pl))] the
    integral of [J_bound] over the panels [panel_terms] and the closed form [Cl] on the
    last scale. The hypotheses are the ranges the proofs give: the thresholds below 39, the
    correlation's [a], the computed [bs] and [hk] satisfying [-(4 hk) <= bs] (their geometry),
    [hk] below the cutoff, and the closed form's inputs at the last scale ([Hcl]). *)
Theorem high_pos_composite (L : lib) (expT nc : R -> R)
  (Hexp : lib_exp_rel L expT 1 2) (Hnc : lib_ncdf_rel L nc)
  (dhf dkf rhof : f64) (dh dk rho Cl : R) (Ec : Z) :
  exb dhf dh 6 -> exb dkf dk 6 -> Rabs dh <= 39 -> Rabs dk <= 39 ->
  exb rhof rho 0 -> Rabs rho <= 1 -> flt rhof k0 = false -> fgt rhof k0 = true ->
  flt (dhf *f dkf) khk_cutoff = true ->
  - (4 * rndF (dh * dk)) <= rndF (rndF (dh - dk) * rndF (dh - dk)) ->
  0 < sqrtF (ass_k (Rabs rho)) -> sqrtF (ass_k (Rabs rho)) <= 381 / 1000 ->
  (forall h l s, panel_sum L 64 (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof)))
       ((dhf -f dkf) *f (dhf -f dkf)) (dhf *f dkf) k0 k0 = (h, l, s) ->
     exb (closed_form L s ((dhf -f dkf) *f (dhf -f dkf)) (dhf *f dkf)) Cl Ec) -> (0 <= Ec <= 100)%Z ->
  let '(l, sl, p) := panel_terms expT 64 (sqrtF (ass_k (Rabs rho)))
                       (rndF (rndF (dh - dk) * rndF (dh - dk))) (rndF (dh * dk)) in
  exb (high_correlation L dhf dkf rhof)
      (clamp (rnd (rnd (- (rnd (Cl + rnd (fst (dwsum ts_ideal 0 0 l) + snd (dwsum ts_ideal 0 0 l))))
                         / TAU) + nc (- B (fmax dhf dkf))))) 0.
Proof.
  intros Hh Hk Hb1 Hb2 Hr Hr1 Hn Hp Hcut Hc Ha0 Ha1 Hcl HEc.
  pose proof (geom_hk dhf dkf dh dk Hh Hk Hb1 Hb2) as Hhk.
  pose proof (geom_bs_pos dhf dkf dh dk Hh Hk) as Hbs.
  assert (Hbs0 : 0 <= rndF (rndF (dh - dk) * rndF (dh - dk))).
  { apply rnd_nonneg0. nra. }
  pose proof (high_integral_ok L expT Hexp ((dhf -f dkf) *f (dhf -f dkf)) (dhf *f dkf)
    (rndF (rndF (dh - dk) * rndF (dh - dk))) (rndF (dh * dk)) Hbs Hbs0 Hhk Hc rhof rho Cl Ec Hr Hr1 Hcut Ha0 Ha1 Hcl HEc) as HI.
  destruct (panel_terms expT 64 (sqrtF (ass_k (Rabs rho))) (rndF (rndF (dh - dk) * rndF (dh - dk))) (rndF (dh * dk)))
    as [[l sl] p] eqn:Ept.
  exact (high_corr_pos L nc Hnc dhf dkf rhof dh dk _ 130%Z Hn Hp Hh Hk HI ltac:(lia)).
Qed.

(** [rho < 0]: the same, for [Phi(-dh) > Phi(dk)] ([high_neg_end_diff]) and for
    [Phi(-dh) <= Phi(dk)] ([high_neg_end_zero]); the kernel reflects [k = -dk] and
    [hk = -(dh dk)]. *)
Section NegativeComposite.
Variables (L : lib) (expT nc : R -> R).
Hypotheses (Hexp : lib_exp_rel L expT 1 2) (Hnc : lib_ncdf_rel L nc).
Variables (dhf dkf rhof : f64) (dh dk rho Cl : R) (Ec : Z).
Hypotheses (Hh : exb dhf dh 6) (Hk : exb dkf dk 6) (Hb1 : Rabs dh <= 39) (Hb2 : Rabs dk <= 39)
  (Hr : exb rhof rho 0) (Hr1 : Rabs rho <= 1) (Hn : flt rhof k0 = true) (Hp : fgt rhof k0 = false)
  (Hcut : flt (fneg (dhf *f dkf)) khk_cutoff = true)
  (Hc : - (4 * - rndF (dh * dk)) <= rndF (rndF (dh - - dk) * rndF (dh - - dk)))
  (Ha0 : 0 < sqrtF (ass_k (Rabs rho))) (Ha1 : sqrtF (ass_k (Rabs rho)) <= 381 / 1000)
  (Hcl : forall h l s, panel_sum L 64 (fsqrt ((k1 -f fabs rhof) *f (k1 +f fabs rhof)))
       ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (fneg (dhf *f dkf)) k0 k0 = (h, l, s) ->
     exb (closed_form L s ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (fneg (dhf *f dkf))) Cl Ec)
  (HEc : (0 <= Ec <= 100)%Z).

Let Hhk : exb (fneg (dhf *f dkf)) (- rndF (dh * dk)) 11 := exb_neg _ _ _ (geom_hk dhf dkf dh dk Hh Hk Hb1 Hb2).
Let Hbs : exb ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (rndF (rndF (dh - - dk) * rndF (dh - - dk))) 14 :=
  geom_bs_neg dhf dkf dh dk Hh Hk.

Theorem high_neg_diff_composite :
  fgt (fneg dhf) dkf = true ->
  let '(l, sl, p) := panel_terms expT 64 (sqrtF (ass_k (Rabs rho)))
                       (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)) in
  exb (high_correlation L dhf dkf rhof)
      (clamp (rnd (fst (ts_ideal (nc (- dh)) (- nc dk)) +
                   rnd (snd (ts_ideal (nc (- dh)) (- nc dk)) +
                        - rnd (- (rnd (Cl + rnd (fst (dwsum ts_ideal 0 0 l) + snd (dwsum ts_ideal 0 0 l)))) / TAU))))) 0.
Proof.
  intros Hd.
  assert (Hbs0 : 0 <= rndF (rndF (dh - - dk) * rndF (dh - - dk))) by (apply rnd_nonneg0; nra).
  pose proof (high_integral_ok L expT Hexp ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (fneg (dhf *f dkf))
    (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)) Hbs Hbs0 Hhk Hc rhof rho Cl Ec Hr Hr1 Hcut Ha0 Ha1 Hcl HEc) as HI.
  destruct (panel_terms expT 64 (sqrtF (ass_k (Rabs rho))) (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)))
    as [[l sl] p] eqn:Ept.
  exact (high_corr_neg_diff L nc Hnc dhf dkf rhof dh dk _ 130%Z Hn Hp Hd Hh Hk HI ltac:(lia)).
Qed.

Theorem high_neg_zero_composite :
  fgt (fneg dhf) dkf = false ->
  let '(l, sl, p) := panel_terms expT 64 (sqrtF (ass_k (Rabs rho)))
                       (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)) in
  exb (high_correlation L dhf dkf rhof)
      (clamp (- rnd (- (rnd (Cl + rnd (fst (dwsum ts_ideal 0 0 l) + snd (dwsum ts_ideal 0 0 l)))) / TAU))) 0.
Proof.
  intros Hd.
  assert (Hbs0 : 0 <= rndF (rndF (dh - - dk) * rndF (dh - - dk))) by (apply rnd_nonneg0; nra).
  pose proof (high_integral_ok L expT Hexp ((dhf -f fneg dkf) *f (dhf -f fneg dkf)) (fneg (dhf *f dkf))
    (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)) Hbs Hbs0 Hhk Hc rhof rho Cl Ec Hr Hr1 Hcut Ha0 Ha1 Hcl HEc) as HI.
  destruct (panel_terms expT 64 (sqrtF (ass_k (Rabs rho))) (rndF (rndF (dh - - dk) * rndF (dh - - dk))) (- rndF (dh * dk)))
    as [[l sl] p] eqn:Ept.
  exact (high_corr_neg_zero L dhf dkf rhof dh dk _ 130%Z Hn Hp Hd Hh Hk HI ltac:(lia)).
Qed.
End NegativeComposite.
