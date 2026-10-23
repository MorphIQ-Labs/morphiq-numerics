(** The absolute error of the low-correlation branch, from the table of one
    rule: [|R - P| <= B] for the computed result [R] and
    [P = Phi(x) Phi(y) + (1/2 pi) int_0^{asin rho} f]. The library functions
    enter through their documented contracts, stated as hypotheses:

    - [exp_contract], [sin_contract] (BvnLow.v): [exp] is a rounding of a value
      within [2^-100] relatively of [e^v] (docs/exp.md proves correct rounding);
      [sin] is within [(1/2 + 2^-144)] ulp (docs/sin_cos.md, on [|theta| <= 2.5]);
    - the normal distribution function: a rounding of a value within [2^-112] of
      [Phi] (docs/normal.md, table of relative errors before the final rounding),
      so within [eP = 2^-54 + 2^-112] of [Phi] and in [[0, 1]];
    - [asin]: a rounding of a value within [2^-62] relatively of [asin rho]
      (docs/asin.md: fast path below [2^-63], accurate path [2^-124]);
    - Plackett: the exact value is a probability;
    - T1: the Gauss-Legendre remainder, the cited theorem of
      docs/bivariate_normal_truncation.md section 2. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnQuadG BvnTail BvnRule BvnIntegral BvnFinal.
Open Scope R_scope.

Definition Rhat (expI sinI : R -> R) (x y asr : R) (nodes : list NodeS) (pxI pyI : R) : R :=
  finish pxI pyI (fst (acc (map (tn expI sinI x y asr) nodes) (0, 0))) (snd (acc (map (tn expI sinI x y asr) nodes) (0, 0))).

Lemma sumR_vn x y asr Kex nodes :
  sumR (map (vn x y asr Kex) nodes) = Kex * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes).
Proof.
  induction nodes as [| n ns IH]; simpl; [ring |].
  rewrite IH. unfold vn. ring.
Qed.

Theorem low_branch (expI sinI : R -> R) (x y rho asr A Tr b0 E : R) (kA : Z) (pxI pyI Phix Phiy : R)
  (nodes : list NodeS) (dats : list Dat) :
  exp_contract expI -> sin_contract sinI ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  Rabs (asin rho) <= A - 1 / 10 ^ 4 -> A <= bpow radix2 kA -> (-1021 <= kA)%Z -> (kA <= 1)%Z ->
  0 <= b0 -> bq <= b0 ->
  List.Forall2 (ok A (rndF (asr / (2 * TAU)))) nodes dats -> (length nodes <= 24)%nat ->
  A / (4 * PI) * sumD (gdat A b0) dats <= E -> E <= 1 ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr
        - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= Tr ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI
        - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI)))
    <= bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + E + 200 * z
       + Tr / (2 * PI) + (bpow radix2 (kA - 54) + bpow radix2 (-62) * bpow radix2 kA) / (2 * PI).
Proof.
  intros Hexp Hsin Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Ha1 Ha2 HA Hrho HAk Hk1 Hk2 Hb0 Hbq Hall Hlen HE HE1 Hprob HT1.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (HPI : 3 < PI < 315 / 100) by (pose proof PI_RGT_0; split; interval).
  destruct HPI as [HPI1 HPI2].
  set (Kh := rndF (asr / (2 * TAU))).
  set (Kex := asr / (4 * PI)).
  assert (HKex2 : Rabs Kex <= / 10).
  { unfold Kex. rewrite Rabs_div_pos by lra. apply Rmult_le_reg_r with (4 * PI); [lra |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (HKex1 : bpow radix2 (-57) <= Rabs Kex).
  { unfold Kex. rewrite Rabs_div_pos by lra.
    apply Rmult_le_reg_r with (4 * PI); [lra |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
    assert (Hb : bpow radix2 (-53) = 16 * bpow radix2 (-57)) by (replace (-53)%Z with (-57 + 4)%Z by reflexivity; rewrite bpow_plus; replace (bpow radix2 4) with 16 by reflexivity; ring).
    pose proof (bpow_gt_0 radix2 (-57)). nra. }
  assert (HKh : Rabs (Kh - Kex) <= ETAK * Rabs Kex) by (apply K_close; lra).
  assert (HAn : Rabs asr <= 6 / 5) by lra.
  destruct (rule_bound expI sinI x y asr A Kex Kh b0 Hexp Hsin Fx Fy Hx Hy Ha1 Ha2 HA HKh HKex1 HKex2 nodes dats Hb0 Hbq Hall Hlen)
    as [HC [FH [HL [HV HB]]]].
  pose proof (sum_g_le A Kex Kh b0 nodes dats Hb0 Hall) as Hg.
  pose proof (sum_g_nonneg A Kex Kh b0 nodes dats Hb0 Hall) as Hg0.
  assert (HKpos : 0 < Rabs Kex) by (pose proof (bpow_gt_0 radix2 (-57)); lra).
  assert (HSD : 0 <= sumD (gdat A b0) dats).
  { destruct (Rle_dec 0 (sumD (gdat A b0) dats)) as [H | H]; [exact H |].
    exfalso. assert (Rabs Kex * sumD (gdat A b0) dats < 0) by nra. lra. }
  assert (HKA : Rabs Kex <= A / (4 * PI)).
  { unfold Kex. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Ha2]. }
  assert (Hgn : sum2 (gn A Kex b0) nodes dats <= E).
  { assert (Hm : Rabs Kex * sumD (gdat A b0) dats <= A / (4 * PI) * sumD (gdat A b0) dats) by (apply Rmult_le_compat_r; [exact HSD | exact HKA]).
    lra. }
  set (V := sumR (map (vn x y asr Kex) nodes)) in *.
  set (Wsum := sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)).
  assert (HVe : V = Kex * Wsum) by (unfold V, Wsum; apply sumR_vn).
  set (H := fst (acc (map (tn expI sinI x y asr) nodes) (0, 0))) in *.
  set (L := snd (acc (map (tn expI sinI x y asr) nodes) (0, 0))) in *.
  assert (Hlen' : INR (length nodes) <= 24) by (replace 24 with (INR 24) by (simpl; lra); apply le_INR; exact Hlen).
  assert (HVb : Rabs V <= 12 / 5) by lra.
  assert (HB1 : sum2 (vbn x y asr A Kex) nodes dats <= 1) by lra.
  assert (HLs : Rabs L <= bpow radix2 (-40)).
  { eapply Rle_trans; [exact HL |].
    assert (Hm : 3 * u * (Rabs V + sum2 (vbn x y asr A Kex) nodes dats + 72 * z) <= 3 * u * (12 / 5 + 1 + 72 * z)).
    { apply Rmult_le_compat_l; [lra |]. lra. }
    assert (Hn : 24 * (3 * u * (12 / 5 + 1 + 72 * z) + 2 * z) <= bpow radix2 (-40)) by (unfold u, z; simpl; interval).
    lra. }
  assert (HHb : Rabs H <= 4).
  { assert (E1 : Rabs H = Rabs (V + (H + L - V) + - L)) by (f_equal; ring).
    assert (Hb2 : Rabs H <= Rabs V + Rabs (H + L - V) + Rabs L).
    { rewrite E1. eapply Rle_trans; [apply Rabs_triang |]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
      rewrite Rabs_Ropp. lra. }
    assert (Hz1 : 200 * z <= / 1000) by (unfold z; simpl; interval).
    assert (Hb40 : bpow radix2 (-40) <= / 1000) by (replace (/ 1000) with (/ 1000) by reflexivity; apply Rle_trans with (bpow radix2 (-10)); [apply bpow_le; lia | change (bpow radix2 (-10)) with (/ 1024); lra]).
    lra. }
  (* the integral and its angle *)
  assert (HIn : Rabs (Iint (x * x + y * y) (x * y) asr / (2 * PI) - V) <= Tr / (2 * PI)).
  { assert (Eq : Iint (x * x + y * y) (x * y) asr / (2 * PI) - V
                 = (Iint (x * x + y * y) (x * y) asr - asr / 2 * Wsum) / (2 * PI)).
    { rewrite HVe. unfold Kex. field. lra. }
    rewrite Eq. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact HT1]. }
  assert (Hr : 0 <= x * x + y * y) by nra.
  assert (Hp : Rabs (x * y) <= (x * x + y * y) / 2).
  { pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2. unfold Rsqr in h1, h2.
    apply Rabs_le. split; nra. }
  assert (Hshift : Rabs (asin rho - asr) <= bpow radix2 (kA - 54) + bpow radix2 (-62) * bpow radix2 kA).
  { destruct Hasin as [Za [Eas HZa]].
    assert (HZb : Rabs Za <= bpow radix2 kA).
    { assert (Eq9 : Za = asin rho + (Za - asin rho)) by ring.
      assert (Rabs Za <= Rabs (asin rho) + Rabs (Za - asin rho)) by (rewrite Eq9 at 1; apply Rabs_triang).
      assert (bpow radix2 (-62) <= / 1000000) by (apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | change (bpow radix2 (-20)) with (/ 1048576); lra]).
      assert (bpow radix2 kA <= 2) by (replace 2 with (bpow radix2 1) by reflexivity; apply bpow_le; lia).
      assert (Hm : bpow radix2 (-62) * Rabs (asin rho) <= bpow radix2 (-62) * 2) by (apply Rmult_le_compat_l; [apply Rlt_le, bpow_gt_0 | lra]).
      assert (Rabs (asin rho) <= A) by lra. lra. }
    assert (Hr1 : Rabs (rndF Za - Za) <= bpow radix2 (kA - 54)) by (apply rnd_pow; assumption).
    rewrite <- Eas in Hr1.
    assert (Eq9 : asin rho - asr = (asin rho - Za) + (Za - asr)) by ring.
    rewrite Eq9. eapply Rle_trans; [apply Rabs_triang |].
    rewrite Rabs_minus_sym in HZa.
    assert (Rabs (Za - asr) <= bpow radix2 (kA - 54)) by (rewrite Rabs_minus_sym; exact Hr1).
    assert (Hm : bpow radix2 (-62) * Rabs (asin rho) <= bpow radix2 (-62) * bpow radix2 kA) by (apply Rmult_le_compat_l; [apply Rlt_le, bpow_gt_0 | lra]).
    lra. }
  assert (Hl2 : Rabs (Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) - Iint (x * x + y * y) (x * y) asr / (2 * PI))
                <= (bpow radix2 (kA - 54) + bpow radix2 (-62) * bpow radix2 kA) / (2 * PI)).
  { assert (Eq : Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) - Iint (x * x + y * y) (x * y) asr / (2 * PI)
                 = (Iint (x * x + y * y) (x * y) (asin rho) - Iint (x * x + y * y) (x * y) asr) / (2 * PI)) by (field; lra).
    rewrite Eq. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra |].
    eapply Rle_trans; [apply Iint_lip; try assumption; lra |]. exact Hshift. }
  set (c := Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI)) in *.
  assert (Hc : Rabs (H + L - c) <= E + 200 * z + Tr / (2 * PI) + (bpow radix2 (kA - 54) + bpow radix2 (-62) * bpow radix2 kA) / (2 * PI)).
  { assert (Eq : H + L - c = (H + L - V) + (V - Iint (x * x + y * y) (x * y) asr / (2 * PI)) + (Iint (x * x + y * y) (x * y) asr / (2 * PI) - c)) by ring.
    rewrite Eq. eapply Rle_trans; [apply Rabs_triang |]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
    rewrite (Rabs_minus_sym V). rewrite (Rabs_minus_sym (Iint (x * x + y * y) (x * y) asr / (2 * PI)) c). lra. }
  (* the distribution functions and the last stage *)
  pose proof (phi_prod Phix Phiy pxI pyI HPx HPy (conj (proj1 Hpx) (proj2 Hpx)) (conj (proj1 Hpy) (proj2 Hpy)) Epx Epy) as Hpp.
  unfold Rhat. fold H. fold L.
  pose proof (finish_bound pxI pyI H L (Phix * Phiy + c) Fpx Fpy Hpx Hpy FH HHb HLs Hprob) as Hfin.
  assert (Hfin2 : Rabs (pxI * pyI + H + L - (Phix * Phiy + c)) <= 2 * eP + Rabs (H + L - c)).
  { assert (Eq : pxI * pyI + H + L - (Phix * Phiy + c) = (pxI * pyI - Phix * Phiy) + (H + L - c)) by ring.
    rewrite Eq. eapply Rle_trans; [apply Rabs_triang |]. lra. }
  lra.
Qed.
