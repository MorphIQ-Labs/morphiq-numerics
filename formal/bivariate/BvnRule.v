(** The whole rule: the accumulated terms against the exact weighted
    integrand values [Kex W_i exp(-Q_i)], with the per-node supremum of
    BvnQuadG.v. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnQuadG BvnTail.
Open Scope R_scope.

(** An exact node (the sign, the exact positive abscissa and weight) with its
    stored binary64 abscissa, weight and folded weight [Kw]. *)
Record NodeS := mkN { nsgn : R; nxs : R; nxh : R; nW : R; nwh : R; nkw : R }.

(** The enclosure data of a node: bounds on [tau = (sign x + 1)/2], an upper
    bound on the weight, and the binade [2^k] above the largest sine of its
    angle. *)
Record Dat := mkD { dtaulo : R; dtauhi : R; dwhi : R; dk : Z; dbr : bool }.

Definition tau_of (n : NodeS) : R := (nsgn n * nxs n + 1) / 2.

Definition theta_of (A : R) (d : Dat) : R :=
  let tauhi := dtauhi d in
  let dth := u * A * (tauhi + 76 / 100) in
  let sg := sin (A * tauhi + dth) in
  let hs_ := (1 + bpow radix2 (-100)) * bpow radix2 (dk d - 54) in
  let eps1 := (dth + hs_) / (1 - (sg + hs_)) in
  eps1 + (1 + eps1) * (71 / 10 * u).

Definition sgs_of (A : R) (d : Dat) : R :=
  sin (A * dtauhi d + u * A * (dtauhi d + 76 / 100)) + (1 + bpow radix2 (-100)) * bpow radix2 (dk d - 54).

(** The part of the node hypotheses about the enclosure data alone. *)
Definition dat_ok (A : R) (d : Dat) : Prop :=
  / 4096 <= dtaulo d /\ dtauhi d <= 1 /\ dwhi d <= 1 /\
  (-1021 <= dk d)%Z /\ (dk d <= 0)%Z /\
  sin (A * dtauhi d + u * A * (dtauhi d + 76 / 100)) <= bpow radix2 (dk d) /\
  sgs_of A d <= 99 / 100 /\ 0 < theta_of A d < 1.

(** The part about the exact node, its stored values and its enclosure. *)
Definition node_enc (Kh : R) (n : NodeS) (d : Dat) : Prop :=
  (nsgn n = 1 \/ nsgn n = -1) /\ 0 < nxs n < 1 /\
  dtaulo d <= tau_of n <= dtauhi d /\
  nxh n = rndF (nxs n) /\ / 4096 <= nW n <= dwhi d /\ nwh n = rndF (nW n) /\
  nkw n = rndF (nwh n * Kh).

Definition psi2 : R := 2000 * u * u.
Definition bq : R := (1 + psi2) * (1 + ew) * (1 + rx) * exp (300 * z) - 1.

Section Rule.
Variables (expI sinI : R -> R) (x y asr A Kex Kh bp : R).

Definition Qn (n : NodeS) : R := Qf (x * x + y * y) (x * y) (sin (asr * tau_of n)).
Definition vn (n : NodeS) : R := Kex * nW n * exp (- Qn n).
Definition tn (n : NodeS) : R := node_term expI sinI x y asr (nsgn n) (nxh n) (nkw n).
Definition vbn (n : NodeS) (d : Dat) : R :=
  Rabs (Kex * nW n) * exp (- Qn n) * ((1 + ew) * (1 + rx) * exp (theta_of A d * Qn n + 300 * z) - 1).
Definition gn (n : NodeS) (d : Dat) : R := Rabs Kex * nW n * Gsup bp (theta_of A d) (1 - theta_of A d).

Fixpoint sum2 {X Y : Type} (f : X -> Y -> R) (l1 : list X) (l2 : list Y) : R :=
  match l1, l2 with
  | a :: l1', b :: l2' => f a b + sum2 f l1' l2'
  | _, _ => 0
  end.

Hypotheses (Hexp : exp_contract expI) (Hsin : sin_contract sinI)
  (Fx : fmtF x) (Fy : fmtF y) (Hx : Rabs x <= 64) (Hy : Rabs y <= 64)
  (Ha1 : bpow radix2 (-53) <= Rabs asr) (Ha2 : Rabs asr <= A) (HA : A <= 6 / 5)
  (HKh : Rabs (Kh - Kex) <= ETAK * Rabs Kex) (HK1 : bpow radix2 (-57) <= Rabs Kex)
  (HK2 : Rabs Kex <= / 10).

Lemma node_facts n d :
  0 <= bp -> bq <= bp -> node_enc Kh n d -> dat_ok A d ->
  Rabs (tn n - vn n) <= vbn n d + 3 * z /\
  psi2 * Rabs (vn n) + (1 + psi2) * vbn n d <= gn n d /\ 0 <= vbn n d /\
  fmtF (tn n) /\ (0 <= Kex -> 0 <= tn n) /\ (Kex <= 0 -> tn n <= 0) /\ Rabs (vn n) <= / 10.
Proof.
  intros Hbp Hbq [Hsg [Hxs [Htau [Hxh [HW [Hwh Hkw]]]]]] [Hlo [Hhi [Hwd [Hk1 [Hk2 [Hsgk [Hsgs Hth]]]]]]].
  destruct HW as [HW1 HW2].
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (HW2' : nW n <= 1) by lra.
  destruct (kw_close (nW n) (nwh n) (nkw n) Kh Kex HW1 HW2' Hwh Hkw HKh HK1 HK2) as [Hkc Hkw1].
  assert (Hew0 : 0 <= ew) by (unfold ew; assert (1 <= (1 + u) * (1 + u) * (1 + ETAK)) by (unfold ETAK; nra); lra).
  pose proof (node_full expI sinI x y asr (nsgn n) (nxs n) (nxh n) (Kex * nW n) (nkw n) A (dtauhi d) (dtaulo d) (dk d) ew
    Hexp Hsin Fx Fy Hx Hy Ha1 Ha2 HA Hsg Hxs (proj1 Htau) (proj2 Htau) Hlo Hhi Hxh Hk1 Hk2 Hsgk Hsgs Hkc Hew0 Hkw1) as Hnf.
  cbv zeta in Hnf.
  assert (Hr : 0 <= x * x + y * y) by nra.
  assert (Hp : Rabs (x * y) <= (x * x + y * y) / 2).
  { pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2. unfold Rsqr in h1, h2.
    apply Rabs_le. split; nra. }
  destruct Htau as [Ht1 Ht2]. fold (tau_of n) in Ht1, Ht2.
  assert (Hta0 : 0 <= tau_of n) by lra.
  assert (Hta1 : tau_of n <= 1) by lra.
  assert (Hasr : Rabs (asr * tau_of n) <= 3 / 2).
  { rewrite Rabs_mult, (Rabs_pos_eq (tau_of n)) by exact Hta0. pose proof (Rabs_pos asr). nra. }
  assert (HQ : 0 <= Qn n) by (unfold Qn; apply Qf_nonneg; [exact Hr | exact Hp | apply sin_abs_lt_1; exact Hasr]).
  assert (Hth' : 0 < theta_of A d /\ theta_of A d < 1) by exact Hth.
  assert (Hbound : Rabs (tn n - vn n) <= vbn n d + 3 * z) by exact Hnf.
  assert (Hef : 0 < exp (- Qn n)) by apply exp_pos.
  assert (Hvb : 0 <= vbn n d).
  { unfold vbn. apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rabs_pos | lra] |].
    assert (1 <= (1 + ew) * (1 + rx) * exp (theta_of A d * Qn n + 300 * z)).
    { assert (Hrx : 0 <= rx) by (unfold rx; destruct ue_small; nra).
      assert (1 <= exp (theta_of A d * Qn n + 300 * z)).
      { rewrite <- exp_0. apply exp_mono. assert (0 <= theta_of A d * Qn n) by (apply Rmult_le_pos; lra). lra. }
      assert (1 <= (1 + ew) * (1 + rx)) by nra. nra. }
    lra. }
  assert (Hs12 : (0 <= Kex -> 0 <= tn n) /\ (Kex <= 0 -> tn n <= 0)).
  { pose proof (Rabs_pos Kex).
    unfold tn, node_term, termf.
    set (a := argnc x y (sinI (angle asr (nsgn n) (nxh n)))).
    destruct (Hexp (- a)) as [Zc [Ex HZ]].
    assert (Hpos : 0 <= expI (- a)).
    { rewrite Ex. rewrite <- rnd_zero.
      apply rnd_mono. pose proof (exp_pos (- a)).
      assert (Hb : bpow radix2 (-100) <= / 2) by (replace (/ 2) with (bpow radix2 (-1)) by reflexivity; apply bpow_le; lia).
      assert (Hm : bpow radix2 (-100) * exp (- a) <= / 2 * exp (- a)) by (apply Rmult_le_compat_r; lra).
      apply Rabs_le_between in HZ. lra. }
    assert (Hwh0 : 0 <= nwh n) by (rewrite Hwh; rewrite <- rnd_zero; apply rnd_mono; lra).
    split.
    + intros HK0. assert (HKh0 : 0 <= Kh).
      { apply Rabs_le_between in HKh. rewrite (Rabs_pos_eq Kex HK0) in HKh. assert (ETAK <= 1) by (unfold ETAK; lra). nra. }
      assert (Hk0 : 0 <= nkw n) by (rewrite Hkw; rewrite <- rnd_zero; apply rnd_mono; apply Rmult_le_pos; assumption).
      rewrite <- rnd_zero. apply rnd_mono. apply Rmult_le_pos; assumption.
    + intros HK0. assert (HKh0 : Kh <= 0).
      { apply Rabs_le_between in HKh. rewrite (Rabs_left1 Kex HK0) in HKh. assert (ETAK <= 1) by (unfold ETAK; lra). nra. }
      assert (Hk0 : nkw n <= 0) by (rewrite Hkw; rewrite <- rnd_zero; apply rnd_mono; nra).
      rewrite <- rnd_zero. apply rnd_mono. nra. }
  assert (Habs : Rabs (vn n) <= / 10).
  { unfold vn. rewrite Rabs_mult, (Rabs_pos_eq (exp (- Qn n))) by (apply Rlt_le; apply exp_pos).
    assert (Hq1 : exp (- Qn n) <= 1) by (rewrite <- exp_0; apply exp_mono; lra).
    rewrite Rabs_mult, (Rabs_pos_eq (nW n)) by lra.
    assert (Hm : Rabs Kex * nW n <= / 10 * 1) by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact HK2 | lra]).
    assert (Hm2 : Rabs Kex * nW n * exp (- Qn n) <= / 10 * 1 * 1) by (apply Rmult_le_compat; [apply Rmult_le_pos; [apply Rabs_pos | lra] | left; apply exp_pos | exact Hm | exact Hq1]).
    lra. }
  refine (conj Hbound (conj _ (conj Hvb (conj _ (conj _ _))))).
  - (* the supremum *)
    pose proof (node_sup bp (theta_of A d) (Qn n) HQ Hbp (proj1 Hth') (proj2 Hth')) as Hns.
    unfold gn, vbn, vn.
    assert (Eexp : exp (theta_of A d * Qn n + 300 * z) = exp (theta_of A d * Qn n) * exp (300 * z)) by apply exp_plus.
    set (f := exp (- Qn n)). set (W := Rabs (Kex * nW n)).
    set (E := exp (theta_of A d * Qn n)).
    assert (HE0 : 0 < E) by apply exp_pos.
    assert (Hf0 : 0 < f) by exact Hef.
    assert (HW0 : 0 <= W) by apply Rabs_pos.
    assert (HvW : Rabs (Kex * nW n * f) = W * f) by (rewrite Rabs_mult, (Rabs_pos_eq f (Rlt_le _ _ Hef)); reflexivity).
    rewrite HvW.
    assert (Hid : psi2 * (W * f) + (1 + psi2) * (W * f * ((1 + ew) * (1 + rx) * (exp (theta_of A d * Qn n) * exp (300 * z)) - 1))
                  = W * (f * ((1 + bq) * E - 1))).
    { unfold bq, E. ring. }
    rewrite Eexp. rewrite Hid.
    assert (Hmono : f * ((1 + bq) * E - 1) <= f * ((1 + bp) * E - 1)) by (apply Rmult_le_compat_l; [lra |]; nra).
    assert (HKa : Rabs Kex * nW n = W) by (unfold W; rewrite Rabs_mult, (Rabs_pos_eq (nW n)) by lra; reflexivity).
    assert (Hfin : W * (f * ((1 + bp) * E - 1)) <= W * Gsup bp (theta_of A d) (1 - theta_of A d))
      by (apply Rmult_le_compat_l; [exact HW0 | exact Hns]).
    assert (Hm2 : W * (f * ((1 + bq) * E - 1)) <= W * (f * ((1 + bp) * E - 1))) by (apply Rmult_le_compat_l; [exact HW0 | exact Hmono]).
    rewrite HKa. lra.
  - unfold tn, node_term, termf. apply fmtF_rnd.
  - exact (proj1 Hs12).
  - exact (conj (proj2 Hs12) Habs).
Qed.

Definition ok (n : NodeS) (d : Dat) : Prop := node_enc Kh n d /\ dat_ok A d.

Lemma rule_facts nodes dats :
  0 <= bp -> bq <= bp -> List.Forall2 ok nodes dats ->
  Rabs (sumR (map tn nodes) - sumR (map vn nodes)) <= sum2 vbn nodes dats + 3 * INR (length nodes) * z /\
  psi2 * sumR (map (fun n => Rabs (vn n)) nodes) + (1 + psi2) * sum2 vbn nodes dats <= sum2 gn nodes dats /\
  0 <= sumR (map (fun n => Rabs (vn n)) nodes) /\ 0 <= sum2 vbn nodes dats /\
  (forall t, In t (map tn nodes) -> fmtF t) /\
  (0 <= Kex -> forall t, In t (map tn nodes) -> 0 <= t) /\
  (Kex <= 0 -> forall t, In t (map tn nodes) -> t <= 0) /\
  sumR (map (fun n => Rabs (vn n)) nodes) <= INR (length nodes) / 10.
Proof.
  intros Hbp Hbq Hall.
  induction Hall as [| n d nodes dats [Hok1 Hok2] Hall IH].
  - simpl. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try (intros; contradiction); try lra.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct IH as [I1 [I2 [I3 [I4 [I5 [I6 [I7 I8]]]]]]].
    destruct (node_facts n d Hbp Hbq Hok1 Hok2) as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
    pose proof z_pos as Hz. pose proof (Rabs_pos (vn n)).
    simpl map. simpl sumR. simpl sum2. simpl length. rewrite S_INR.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + assert (E : tn n + sumR (map tn nodes) - (vn n + sumR (map vn nodes))
                  = (tn n - vn n) + (sumR (map tn nodes) - sumR (map vn nodes))) by ring.
      rewrite E. eapply Rle_trans; [apply Rabs_triang |]. lra.
    + lra.
    + lra.
    + lra.
    + intros t [Ht | Ht]; [rewrite <- Ht; exact F4 | apply I5; exact Ht].
    + intros HK t [Ht | Ht]; [rewrite <- Ht; apply F5; exact HK | apply I6; assumption].
    + intros HK t [Ht | Ht]; [rewrite <- Ht; apply F6; exact HK | apply I7; assumption].
    + lra.
Qed.

Lemma rule_bound nodes dats :
  0 <= bp -> bq <= bp -> List.Forall2 ok nodes dats -> (length nodes <= 24)%nat ->
  Rabs (fst (acc (map tn nodes) (0, 0)) + snd (acc (map tn nodes) (0, 0)) - sumR (map vn nodes))
    <= sum2 gn nodes dats + 200 * z /\
  fmtF (fst (acc (map tn nodes) (0, 0))) /\ Rabs (snd (acc (map tn nodes) (0, 0))) <= 24 * (3 * u * (Rabs (sumR (map vn nodes)) + sum2 vbn nodes dats + 72 * z) + 2 * z).
Proof.
  intros Hbp Hbq Hall Hlen.
  destruct (rule_facts nodes dats Hbp Hbq Hall) as [I1 [I2 [I3 [I4 [I5 [I6 [I7 I8]]]]]]].
  pose proof z_pos as Hz. pose proof u_pos as Hu. pose proof u_val as Huv.
  assert (Hlen' : (length (map tn nodes) <= 24)%nat) by (rewrite map_length; exact Hlen).
  assert (Hl : INR (length nodes) <= 24) by (replace 24 with (INR 24) by (simpl; lra); apply le_INR; exact Hlen).
  set (T := sumR (map tn nodes)) in *. set (V := sumR (map vn nodes)) in *.
  set (Va := sumR (map (fun n => Rabs (vn n)) nodes)) in *.
  set (B1 := sum2 vbn nodes dats) in *.
  assert (HVa : Rabs V <= Va).
  { unfold V, Va. clear. induction nodes as [| n ns IH]; simpl; [rewrite Rabs_R0; lra |].
    eapply Rle_trans; [apply Rabs_triang |]. lra. }
  assert (HT : Rabs (T - V) <= B1 + 72 * z) by nra.
  assert (Hacc : fmtF (fst (acc (map tn nodes) (0, 0))) /\
    Rabs (fst (acc (map tn nodes) (0, 0)) + snd (acc (map tn nodes) (0, 0)) - T) <= 2000 * u * u * Rabs T + 30 * z /\
    Rabs (snd (acc (map tn nodes) (0, 0))) <= 24 * (3 * u * Rabs T + 2 * z)).
  { destruct (Rle_dec 0 Kex) as [Hk | Hk].
    - destruct (acc_final (map tn nodes) (fun t Ht => conj (I5 t Ht) (I6 Hk t Ht)) Hlen') as [Fh [_ [H HL]]].
      rewrite (Rabs_pos_eq T) by (apply sumR_nonneg; intros t Ht; apply (I6 Hk t Ht)). exact (conj Fh (conj H HL)).
    - destruct (acc_final_neg (map tn nodes) (fun t Ht => conj (I5 t Ht) (I7 ltac:(lra) t Ht)) Hlen') as [Fh [_ [H HL]]]. exact (conj Fh (conj H HL)). }
  destruct Hacc as [Fh [Hacc HaccL]].
  assert (HTa : Rabs T <= Va + B1 + 72 * z).
  { assert (E : T = V + (T - V)) by ring. assert (Rabs T <= Rabs V + Rabs (T - V)) by (rewrite E at 1; apply Rabs_triang). lra. }
  assert (E2 : fst (acc (map tn nodes) (0, 0)) + snd (acc (map tn nodes) (0, 0)) - V
               = (fst (acc (map tn nodes) (0, 0)) + snd (acc (map tn nodes) (0, 0)) - T) + (T - V)) by ring.
  refine (conj _ (conj Fh _)).
  2: { eapply Rle_trans; [exact HaccL |]. assert (Hm : 3 * u * Rabs T <= 3 * u * (Rabs V + B1 + 72 * z)) by (apply Rmult_le_compat_l; [lra | assert (Rabs T <= Rabs V + Rabs (T - V)) by (assert (E3 : T = V + (T - V)) by ring; rewrite E3 at 1; apply Rabs_triang); lra]). lra. }
  rewrite E2. eapply Rle_trans; [apply Rabs_triang |].
  assert (Hs : 2000 * u * u * Rabs T <= 2000 * u * u * (Va + B1 + 72 * z)) by (apply Rmult_le_compat_l; [nra | exact HTa]).
  assert (Hps : psi2 = 2000 * u * u) by reflexivity.
  assert (Hzs : 2000 * u * u * (72 * z) <= z) by (rewrite Huv; nra).
  assert (Hva : 0 <= Va) by exact I3.
  assert (Hb1 : 0 <= B1) by exact I4.
  assert (Hq : 2000 * u * u * (Va + B1 + 72 * z) = psi2 * Va + psi2 * B1 + 2000 * u * u * (72 * z)) by (rewrite Hps; ring).
  nra.
Qed.

(** The branch flag of a datum records which side of [Gsup] applies. *)
Definition gdat (d : Dat) : R := dwhi d * Gsup bp (theta_of A d) (1 - theta_of A d).

Fixpoint sumD (f : Dat -> R) (l : list Dat) : R :=
  match l with nil => 0 | d :: l' => f d + sumD f l' end.

Lemma sum_g_le nodes dats :
  0 <= bp -> List.Forall2 ok nodes dats -> sum2 gn nodes dats <= Rabs Kex * sumD gdat dats.
Proof.
  intros Hbp Hall. induction Hall as [| n d nodes dats [Hok1 Hok2] Hall IH]; simpl; [lra |].
  destruct Hok1 as [_ [_ [_ [_ [HW _]]]]]. destruct HW as [HW1 HW2].
  destruct Hok2 as [_ [_ [Hwd [_ [_ [_ [_ Hth]]]]]]].
  assert (HG : 0 <= Gsup bp (theta_of A d) (1 - theta_of A d)) by (apply Gsup_nonneg; [exact Hbp | lra | lra]).
  assert (Hg : gn n d <= Rabs Kex * gdat d).
  { unfold gn, gdat. assert (Rabs Kex * nW n <= Rabs Kex * dwhi d) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact HW2]).
    assert (Hm : Rabs Kex * nW n * Gsup bp (theta_of A d) (1 - theta_of A d) <= Rabs Kex * dwhi d * Gsup bp (theta_of A d) (1 - theta_of A d))
      by (apply Rmult_le_compat_r; [exact HG | assumption]).
    lra. }
  lra.
Qed.

Lemma sum_g_nonneg nodes dats :
  0 <= bp -> List.Forall2 ok nodes dats -> 0 <= sum2 gn nodes dats.
Proof.
  intros Hbp Hall. induction Hall as [| n d nodes dats [Hok1 Hok2] Hall IH]; simpl; [lra |].
  destruct Hok1 as [_ [_ [_ [_ [HW _]]]]]. destruct HW as [HW1 HW2].
  destruct Hok2 as [_ [_ [_ [_ [_ [_ [_ Hth]]]]]]].
  assert (HG : 0 <= Gsup bp (theta_of A d) (1 - theta_of A d)) by (apply Gsup_nonneg; [exact Hbp | lra | lra]).
  assert (Hg : 0 <= gn n d) by (unfold gn; apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rabs_pos | lra] | exact HG]).
  lra.
Qed.

Definition gcl (d : Dat) : R :=
  dwhi d * (if dbr d then theta_of A d / (1 - theta_of A d) * exp ((1 - theta_of A d) * bp / theta_of A d - 1) else bp).

Definition br_ok (d : Dat) : Prop :=
  (dbr d = true -> (1 - theta_of A d) * bp <= theta_of A d) /\
  (dbr d = false -> theta_of A d < (1 - theta_of A d) * bp).

Lemma gdat_gcl d : br_ok d -> gdat d = gcl d.
Proof.
  intros [H1 H2]. unfold gdat, gcl, Gsup. destruct (dbr d) eqn:E.
  - destruct (Rle_dec ((1 - theta_of A d) * bp) (theta_of A d)) as [H | H]; [reflexivity |].
    exfalso. apply H. apply H1. reflexivity.
  - destruct (Rle_dec ((1 - theta_of A d) * bp) (theta_of A d)) as [H | H]; [| reflexivity].
    exfalso. pose proof (H2 eq_refl). lra.
Qed.

Lemma sumD_gcl dats : List.Forall br_ok dats -> sumD gdat dats = sumD gcl dats.
Proof.
  intros H. induction H as [| d dats Hd H IH]; simpl; [reflexivity |].
  rewrite (gdat_gcl d Hd), IH. reflexivity.
Qed.
End Rule.
