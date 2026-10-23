(** The whole rule: the corrected sum against [Kex] times the exact weighted
    integrand values, with the per-node supremum of BvnQuadG.v. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound BvnArg BvnNode BvnTrig BvnLow BvnSum BvnChain BvnQuadG.
Open Scope R_scope.

(** An exact node (the sign, the exact positive abscissa and weight) with its
    stored binary64 abscissa and weight. *)
Record NodeS := mkN { nsgn : R; nxs : R; nxh : R; nW : R; nwh : R }.

(** The enclosure data of a node: bounds on [tau = (sign x + 1)/2] and the
    binade [2^k] above the largest sine of its angle. *)
Record Dat := mkD { dtaulo : R; dtauhi : R; dwhi : R; dk : Z }.

Definition tau_of (n : NodeS) : R := (nsgn n * nxs n + 1) / 2.

Definition theta_of (A : R) (d : Dat) : R :=
  let tauhi := dtauhi d in
  let dth := u * A * (tauhi + 76 / 100) in
  let sg := sin (A * tauhi + dth) in
  let hs_ := bpow radix2 (dk d - 54) in
  let hc_ := bpow radix2 (-54) in
  let zt := hc_ * (2 + hc_) / (1 - sg * sg) in
  let Eh := hs_ + 2 * (2 * u + u * u) in
  let ar1 := ar0 zt Eh sg * (1 + u) + u in
  let eps1 := dth / (1 - sg) in
  eps1 + (1 + eps1) * ar1.

Definition zt_of (A : R) (d : Dat) : R :=
  let tauhi := dtauhi d in
  let dth := u * A * (tauhi + 76 / 100) in
  let sg := sin (A * tauhi + dth) in
  let hc_ := bpow radix2 (-54) in
  hc_ * (2 + hc_) / (1 - sg * sg).

Definition node_ok (asr A : R) (n : NodeS) (d : Dat) : Prop :=
  (nsgn n = 1 \/ nsgn n = -1) /\ 0 < nxs n < 1 /\
  dtaulo d <= tau_of n <= dtauhi d /\ / 4096 <= dtaulo d /\ dtauhi d <= 1 /\
  nxh n = rndF (nxs n) /\ / 4096 <= nW n <= dwhi d /\ dwhi d <= / 2 /\ nwh n = rndF (nW n) /\
  (-1000 <= dk d)%Z /\ (dk d <= 0)%Z /\
  sin (A * dtauhi d + u * A * (dtauhi d + 76 / 100)) <= bpow radix2 (dk d) /\
  zt_of A d <= / 2 /\ 0 < theta_of A d < 1.

(** Per-node quantities at the correlation's angle bound [asr]. *)
Section Rule.
Variables x y asr A etaK : R.

Definition Qn (n : NodeS) : R := Qf (x * x + y * y) (x * y) (sin (asr * tau_of n)).
Definition vn (n : NodeS) : R := nW n * exp (- Qn n).
Definition tn (n : NodeS) : R := node_term x y asr (nsgn n) (nxh n) (nwh n).
Definition bp : R := (1 + psi etaK) * (1 + u) ^ 3 * exp z - 1.
Definition vbn (n : NodeS) (d : Dat) : R :=
  vn n * ((1 + u) ^ 3 * exp (theta_of A d * Qn n + z) - 1).
Definition gn (n : NodeS) (d : Dat) : R := nW n * Gsup bp (theta_of A d) (1 - theta_of A d).

Fixpoint sum2 {X Y : Type} (f : X -> Y -> R) (l1 : list X) (l2 : list Y) : R :=
  match l1, l2 with
  | a :: l1', b :: l2' => f a b + sum2 f l1' l2'
  | _, _ => 0
  end.

Hypothesis Hetaa : 0 <= etaK.

Lemma node_facts n d :
  dom x -> dom y -> bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  node_ok asr A n d ->
  Rabs (tn n - vn n) <= vbn n d + 3 * z /\
  psi etaK * vn n + (1 + psi etaK) * vbn n d <= gn n d /\ 0 <= vn n /\ 0 <= vbn n d /\
  fmtF (tn n) /\ 0 <= tn n.
Proof.
  intros Hx Hy Ha1 Ha2 HA Hok.
  destruct Hok as [Hsg [Hxs [Htau [Hlo [Hhi [Hxh [HW [Hwd [Hwh [Hk1 [Hk2 [Hsgk [Hzt Hth]]]]]]]]]]]]].
  destruct HW as [HW1 HW2']. assert (HW2 : nW n <= / 2) by lra.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  pose proof (node_full x y asr (nsgn n) (nxs n) (nxh n) (nW n) (nwh n) A (dtauhi d) (dtaulo d) (dk d)
    Hx Hy Ha1 Ha2 HA Hsg Hxs (proj1 Htau) (proj2 Htau) Hlo Hhi Hxh HW1 HW2 Hwh Hk1 Hk2 Hsgk Hzt) as Hnf.
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
  assert (HQ : 0 <= Qn n).
  { unfold Qn. apply Qf_nonneg; [exact Hr | exact Hp |]. apply sin_abs_lt_1. exact Hasr. }
  assert (Hvn : 0 <= vn n) by (unfold vn; apply Rmult_le_pos; [lra | left; apply exp_pos]).
  assert (Hth' : 0 < theta_of A d /\ theta_of A d < 1) by exact Hth.
  assert (Hbound : Rabs (tn n - vn n) <= vbn n d + 3 * z) by exact Hnf.
  assert (Hvb : 0 <= vbn n d).
  { unfold vbn. apply Rmult_le_pos; [exact Hvn |].
    assert (1 <= (1 + u) ^ 3 * exp (theta_of A d * Qn n + z)).
    { assert (1 <= (1 + u) ^ 3) by (apply pow_R1_Rle; lra).
      assert (1 <= exp (theta_of A d * Qn n + z)).
      { rewrite <- exp_0. apply exp_mono. assert (0 <= theta_of A d * Qn n) by (apply Rmult_le_pos; lra). lra. }
      nra. }
    lra. }
  split; [exact Hbound |]. split.
  - (* the supremum *)
    assert (Hbp : 0 <= bp).
    { unfold bp, psi. assert (1 <= (1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u)) by nra.
      assert (1 <= (1 + u) ^ 3) by (apply pow_R1_Rle; lra).
      assert (1 <= exp z) by (rewrite <- exp_0; apply exp_mono; lra).
      assert (Hq1 : 1 <= (1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) * (1 + u) ^ 3) by nra.
      assert (1 <= (1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) * (1 + u) ^ 3 * exp z) by nra.
      replace ((1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) - 1 + 1) with ((1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u)) by ring.
      nra. }
    pose proof (node_sup bp (theta_of A d) (Qn n) HQ Hbp (proj1 Hth') (proj2 Hth')) as Hns.
    unfold gn, vbn, vn.
    assert (Eexp : exp (theta_of A d * Qn n + z) = exp (theta_of A d * Qn n) * exp z) by apply exp_plus.
    set (f := exp (- Qn n)). set (W := nW n).
    set (E := exp (theta_of A d * Qn n)).
    assert (EexpE : exp (theta_of A d * Qn n + z) = E * exp z) by exact Eexp.
    assert (Hf0 : 0 < f) by apply exp_pos. assert (HW0 : 0 <= W) by (unfold W; lra).
    assert (Hid : psi etaK * (W * f) + (1 + psi etaK) * (W * f * ((1 + u) ^ 3 * exp (theta_of A d * Qn n + z) - 1))
                  = W * (f * ((1 + bp) * E - 1))).
    { unfold bp. rewrite EexpE. ring. }
    rewrite Hid. apply Rmult_le_compat_l; [exact HW0 | exact Hns].
  - split; [exact Hvn | split; [exact Hvb | ]].
    unfold tn, node_term, termf. split; [apply fmtF_rnd |].
    apply rnd_nonneg. apply Rmult_le_pos.
    + rewrite Hwh. rewrite <- (round_0 radix2 (FLT_exp (-1074) 53) (Znearest (fun n0 => negb (Z.even n0)))).
      apply round_le; [auto with typeclass_instances | auto with typeclass_instances | lra].
    + rewrite <- (round_0 radix2 (FLT_exp (-1074) 53) (Znearest (fun n0 => negb (Z.even n0)))).
      apply round_le; [auto with typeclass_instances | auto with typeclass_instances | left; apply exp_pos].
Qed.

Lemma rule_facts nodes dats :
  dom x -> dom y -> bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  Forall2 (node_ok asr A) nodes dats ->
  Rabs (sumR (map tn nodes) - sumR (map vn nodes)) <= sum2 vbn nodes dats + 3 * INR (length nodes) * z /\
  psi etaK * sumR (map vn nodes) + (1 + psi etaK) * sum2 vbn nodes dats <= sum2 gn nodes dats /\
  0 <= sumR (map vn nodes) /\ 0 <= sum2 vbn nodes dats /\
  (forall t, In t (map tn nodes) -> fmtF t /\ 0 <= t).
Proof.
  intros Hx Hy Ha1 Ha2 HA Hall.
  induction Hall as [| n d nodes dats Hok Hall IH].
  - simpl. repeat split; try lra. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct IH as [I1 [I2 [I3 [I4 I5]]]].
    destruct (node_facts n d Hx Hy Ha1 Ha2 HA Hok) as [F1 [F2 [F3 [F4 [F5 F6]]]]].
    pose proof z_pos as Hz.
    simpl map. simpl sumR. simpl sum2. simpl length. rewrite S_INR.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + assert (E : tn n + sumR (map tn nodes) - (vn n + sumR (map vn nodes))
                  = (tn n - vn n) + (sumR (map tn nodes) - sumR (map vn nodes))) by ring.
      rewrite E. eapply Rle_trans; [apply Rabs_triang |]. lra.
    + lra.
    + lra.
    + lra.
    + intros tt [Ht | Ht]; [rewrite <- Ht; split; assumption | apply I5; exact Ht].
Qed.

Lemma rule_bound nodes dats Kex Kh :
  dom x -> dom y -> bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  Forall2 (node_ok asr A) nodes dats -> (length nodes <= 24)%nat ->
  0 <= Kex -> Kex <= 1 -> Rabs (Kh - Kex) <= etaK * Kex -> etaK <= / 1000 ->
  Rabs (rndF (rndF (fst (acc (map tn nodes) (0, 0)) + snd (acc (map tn nodes) (0, 0))) * Kh)
        - Kex * sumR (map vn nodes))
    <= Kex * sum2 gn nodes dats + 1000 * z.
Proof.
  intros Hx Hy Ha1 Ha2 HA Hall Hlen HK0 HK1 HKh Heta1.
  destruct (rule_facts nodes dats Hx Hy Ha1 Ha2 HA Hall) as [I1 [I2 [I3 [I4 I5]]]].
  pose proof z_pos as Hz.
  assert (Hlen' : (length (map tn nodes) <= 24)%nat) by (rewrite map_length; exact Hlen).
  assert (Hl : INR (length nodes) <= 24) by (replace 24 with (INR 24) by (simpl; lra); apply le_INR; exact Hlen).
  assert (HT : Rabs (sumR (map tn nodes) - sumR (map vn nodes)) <= sum2 vbn nodes dats + 72 * z) by nra.
  pose proof (chain (map tn nodes) (sumR (map vn nodes)) (sum2 vbn nodes dats) Kex Kh etaK
    I5 Hlen' I3 I4 HT HK0 HK1 HKh Hetaa Heta1) as Hc.
  eapply Rle_trans; [exact Hc |].
  assert (Hm : Kex * (psi etaK * sumR (map vn nodes) + (1 + psi etaK) * sum2 vbn nodes dats) <= Kex * sum2 gn nodes dats)
    by (apply Rmult_le_compat_l; [exact HK0 | exact I2]).
  lra.
Qed.

Definition gdat (d : Dat) : R := dwhi d * Gsup bp (theta_of A d) (1 - theta_of A d).

Fixpoint sumD (f : Dat -> R) (l : list Dat) : R :=
  match l with nil => 0 | d :: l' => f d + sumD f l' end.

Lemma sum_g_le nodes dats :
  0 <= bp -> Forall2 (node_ok asr A) nodes dats -> sum2 gn nodes dats <= sumD gdat dats.
Proof.
  intros Hbp Hall. induction Hall as [| n d nodes dats Hok Hall IH]; simpl; [lra |].
  assert (Hg : gn n d <= gdat d).
  { unfold gn, gdat. destruct Hok as [_ [_ [_ [_ [_ [_ [HW [_ [_ [_ [_ [_ [_ Hth]]]]]]]]]]]]].
    destruct HW as [HW1 HW2].
    assert (HG : 0 <= Gsup bp (theta_of A d) (1 - theta_of A d)).
    { apply Gsup_nonneg; [exact Hbp | lra | lra]. }
    apply Rmult_le_compat_r; [exact HG | exact HW2]. }
  lra.
Qed.
End Rule.
