(** The double-word accumulation of the quadrature sum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Interval Require Import Tactic.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound.
Open Scope R_scope.

Lemma two_sum_exact a b : fmtF a -> fmtF b ->
  fst (two_sum a b) + snd (two_sum a b) = a + b /\ fmtF (fst (two_sum a b)) /\ fmtF (snd (two_sum a b))
  /\ fst (two_sum a b) = rndF (a + b).
Proof.
  intros Fa Fb.
  pose proof (two_sum_eq a b Fa Fb) as E.
  pose proof (two_sum_fmt a b Fa Fb) as [Fs Fe].
  pose proof (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl a b (fmtF_fmtX a Fa) (fmtF_fmtX b Fb)) as C.
  rewrite E. cbn [fst snd].
  repeat split; try assumption.
  - lra.
  - unfold TwoSum_sum. unfold TwoSum. simpl. symmetry. apply sum_round; assumption.
Qed.

Definition step (hl : R * R) (t : R) : R * R :=
  let '(h, l) := hl in
  let '(s, e) := two_sum h t in (s, rndF (l + e)).

Fixpoint acc (ts : list R) (hl : R * R) : R * R :=
  match ts with
  | nil => hl
  | t :: ts' => acc ts' (step hl t)
  end.

Fixpoint sumR (ts : list R) : R :=
  match ts with nil => 0 | t :: ts' => t + sumR ts' end.

Lemma step_spec h l t : fmtF h -> fmtF l -> fmtF t -> 0 <= h -> 0 <= t ->
  exists s e, step (h, l) t = (s, rndF (l + e)) /\ fmtF s /\ fmtF e /\ 0 <= s
    /\ s + e = h + t /\ Rabs e <= u * (h + t) /\ s <= (1 + u) * (h + t).
Proof.
  intros Fh Fl Ft Hh Ht.
  destruct (two_sum_exact h t Fh Ft) as [Hex [Fs [Fe Hs]]].
  exists (fst (two_sum h t)), (snd (two_sum h t)).
  assert (Hst : step (h, l) t = (fst (two_sum h t), rndF (l + snd (two_sum h t)))).
  { unfold step. destruct (two_sum h t) as [s e]. reflexivity. }
  destruct (rnd_add_delta h t Fh Ft) as [d [Hd Ed]].
  pose proof u_pos as Hu. apply Rabs_le_inv in Hd. destruct Hd as [Hd1 Hd2].
  assert (Hhs : 0 <= h + t) by lra.
  assert (H0s : 0 <= fst (two_sum h t)) by (rewrite Hs; apply rnd_nonneg; exact Hhs).
  assert (Hee : Rabs (snd (two_sum h t)) <= u * (h + t)).
  { assert (E : snd (two_sum h t) = (h + t) - rndF (h + t)) by (rewrite <- Hs; lra).
    rewrite Ed in E.
    assert (E2 : snd (two_sum h t) = - ((h + t) * d)) by (rewrite E; ring). rewrite E2.
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (h + t)) by exact Hhs.
    assert (Rabs d <= u) by (apply Rabs_le; lra). nra. }
  assert (Hsu : fst (two_sum h t) <= (1 + u) * (h + t)) by (rewrite Hs, Ed; nra).
  exact (conj Hst (conj Fs (conj Fe (conj H0s (conj Hex (conj Hee Hsu)))))).
Qed.

Lemma sumR_nonneg ts : (forall t, In t ts -> 0 <= t) -> 0 <= sumR ts.
Proof.
  induction ts as [| a ts IH]; intros H; simpl.
  - lra.
  - assert (0 <= a) by (apply H; left; reflexivity).
    assert (0 <= sumR ts) by (apply IH; intros t Ht; apply H; right; exact Ht). lra.
Qed.

Lemma pow_le_two j : (j <= 24)%nat -> (1 + u) ^ j <= 2.
Proof.
  intros Hj.
  assert (H24 : (1 + u) ^ 24 <= 2).
  { rewrite u_val. interval. }
  eapply Rle_trans; [| exact H24].
  apply Rle_pow; [pose proof u_pos; lra | exact Hj].
Qed.

Section Acc.
Variable T : R.
Hypothesis HT : 0 <= T.
Let c : R := 3 * u * T + 2 * z.
Let eps : R := u * (24 * c + 2 * u * T) + z.

Lemma acc_inv ts : forall h l j,
  fmtF h -> fmtF l -> 0 <= h ->
  (forall t, In t ts -> fmtF t /\ 0 <= t) ->
  h + sumR ts <= T * (1 + u) ^ j -> Rabs l <= INR j * c -> (j + length ts <= 24)%nat ->
  fmtF (fst (acc ts (h, l))) /\ fmtF (snd (acc ts (h, l))) /\
  Rabs (snd (acc ts (h, l))) <= INR (j + length ts) * c /\
  Rabs (fst (acc ts (h, l)) + snd (acc ts (h, l)) - (h + l + sumR ts)) <= INR (length ts) * eps.
Proof.
  induction ts as [| t ts IH]; intros h l j Fh Fl Hh Hts HT1 Hl Hj.
  - simpl. repeat split; try assumption.
    + rewrite Nat.add_0_r. exact Hl.
    + replace (h + l - (h + l + 0)) with 0 by ring. rewrite Rabs_R0. simpl. lra.
  - destruct (Hts t (or_introl eq_refl)) as [Ft Ht0].
    destruct (step_spec h l t Fh Fl Ft Hh Ht0) as [s [e [Hst [Fs [Fe [Hs0 [Hse [He Hsu]]]]]]]].
    assert (Hrest : 0 <= sumR ts) by (apply sumR_nonneg; intros t' Ht'; apply (Hts t'); right; exact Ht').
    simpl in HT1. simpl in Hj.
    pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz0.
    assert (Hpj : (1 + u) ^ j <= 2) by (apply pow_le_two; lia).
    assert (Hpp : 0 < (1 + u) ^ j) by (apply pow_lt; lra).
    assert (HhtT : h + t <= T * (1 + u) ^ j) by lra.
    assert (HeT : Rabs e <= 2 * u * T).
    { eapply Rle_trans; [exact He |]. assert (u * (h + t) <= u * (T * (1 + u) ^ j)) by (apply Rmult_le_compat_l; lra).
      assert (T * (1 + u) ^ j <= T * 2) by (apply Rmult_le_compat_l; lra). nra. }
    assert (Hj23 : (j <= 23)%nat) by lia.
    assert (Hjc : INR j <= 23) by (replace 23 with (INR 23) by (simpl; lra); apply le_INR; exact Hj23).
    assert (Hc0 : 0 <= c) by (unfold c; nra).
    assert (Hle : Rabs (l + e) <= INR j * c + 2 * u * T).
    { eapply Rle_trans; [apply Rabs_triang |]. lra. }
    pose proof (rnd_rel_z (l + e)) as Hr.
    set (l2 := rndF (l + e)) in *.
    assert (Hl2 : Rabs l2 <= INR (S j) * c).
    { assert (Hl2' : Rabs l2 <= (1 + u) * Rabs (l + e) + z).
      { assert (Rabs l2 <= Rabs (l + e) + Rabs (l2 - (l + e))).
        { assert (E : l2 = (l + e) + (l2 - (l + e))) by ring. rewrite E at 1. apply Rabs_triang. }
        nra. }
      rewrite S_INR.
      assert (Hk : (1 + u) * (INR j * c + 2 * u * T) + z <= (INR j + 1) * c).
      { unfold c. nra. }
      assert (Hm : (1 + u) * Rabs (l + e) <= (1 + u) * (INR j * c + 2 * u * T)) by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (Herr : Rabs (l2 - (l + e)) <= eps).
    { eapply Rle_trans; [exact Hr |]. unfold eps.
      assert (Hm : u * Rabs (l + e) <= u * (24 * c + 2 * u * T)) by (apply Rmult_le_compat_l; [lra | nra]).
      lra. }
    assert (HsT : s + sumR ts <= T * (1 + u) ^ S j).
    { rewrite <- tech_pow_Rmult.
      assert (Hx : (1 + u) * (h + t + sumR ts) <= (1 + u) * (T * (1 + u) ^ j)) by (apply Rmult_le_compat_l; lra).
      assert (Hy : s + sumR ts <= (1 + u) * (h + t + sumR ts)) by nra.
      nra. }
    assert (Hts' : forall t', In t' ts -> fmtF t' /\ 0 <= t') by (intros t' Ht'; apply Hts; right; exact Ht').
    assert (Hac : acc (t :: ts) (h, l) = acc ts (step (h, l) t)) by reflexivity.
    rewrite Hac, Hst. cbn [length sumR].
    destruct (IH s l2 (S j) Fs (fmtF_rnd (l + e)) Hs0 Hts' HsT Hl2 ltac:(lia)) as [Ia [Ib [Ic Id]]].
    repeat split; try assumption.
    + replace (S j + length ts)%nat with (j + S (length ts))%nat in Ic by lia. exact Ic.
    + rewrite S_INR.
      assert (E : fst (acc ts (s, l2)) + snd (acc ts (s, l2)) - (h + l + (t + sumR ts))
                  = (fst (acc ts (s, l2)) + snd (acc ts (s, l2)) - (s + l2 + sumR ts)) + (l2 - (l + e))).
      { assert (s + e = h + t) by exact Hse. nra. }
      rewrite E. eapply Rle_trans; [apply Rabs_triang |].
      assert (Hpos : 0 <= INR (length ts)) by apply pos_INR. nra.
Qed.
End Acc.

(** The accumulated high and low words sum to the exact total of the terms,
    up to [2000 u^2] relative and [30 z]. *)
Lemma acc_final ts :
  (forall t, In t ts -> fmtF t /\ 0 <= t) -> (length ts <= 24)%nat ->
  fmtF (fst (acc ts (0, 0))) /\ fmtF (snd (acc ts (0, 0))) /\
  Rabs (fst (acc ts (0, 0)) + snd (acc ts (0, 0)) - sumR ts) <= 2000 * u * u * sumR ts + 30 * z /\
  Rabs (snd (acc ts (0, 0))) <= 24 * (3 * u * sumR ts + 2 * z).
Proof.
  intros Hts Hn.
  assert (HT : 0 <= sumR ts) by (apply sumR_nonneg; intros t Ht; apply (Hts t Ht)).
  assert (F0 : fmtF 0) by apply generic_format_0.
  pose proof (acc_inv (sumR ts) HT ts 0 0 0%nat F0 F0 (Rle_refl 0) Hts) as H.
  assert (H1 : 0 + sumR ts <= sumR ts * (1 + u) ^ 0%nat) by (simpl; lra).
  assert (H2 : Rabs 0 <= INR 0%nat * (3 * u * sumR ts + 2 * z)) by (rewrite Rabs_R0; simpl; lra).
  specialize (H H1 H2 ltac:(lia)).
  destruct H as [Fa [Fb [Hl Hd]]].
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz0.
  assert (HlL : Rabs (snd (acc ts (0, 0))) <= 24 * (3 * u * sumR ts + 2 * z)).
  { eapply Rle_trans; [exact Hl |]. rewrite Nat.add_0_l.
    assert (Hln : INR (length ts) <= 24) by (replace 24 with (INR 24) by (simpl; lra); apply le_INR; exact Hn).
    assert (Hc0 : 0 <= 3 * u * sumR ts + 2 * z) by nra.
    nra. }
  refine (conj Fa (conj Fb (conj _ HlL))).
  replace (0 + 0 + sumR ts) with (sumR ts) in Hd by ring.
  eapply Rle_trans; [exact Hd |].
  assert (Hl2 : INR (length ts) <= 24) by (replace 24 with (INR 24) by (simpl; lra); apply le_INR; exact Hn).
  assert (He : 0 <= u * (24 * (3 * u * sumR ts + 2 * z) + 2 * u * sumR ts) + z) by nra.
  assert (Hk : u * (24 * (3 * u * sumR ts + 2 * z) + 2 * u * sumR ts) + z <= 80 * u * u * sumR ts + 2 * z) by nra.
  assert (Hm : INR (length ts) * (u * (24 * (3 * u * sumR ts + 2 * z) + 2 * u * sumR ts) + z)
                <= 24 * (80 * u * u * sumR ts + 2 * z)) by nra.
  nra.
Qed.

(** Rounding is odd, so a list of non-positive terms accumulates as the
    negation of the list of their negations. *)
Lemma two_sum_opp a b : two_sum (- a) (- b) = (- fst (two_sum a b), - snd (two_sum a b)).
Proof.
  unfold two_sum.
  replace (- a + - b) with (- (a + b)) by ring. rewrite rnd_opp.
  set (s := rndF (a + b)).
  replace (- s - - b) with (- (s - b)) by ring. rewrite rnd_opp.
  set (a' := rndF (s - b)).
  replace (- s - - a') with (- (s - a')) by ring. rewrite rnd_opp.
  set (b' := rndF (s - a')).
  replace (- a - - a') with (- (a - a')) by ring. rewrite rnd_opp.
  replace (- b - - b') with (- (b - b')) by ring. rewrite rnd_opp.
  replace (- rndF (a - a') + - rndF (b - b')) with (- (rndF (a - a') + rndF (b - b'))) by ring.
  rewrite rnd_opp. reflexivity.
Qed.

Lemma step_opp h l t : step (- h, - l) (- t) = (- fst (step (h, l) t), - snd (step (h, l) t)).
Proof.
  unfold step. rewrite two_sum_opp.
  destruct (two_sum h t) as [s e]. simpl.
  replace (- l + - e) with (- (l + e)) by ring. rewrite rnd_opp. reflexivity.
Qed.

Lemma acc_cons t ts hl : acc (t :: ts) hl = acc ts (step hl t).
Proof. reflexivity. Qed.

Lemma acc_opp ts : forall h l,
  acc (map Ropp ts) (- h, - l) = (- fst (acc ts (h, l)), - snd (acc ts (h, l))).
Proof.
  induction ts as [| t ts IH]; intros h l.
  - reflexivity.
  - rewrite map_cons, !acc_cons, step_opp.
    destruct (step (h, l) t) as [s l2] eqn:Hs. simpl. apply IH.
Qed.

Lemma sumR_opp ts : sumR (map Ropp ts) = - sumR ts.
Proof. induction ts as [| t ts IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma acc_final_neg ts :
  (forall t, In t ts -> fmtF t /\ t <= 0) -> (length ts <= 24)%nat ->
  fmtF (fst (acc ts (0, 0))) /\ fmtF (snd (acc ts (0, 0))) /\
  Rabs (fst (acc ts (0, 0)) + snd (acc ts (0, 0)) - sumR ts) <= 2000 * u * u * Rabs (sumR ts) + 30 * z /\
  Rabs (snd (acc ts (0, 0))) <= 24 * (3 * u * Rabs (sumR ts) + 2 * z).
Proof.
  intros Hts Hn.
  assert (Hts' : forall t, In t (map Ropp ts) -> fmtF t /\ 0 <= t).
  { intros t Ht. apply in_map_iff in Ht. destruct Ht as [t0 [E Ht0]]. subst t.
    destruct (Hts t0 Ht0) as [F H0]. split; [apply generic_format_opp; exact F | lra]. }
  assert (Hn' : (length (map Ropp ts) <= 24)%nat) by (rewrite map_length; exact Hn).
  destruct (acc_final (map Ropp ts) Hts' Hn') as [F1 [F2 [Hb HbL]]].
  assert (E : acc ts (0, 0) = (- fst (acc (map Ropp ts) (0, 0)), - snd (acc (map Ropp ts) (0, 0)))).
  { assert (Hz : acc (map Ropp (map Ropp ts)) (- 0, - 0) = (- fst (acc (map Ropp ts) (0, 0)), - snd (acc (map Ropp ts) (0, 0)))) by (apply acc_opp).
    rewrite map_map in Hz. rewrite (map_ext (fun x => Ropp (Ropp x)) (fun x => x)) in Hz by (intros; ring).
    rewrite map_id in Hz. replace (- 0) with 0 in Hz by ring. exact Hz. }
  rewrite E. simpl.
  rewrite sumR_opp in Hb.
  assert (Hsn : sumR (map Ropp ts) = - sumR ts) by apply sumR_opp.
  assert (Hnn : 0 <= sumR (map Ropp ts)) by (apply sumR_nonneg; intros t Ht; apply (Hts' t Ht)).
  rewrite Hsn in Hnn.
  split; [apply generic_format_opp; exact F1 |]. split; [apply generic_format_opp; exact F2 |].
  rewrite (Rabs_left1 (sumR ts)) by lra.
  split; [| rewrite Rabs_Ropp; rewrite Hsn in HbL; exact HbL].
  assert (Ee : - fst (acc (map Ropp ts) (0, 0)) + - snd (acc (map Ropp ts) (0, 0)) - sumR ts
               = - (fst (acc (map Ropp ts) (0, 0)) + snd (acc (map Ropp ts) (0, 0)) - - sumR ts)) by ring.
  rewrite Ee, Rabs_Ropp. exact Hb.
Qed.
