(** The double-word accumulation of the node terms (docs/bivariate_normal_high.md
    section 4.3): [two_sum] per term, the low parts added in order, and one final
    rounding of [hi + lo].  [TwoSum] is the library's error-free transform
    ([eft.rs], [IEEE64Eft.two_sum_ieee]); its exactness is the hypothesis
    [Hts]. *)
From Coq Require Import Reals Lra Psatz ZArith Lia List.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget.
Open Scope R_scope.

Fixpoint sabs (l : list R) : R := match l with nil => 0 | t :: l' => Rabs t + sabs l' end.
Fixpoint ssum (l : list R) : R := match l with nil => 0 | t :: l' => t + ssum l' end.

Section DW.
Variable ts : R -> R -> R * R.
(** [two_sum a b = (s, e)] with [s = rnd (a + b)] and [s + e = a + b]. *)
Hypothesis Hts : forall a b, fst (ts a b) = rnd (a + b) /\ fst (ts a b) + snd (ts a b) = a + b.

Fixpoint dwsum (hi lo : R) (l : list R) : R * R :=
  match l with
  | nil => (hi, lo)
  | t :: l' => let p := ts hi t in dwsum (fst p) (rnd (lo + snd p)) l'
  end.

Lemma sabs_nonneg l : 0 <= sabs l.
Proof. induction l as [|t l IH]; simpl; [lra|]. pose proof (Rabs_pos t). lra. Qed.

Lemma c55_small : c54 / 2 <= 1 / 10 ^ 16.
Proof. rewrite c54_value. interval. Qed.

Lemma dw_step hi lo t :
  Rabs (hi + t) < / 2 -> Rabs lo <= 1 / 10 ^ 12 ->
  let p := ts hi t in
  Rabs (fst p) <= Rabs (hi + t) + c54 / 2 /\
  Rabs (rnd (lo + snd p) - (lo + snd p)) <= 1 / 10 ^ 27 /\ Rabs (snd p) <= c54 / 2.
Proof.
  intros Hh Hl p. destruct (Hts hi t) as [H1 H2]. fold p in H1, H2.
  assert (Hb : Rabs (hi + t) < bpow radix2 (-1)) by (replace (bpow radix2 (-1)) with (/ 2) by (simpl; lra); exact Hh).
  pose proof (rnd_err_below (hi + t) (-1) ltac:(lia) Hb) as He.
  replace (-1 - 54)%Z with (-55)%Z in He by lia. rewrite c54_half in He.
  assert (Hs : Rabs (snd p) <= c54 / 2).
  { replace (snd p) with (-(rnd (hi + t) - (hi + t))) by (rewrite <- H1; lra). rewrite Rabs_Ropp. exact He. }
  assert (Hf : Rabs (fst p) <= Rabs (hi + t) + c54 / 2).
  { rewrite H1. pose proof (Rabs_triang (rnd (hi + t) - (hi + t)) (hi + t)).
    replace (rnd (hi + t) - (hi + t) + (hi + t)) with (rnd (hi + t)) in H by ring. lra. }
  pose proof (rnd_abs (lo + snd p)) as Hr.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη. pose proof c55_small as Hc.
  pose proof (Rabs_triang lo (snd p)) as Ht.
  assert (Hq : u * Rabs (lo + snd p) <= u * (1 / 10 ^ 12 + 1 / 10 ^ 16)) by (apply Rmult_le_compat_l; lra).
  assert (Hz : u * (1 / 10 ^ 12 + 1 / 10 ^ 16) + / 10 ^ 300 <= 1 / 10 ^ 27).
  { assert (12 / 10 ^ 17 * (1 / 10 ^ 12 + 1 / 10 ^ 16) + / 10 ^ 300 <= 1 / 10 ^ 27) by interval.
    assert (u * (1 / 10 ^ 12 + 1 / 10 ^ 16) <= 12 / 10 ^ 17 * (1 / 10 ^ 12 + 1 / 10 ^ 16)) by (apply Rmult_le_compat_r; [interval | lra]). lra. }
  repeat split; try lra.
Qed.

Lemma dw_ok l : forall hi lo,
  Rabs hi + sabs l + INR (length l) * (c54 / 2) < 46 / 100 ->
  Rabs lo + INR (length l) * (1 / 10 ^ 15) <= 1 / 10 ^ 12 ->
  let r := dwsum hi lo l in
  Rabs (fst r + snd r - (hi + lo + ssum l)) <= INR (length l) * (1 / 10 ^ 27) /\
  Rabs (snd r) <= Rabs lo + INR (length l) * (1 / 10 ^ 15) /\
  Rabs (fst r) <= Rabs hi + sabs l + INR (length l) * (c54 / 2).
Proof.
  induction l as [|t l IH]; intros hi lo H1 H2 r; cbn [sabs ssum length] in *.
  - subst r. cbn [dwsum fst snd]. replace (hi + lo - (hi + lo + 0)) with 0 by ring. rewrite Rabs_R0. cbn [INR]. repeat split; lra.
  - unfold r. cbn [dwsum].
    pose proof (Rabs_pos t) as Ht0. pose proof (sabs_nonneg l) as Hs0. pose proof (pos_INR (length l)) as Hn.
    pose proof c54_pos as Hc. pose proof (Rabs_pos hi) as Hh0. pose proof (Rabs_pos lo) as Hl0.
    pose proof c55_small as Hc55.
    rewrite S_INR in H1, H2.
    rewrite S_INR.

    assert (Hn1 : 0 <= INR (length l) * (c54 / 2)) by (apply Rmult_le_pos; lra).
    assert (Hn2 : 0 <= INR (length l) * (1 / 10 ^ 15)) by (apply Rmult_le_pos; [lra | interval]).
    pose proof (Rabs_triang hi t) as Htr.
    rewrite Rmult_plus_distr_r in H1. rewrite Rmult_plus_distr_r in H2.
    assert (Hsum : Rabs (hi + t) < / 2) by lra.
    assert (Hlo : Rabs lo <= 1 / 10 ^ 12).
    { assert (0 <= 1 * (1 / 10 ^ 15)) by interval. lra. }
    destruct (dw_step hi lo t Hsum Hlo) as [Hf [Hr Hsn]].
    destruct (Hts hi t) as [E1 E2].
    set (p := ts hi t) in *.
    set (lo' := rnd (lo + snd p)) in *.
    assert (Hh' : Rabs (fst p) + sabs l + INR (length l) * (c54 / 2) < 46 / 100) by lra.
    pose proof (Rabs_triang lo (snd p)) as Hlp.
    pose proof (Rabs_triang (lo' - (lo + snd p)) (lo + snd p)) as Hlq.
    replace (lo' - (lo + snd p) + (lo + snd p)) with lo' in Hlq by ring.
    assert (Hz : 1 / 10 ^ 27 + c54 / 2 <= 1 / 10 ^ 15) by (assert (1 / 10 ^ 27 + 1 / 10 ^ 16 <= 1 / 10 ^ 15) by interval; lra).
    assert (Hl' : Rabs lo' + INR (length l) * (1 / 10 ^ 15) <= 1 / 10 ^ 12) by lra.
    specialize (IH (fst p) lo' Hh' Hl').
    cbv zeta in IH. destruct (dwsum (fst p) lo' l) as [h l2]. cbn [fst snd] in *.
    destruct IH as [I1 [I2 I3]].
    repeat split.
    + replace (h + l2 - (hi + lo + (t + ssum l))) with ((h + l2 - (fst p + lo' + ssum l)) + (lo' - (lo + snd p))) by lra.
      pose proof (Rabs_triang (h + l2 - (fst p + lo' + ssum l)) (lo' - (lo + snd p))) as Hq.
      rewrite Rmult_plus_distr_r. lra.
    + rewrite Rmult_plus_distr_r. lra.
    + rewrite Rmult_plus_distr_r. lra.
Qed.
End DW.
