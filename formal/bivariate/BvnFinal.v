(** The last stage of the low-correlation branch: the product of the two
    distribution functions kept as a double-word, the double-word sum of the
    terms, and one final rounding with the clamp. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Interval Require Import Tactic.
Require TwoProdBinary64.
Require Import BvnRound BvnSum BvnTail.
Open Scope R_scope.

Definition PFLOOR : R := / 10 ^ 270.

Definition prod_lo (pxI pyI : R) : R :=
  let hi := TwoProdBinary64.two_prod_p pxI pyI in
  if Rle_dec PFLOOR hi then TwoProdBinary64.two_prod_e pxI pyI else 0.

(** The result from the product's two words and the accumulator's two words. *)
Definition finish (pxI pyI H L : R) : R :=
  let hi := TwoProdBinary64.two_prod_p pxI pyI in
  let lo := prod_lo pxI pyI in
  let se := two_sum hi H in
  clampf (rndF (fst se + rndF (snd se + rndF (L + lo)))).

Lemma two_prod_p_eq a b : TwoProdBinary64.two_prod_p a b = rndF (a * b).
Proof. reflexivity. Qed.

Lemma PFLOOR_pos : 0 < PFLOOR.
Proof. unfold PFLOOR. apply Rinv_0_lt_compat. apply pow_lt. lra. Qed.

Lemma PFLOOR_big : bpow radix2 (-969) < PFLOOR.
Proof. unfold PFLOOR. simpl. interval. Qed.

Lemma PFLOOR_z : z <= PFLOOR / 4.
Proof. unfold z, PFLOOR. simpl. interval. Qed.

Lemma PFLOOR_u : 3 * PFLOOR * u + z <= bpow radix2 (-900).
Proof. unfold PFLOOR, z, u. simpl. interval. Qed.

Lemma prod_words pxI pyI : fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (TwoProdBinary64.two_prod_p pxI pyI + prod_lo pxI pyI - pxI * pyI) <= bpow radix2 (-900)
  /\ Rabs (prod_lo pxI pyI) <= bpow radix2 (-54).
Proof.
  intros Fa Fb [Ha0 Ha1] [Hb0 Hb1].
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (Hab0 : 0 <= pxI * pyI) by (apply Rmult_le_pos; lra).
  assert (Hab1 : pxI * pyI <= 1) by nra.
  rewrite two_prod_p_eq. unfold prod_lo. rewrite two_prod_p_eq.
  destruct (Rle_dec PFLOOR (rndF (pxI * pyI))) as [Hf | Hf].
  - assert (Hbig : bpow radix2 (-969) <= Rabs (pxI * pyI)).
    { destruct (Rle_or_lt (bpow radix2 (-969)) (Rabs (pxI * pyI))) as [H | H]; [exact H |].
      exfalso. rewrite Rabs_pos_eq in H by exact Hab0.
      assert (Hg : rndF (bpow radix2 (-969)) = bpow radix2 (-969)).
      { apply round_generic; [auto with typeclass_instances |]. apply generic_format_bpow. unfold FLT_exp. apply Z.max_lub; lia. }
      assert (Hr : rndF (pxI * pyI) <= rndF (bpow radix2 (-969))) by (apply rnd_mono; lra).
      rewrite Hg in Hr.
      pose proof PFLOOR_big. lra. }
    pose proof (TwoProdBinary64.two_prod_exact pxI pyI Fa Fb (or_intror Hbig)) as Hx.
    rewrite two_prod_p_eq in Hx.
    split.
    + replace (rndF (pxI * pyI) + TwoProdBinary64.two_prod_e pxI pyI - pxI * pyI) with 0.
      * rewrite Rabs_R0. left. apply bpow_gt_0.
      * lra.
    + assert (Hr : Rabs (rndF (pxI * pyI) - pxI * pyI) <= bpow radix2 (-54)).
      { replace (-54)%Z with (0 - 54)%Z by reflexivity. apply rnd_pow; [lia |].
        replace (bpow radix2 0) with 1 by reflexivity. rewrite Rabs_pos_eq by exact Hab0. exact Hab1. }
      assert (E : TwoProdBinary64.two_prod_e pxI pyI = pxI * pyI - rndF (pxI * pyI)) by lra.
      rewrite E. rewrite Rabs_minus_sym. exact Hr.
  - split.
    + replace (rndF (pxI * pyI) + 0 - pxI * pyI) with (rndF (pxI * pyI) - pxI * pyI) by ring.
      pose proof (rnd_rel_z (pxI * pyI)) as Hr.
      assert (Hlt : rndF (pxI * pyI) < PFLOOR) by lra.
      assert (Hab : pxI * pyI <= 3 * PFLOOR).
      { assert (E : pxI * pyI = rndF (pxI * pyI) - (rndF (pxI * pyI) - pxI * pyI)) by ring.
        assert (H0 : Rabs (pxI * pyI) <= Rabs (rndF (pxI * pyI)) + Rabs (rndF (pxI * pyI) - pxI * pyI)) by (rewrite E at 1; eapply Rle_trans; [apply Rabs_triang |]; rewrite Rabs_Ropp; lra).
        rewrite (Rabs_pos_eq (pxI * pyI)) in H0 by exact Hab0.
        assert (Hrr : 0 <= rndF (pxI * pyI)) by (rewrite <- rnd_zero; apply rnd_mono; lra).
        rewrite (Rabs_pos_eq (rndF (pxI * pyI))) in H0 by exact Hrr.
        pose proof PFLOOR_pos. pose proof PFLOOR_z.
        assert (Hr' : Rabs (rndF (pxI * pyI) - pxI * pyI) <= u * (pxI * pyI) + z) by (rewrite (Rabs_pos_eq (pxI * pyI)) in Hr by exact Hab0; exact Hr).
        assert (Hm : u * (pxI * pyI) <= / 2 * (pxI * pyI)) by (apply Rmult_le_compat_r; [exact Hab0 | rewrite Huv; lra]).
        lra. }
      eapply Rle_trans; [exact Hr |].
      pose proof PFLOOR_pos. pose proof PFLOOR_u as Hb900.
      assert (Hm : u * Rabs (pxI * pyI) <= u * (3 * PFLOOR)) by (apply Rmult_le_compat_l; [lra | rewrite Rabs_pos_eq by exact Hab0; exact Hab]).
      lra.
    + rewrite Rabs_R0. left. apply bpow_gt_0.
Qed.

Lemma small_consts : u * bpow radix2 (-39) + z + u * (5 * u + bpow radix2 (-38)) + z <= bpow radix2 (-90).
Proof. unfold u, z. simpl. interval. Qed.

Lemma finish_bound pxI pyI H L P :
  fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  fmtF H -> Rabs H <= 4 -> Rabs L <= bpow radix2 (-40) -> 0 <= P <= 1 ->
  Rabs (finish pxI pyI H L - P)
    <= Rabs (pxI * pyI + H + L - P) + bpow radix2 (-900) + bpow radix2 (-54) + bpow radix2 (-90).
Proof.
  intros Fa Fb Ha Hb FH HH HL HP.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  destruct (prod_words pxI pyI Fa Fb Ha Hb) as [Hw Hlo].
  set (hi := TwoProdBinary64.two_prod_p pxI pyI) in *.
  set (lo := prod_lo pxI pyI) in *.
  assert (Fhi : fmtF hi) by (unfold hi; rewrite two_prod_p_eq; apply fmtF_rnd).
  assert (Hhi : 0 <= hi <= 1).
  { unfold hi. rewrite two_prod_p_eq. destruct (rnd_unit (pxI * pyI)) as [[R0 R1] _]; [split; nra | split; assumption]. }
  destruct (two_sum_exact hi H Fhi FH) as [Hex [Fs [Fe Hs]]].
  set (s1 := fst (two_sum hi H)) in *. set (e := snd (two_sum hi H)) in *.
  destruct (rnd_add_delta hi H Fhi FH) as [d [Hd Ed]].
  assert (He : Rabs e <= 5 * u).
  { assert (Ee : e = hi + H - rndF (hi + H)) by (rewrite <- Hs; lra).
    rewrite Ee, Ed. replace (hi + H - (hi + H) * (1 + d)) with (- ((hi + H) * d)) by ring.
    rewrite Rabs_Ropp, Rabs_mult.
    assert (Rabs (hi + H) <= 5) by (eapply Rle_trans; [apply Rabs_triang |]; rewrite (Rabs_pos_eq hi (proj1 Hhi)); lra).
    pose proof (Rabs_pos d). pose proof (Rabs_pos (hi + H)). nra. }
  set (tt := rndF (L + lo)).
  assert (Ht : Rabs (tt - (L + lo)) <= u * Rabs (L + lo) + z) by exact (rnd_rel_z (L + lo)).
  assert (HLl : Rabs (L + lo) <= bpow radix2 (-39)).
  { eapply Rle_trans; [apply Rabs_triang |].
    assert (bpow radix2 (-40) + bpow radix2 (-54) <= bpow radix2 (-39)).
    { replace (-39)%Z with (-40 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2.
      assert (bpow radix2 (-54) <= bpow radix2 (-40)) by (apply bpow_le; lia). lra. }
    lra. }
  assert (Htt : Rabs tt <= bpow radix2 (-38)).
  { assert (E : tt = (L + lo) + (tt - (L + lo))) by ring.
    assert (Rabs tt <= Rabs (L + lo) + Rabs (tt - (L + lo))) by (rewrite E at 1; apply Rabs_triang).
    assert (Hm : u * Rabs (L + lo) <= u * bpow radix2 (-39)) by (apply Rmult_le_compat_l; [lra | exact HLl]).
    assert (bpow radix2 (-39) * 2 = bpow radix2 (-38)) by (replace (-38)%Z with (-39 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    assert (u * bpow radix2 (-39) <= bpow radix2 (-39) / 4) by (rewrite Huv; pose proof (bpow_gt_0 radix2 (-39)); nra).
    assert (z <= bpow radix2 (-39) / 4) by (unfold z; assert (bpow radix2 (-1075) <= bpow radix2 (-45)) by (apply bpow_le; lia); assert (bpow radix2 (-39) = 64 * bpow radix2 (-45)) by (replace (-39)%Z with (-45 + 6)%Z by reflexivity; rewrite bpow_plus; replace (bpow radix2 6) with 64 by reflexivity; ring); pose proof (bpow_gt_0 radix2 (-45)); lra).
    lra. }
  set (r := rndF (e + tt)).
  assert (Hr : Rabs (r - (e + tt)) <= u * Rabs (e + tt) + z) by exact (rnd_rel_z (e + tt)).
  assert (Her : Rabs (r - (e + L + lo)) <= bpow radix2 (-90)).
  { assert (E : r - (e + L + lo) = (r - (e + tt)) + (tt - (L + lo))) by ring.
    rewrite E. eapply Rle_trans; [apply Rabs_triang |].
    assert (Hett : Rabs (e + tt) <= 5 * u + bpow radix2 (-38)) by (eapply Rle_trans; [apply Rabs_triang | lra]).
    assert (Hm1 : u * Rabs (e + tt) <= u * (5 * u + bpow radix2 (-38))) by (apply Rmult_le_compat_l; [lra | exact Hett]).
    assert (Hm2 : u * Rabs (L + lo) <= u * bpow radix2 (-39)) by (apply Rmult_le_compat_l; [lra | exact HLl]).
    pose proof small_consts. lra. }
  assert (Hdef : finish pxI pyI H L = clampf (rndF (s1 + r))) by reflexivity.
  rewrite Hdef.
  pose proof (clamp_round (s1 + r) P HP) as Hcl.
  assert (Hsx : s1 + r - P = (r - (e + L + lo)) + ((hi + lo - pxI * pyI) + (pxI * pyI + H + L - P))).
  { assert (s1 + e = hi + H) by exact Hex. lra. }
  assert (Hab : Rabs (s1 + r - P) <= bpow radix2 (-90) + (bpow radix2 (-900) + Rabs (pxI * pyI + H + L - P))).
  { rewrite Hsx. eapply Rle_trans; [apply Rabs_triang |]. eapply Rle_trans; [apply Rplus_le_compat_l; apply Rabs_triang |].
    lra. }
  lra.
Qed.
