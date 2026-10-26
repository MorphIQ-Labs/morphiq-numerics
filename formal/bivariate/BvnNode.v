(** One quadrature term, [rndF (wh * expI (-a'))], against
    [W * exp(-Q(sin t))] at the exact node angle [t]. [a'] is the computed
    exponent argument of BvnArg.v at the rounded sine [sh] of the computed
    angle [th], [|th - t| <= dth]. The library [exp] enters through its
    contract: a rounding of a value within [2^-100] relatively of [e^v]
    (docs/exp.md proves correct rounding, a stronger statement). *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Flocq Require Import Core.
Require Import BvnRound BvnQ BvnArg.
Open Scope R_scope.

Definition termf (expI : R -> R) (x y sh wh : R) : R :=
  rndF (wh * expI (- argnc x y sh)).

Definition ue : R := u * (1 + bpow radix2 (-100)) + bpow radix2 (-100).
Definition rx : R := ue + u * (1 + ue).

Lemma ue_small : 0 < ue /\ ue <= 2 * u.
Proof.
  unfold ue. pose proof u_pos as Hu. pose proof u_val as Huv.
  pose proof (bpow_gt_0 radix2 (-100)) as H.
  assert (Hb : bpow radix2 (-100) <= u / 16).
  { assert (E : u / 16 = bpow radix2 (-57)) by (unfold u; replace (-57)%Z with (-53 + -4)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 (-4)) with (/ 16); field).
    rewrite E. apply bpow_le. lia. }
  assert (Hm : u * bpow radix2 (-100) <= u * (u / 16)) by (apply Rmult_le_compat_l; lra).
  split; nra.
Qed.

Lemma node_err (expI : R -> R) x y t th sh W wh dth sg hs_ ew :
  (forall v, exists Zc, expI v = rndF Zc /\ Rabs (Zc - exp v) <= bpow radix2 (-100) * exp v) ->
  fmtF x -> fmtF y -> fmtF sh -> Rabs x <= 64 -> Rabs y <= 64 ->
  Rabs (th - t) <= dth -> Rabs (sin t) < 1 -> Rabs (sin th) <= sg ->
  Rabs (sh - sin th) <= hs_ -> sg + hs_ <= 99 / 100 -> 0 <= hs_ -> 0 <= dth ->
  Rabs (wh - W) <= ew * Rabs W -> 0 <= ew -> Rabs wh <= 1 -> 0 <= sg ->
  let r := x * x + y * y in
  let p := x * y in
  let eps1 := (dth + hs_) / (1 - (sg + hs_)) in
  let theta := eps1 + (1 + eps1) * (71 / 10 * u) in
  Rabs (termf expI x y sh wh - W * exp (- Qf r p (sin t)))
    <= Rabs W * exp (- Qf r p (sin t)) * ((1 + ew) * (1 + rx) * exp (theta * Qf r p (sin t) + 300 * z) - 1) + 3 * z.
Proof.
  intros Hexp Fx Fy Fs Hx Hy Hdth Hst Hsin Hsh Hsg Hhs Hdth0 HwW Hew Hwh Hsg0 r p eps1 theta.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  destruct ue_small as [Hue0 Hue1].
  assert (Hr : 0 <= r) by (unfold r; nra).
  assert (Hp : Rabs p <= r / 2).
  { unfold p, r. pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2. unfold Rsqr in h1, h2.
    apply Rabs_le. split; nra. }
  set (a := argnc x y sh).
  set (S := sin th) in *. set (s := sin t) in *.
  assert (HshB : Rabs sh <= sg + hs_).
  { assert (E : sh = S + (sh - S)) by ring.
    assert (Rabs sh <= Rabs S + Rabs (sh - S)) by (rewrite E at 1; apply Rabs_triang). lra. }
  assert (Hshs : Rabs sh < 1) by lra.
  pose proof (arg_nc x y sh (sg + hs_) Fx Fy Fs Hx Hy HshB Hsg) as Harg.
  fold r in Harg. fold p in Harg. fold a in Harg.
  set (QS := Qf r p sh) in *. set (Qs := Qf r p s) in *.
  pose proof (Qf_nonneg r p s Hr Hp Hst) as HQs0. fold Qs in HQs0.
  pose proof (Qf_nonneg r p sh Hr Hp Hshs) as HQS0. fold QS in HQS0.
  assert (Hsd : Rabs (sh - s) <= dth + hs_).
  { assert (E : sh - s = (sh - S) + (S - s)) by ring. rewrite E.
    eapply Rle_trans; [apply Rabs_triang |].
    assert (Rabs (S - s) <= dth) by (eapply Rle_trans; [apply sin_lip | exact Hdth]). lra. }
  assert (H1S : 0 < 1 - (sg + hs_)) by lra.
  assert (HqD : Rabs (QS - Qs) <= eps1 * Qs).
  { pose proof (Q_diff r p sh s Hr Hp Hshs Hst) as H. fold QS in H. fold Qs in H.
    assert (Hc : Rabs (sh - s) / (1 - Rabs sh) <= eps1).
    { unfold eps1. apply Rle_trans with ((dth + hs_) / (1 - Rabs sh)).
      - unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Hsd].
      - unfold Rdiv. apply Rmult_le_compat_l; [lra |]. apply Rinv_le_contravar; lra. }
    eapply Rle_trans; [exact H |]. apply Rmult_le_compat_r; [exact HQs0 | exact Hc]. }
  assert (Heps0 : 0 <= eps1) by (unfold eps1; apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact H1S]).
  assert (HQSle : QS <= (1 + eps1) * Qs) by (apply Rabs_le_between in HqD; nra).
  assert (HD : Rabs (- a + Qs) <= theta * Qs + 300 * z).
  { assert (E : - a + Qs = - (a - QS) + (Qs - QS)) by ring. rewrite E.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
    assert (Rabs (Qs - QS) <= eps1 * Qs) by (rewrite Rabs_minus_sym; exact HqD).
    assert (Hm : 71 / 10 * u * QS <= 71 / 10 * u * ((1 + eps1) * Qs)) by (apply Rmult_le_compat_l; [lra | exact HQSle]).
    unfold theta. nra. }
  set (D := Rabs (- a + Qs)) in *.
  assert (HD0 : 0 <= D) by apply Rabs_pos.
  set (E := exp (- a)). set (f := exp (- Qs)). set (g := exp (- a + Qs)).
  assert (HEfg : E = f * g) by (unfold E, f, g; rewrite <- exp_plus; f_equal; ring).
  assert (HgU : g <= exp D) by (unfold g; apply exp_mono; apply Rle_abs).
  assert (HgL : exp (- D) <= g).
  { unfold g. apply exp_mono. destruct (Rabs_le_between (- a + Qs) D) as [H _]. specialize (H (Rle_refl _)). lra. }
  assert (Hf0 : 0 < f) by apply exp_pos. assert (Hg0 : 0 < g) by apply exp_pos. assert (HE0 : 0 < E) by apply exp_pos.
  (* the exp contract *)
  destruct (Hexp (- a)) as [Zc [Ex HZ]]. fold E in HZ.
  set (ex := expI (- a)) in *.
  assert (Hex : Rabs (ex - E) <= ue * E + z).
  { assert (E3 : ex - E = (rndF Zc - Zc) + (Zc - E)) by (rewrite Ex; ring).
    rewrite E3. eapply Rle_trans; [apply Rabs_triang |].
    pose proof (rnd_rel_z Zc) as Hr1.
    assert (HZ1 : Rabs Zc <= (1 + bpow radix2 (-100)) * E).
    { assert (E4 : Zc = E + (Zc - E)) by ring. assert (Rabs Zc <= Rabs E + Rabs (Zc - E)) by (rewrite E4 at 1; apply Rabs_triang).
      rewrite (Rabs_pos_eq E) in H by lra. lra. }
    assert (Hu1 : u * Rabs Zc <= u * ((1 + bpow radix2 (-100)) * E)) by (apply Rmult_le_compat_l; [lra | exact HZ1]).
    unfold ue. nra. }
  assert (Hexa : Rabs ex <= E * (1 + ue) + z) by (apply Rabs_le_between in Hex; apply Rabs_le; lra).
  pose proof (rnd_rel_z (wh * ex)) as Hr2.
  unfold termf. change (expI (- argnc x y sh)) with ex. fold a.
  set (tm := rndF (wh * ex)) in *.
  assert (Hwe : Rabs (wh * ex) <= Rabs wh * (E * (1 + ue) + z)).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | exact Hexa]. }
  assert (Htm1 : Rabs (tm - wh * E) <= Rabs wh * E * rx + 3 * z).
  { assert (E5 : tm - wh * E = (tm - wh * ex) + wh * (ex - E)) by ring.
    rewrite E5. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
    assert (Ha : Rabs (tm - wh * ex) <= u * (Rabs wh * (E * (1 + ue) + z)) + z) by (eapply Rle_trans; [exact Hr2 |]; apply Rplus_le_compat_r; apply Rmult_le_compat_l; [lra | exact Hwe]).
    assert (Hb : Rabs wh * Rabs (ex - E) <= Rabs wh * (ue * E + z)) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact Hex]).
    pose proof (Rabs_pos wh).
    assert (Hwz : Rabs wh * z <= z) by nra.
    unfold rx. nra. }
  (* against the exact term *)
  assert (HwE : Rabs (wh * E - W * f) <= Rabs W * f * ((1 + ew) * exp D - 1)).
  { assert (Eq1 : wh * E - W * f = f * ((wh - W) * g + W * (g - 1))) by (rewrite HEfg; ring).
    rewrite Eq1. rewrite Rabs_mult, (Rabs_pos_eq f) by lra.
    assert (Hg1 : Rabs (g - 1) <= exp D - 1).
    { pose proof (exp_two_sided 0 D (Rle_refl 0) ltac:(lra) HD0) as H2.
      apply Rabs_le. split; lra. }
    assert (Hterm : Rabs ((wh - W) * g + W * (g - 1)) <= ew * Rabs W * exp D + Rabs W * (exp D - 1)).
    { eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult. rewrite (Rabs_pos_eq g) by lra.
      assert (Hm1 : Rabs (wh - W) * g <= (ew * Rabs W) * exp D) by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact HwW | exact HgU]).
      assert (Hm2 : Rabs W * Rabs (g - 1) <= Rabs W * (exp D - 1)) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact Hg1]).
      lra. }
    assert (Hm : f * Rabs ((wh - W) * g + W * (g - 1)) <= f * (ew * Rabs W * exp D + Rabs W * (exp D - 1))) by (apply Rmult_le_compat_l; [lra | exact Hterm]).
    nra. }
  assert (HeD : exp D <= exp (theta * Qs + 300 * z)) by (apply exp_mono; lra).
  assert (HwEE : Rabs wh * E <= Rabs W * f * ((1 + ew) * exp D)).
  { rewrite HEfg.
    assert (Hwabs : Rabs wh <= (1 + ew) * Rabs W).
    { assert (E6 : wh = W + (wh - W)) by ring. assert (Rabs wh <= Rabs W + Rabs (wh - W)) by (rewrite E6 at 1; apply Rabs_triang). lra. }
    assert (Hm : Rabs wh * g <= (1 + ew) * Rabs W * exp D) by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hwabs | exact HgU]).
    nra. }
  assert (Hfin : Rabs (tm - W * f) <= Rabs W * f * ((1 + ew) * (1 + rx) * exp D - 1) + 3 * z).
  { assert (E7 : tm - W * f = (tm - wh * E) + (wh * E - W * f)) by ring.
    rewrite E7. eapply Rle_trans; [apply Rabs_triang |].
    assert (Hrx0 : 0 <= rx) by (unfold rx; nra).
    assert (Hc2 : Rabs wh * E * rx <= Rabs W * f * ((1 + ew) * exp D) * rx) by (apply Rmult_le_compat_r; [exact Hrx0 | exact HwEE]).
    assert (E8 : Rabs W * f * ((1 + ew) * (1 + rx) * exp D - 1)
                 = Rabs W * f * ((1 + ew) * exp D - 1) + Rabs W * f * ((1 + ew) * exp D) * rx) by ring.
    nra. }
  eapply Rle_trans; [exact Hfin |].
  assert (Hwf : 0 <= Rabs W * f) by (apply Rmult_le_pos; [apply Rabs_pos | lra]).
  assert (Hrx1 : 0 <= rx) by (unfold rx; nra).
  assert (Hc3 : (1 + ew) * (1 + rx) * exp D <= (1 + ew) * (1 + rx) * exp (theta * Qs + 300 * z)).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact HeD]. }
  assert (Hc4 : Rabs W * f * ((1 + ew) * (1 + rx) * exp D) <= Rabs W * f * ((1 + ew) * (1 + rx) * exp (theta * Qs + 300 * z)))
    by (apply Rmult_le_compat_l; [exact Hwf | exact Hc3]).
  nra.
Qed.
