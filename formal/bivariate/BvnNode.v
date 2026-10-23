(** One quadrature node: the computed term [rndF (w * rndF (exp a))] against
    the exact [W exp(-Q(sin t))] at the exact node angle [t], where [a] is the
    computed exponent argument of BvnArg.v at the rounded sine and cosine of
    the computed angle [th], [|th - t| <= dth]. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Flocq Require Import Core.
From Flocq Require Import Relative.
Require Import BvnRound BvnArg.
Open Scope R_scope.

(** [sin] is 1-Lipschitz. *)
Lemma sin_lip_lt a b : a < b -> Rabs (sin b - sin a) <= Rabs (b - a).
Proof.
  intros H.
  destruct (MVT_cor2 sin cos a b H (fun c _ => derivable_pt_lim_sin c)) as [c [E _]].
  rewrite E, Rabs_mult.
  assert (Hc : Rabs (cos c) <= 1) by (apply Rabs_le; apply COS_bound).
  pose proof (Rabs_pos (b - a)). nra.
Qed.

Lemma sin_lip a b : Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
  destruct (Rtotal_order a b) as [H | [H | H]].
  - pose proof (sin_lip_lt a b H). rewrite Rabs_minus_sym. rewrite (Rabs_minus_sym a b). exact H0.
  - subst. replace (sin b - sin b) with 0 by ring. rewrite Rabs_R0. apply Rabs_pos.
  - exact (sin_lip_lt b a H).
Qed.

(** The exponent at a perturbed [S] against the exponent at [s], relative to
    the latter, for every [p] with [|p| <= r/2]. *)
Lemma Q_diff r p S s : 0 <= r -> Rabs p <= r / 2 -> Rabs S < 1 -> Rabs s < 1 ->
  Rabs (Qf r p S - Qf r p s) <= Rabs (S - s) / (1 - Rabs S) * Qf r p s.
Proof.
  intros Hr Hp HS Hs.
  apply Rabs_le_inv in Hp.
  pose proof (Rabs_pos S) as HSa. pose proof (Rabs_pos s) as Hsa.
  assert (HS1 : -1 < S < 1) by (apply Rabs_lt_between; exact HS).
  assert (Hs1 : -1 < s < 1) by (apply Rabs_lt_between; exact Hs).
  assert (HD1 : 0 < 1 - S * S) by nra.
  assert (HD2 : 0 < 1 - s * s) by nra.
  set (A := r / 2 * (S + s) - p * (1 + S * s)).
  assert (Hdiff : Qf r p S - Qf r p s = (S - s) * A / ((1 - S * S) * (1 - s * s))).
  { unfold Qf, A. field. split; lra. }
  set (a1 := r / 2 - p). set (a2 := r / 2 + p).
  assert (Ha1 : 0 <= a1) by (unfold a1; lra).
  assert (Ha2 : 0 <= a2) by (unfold a2; lra).
  assert (HA : A = a1 * (1 + S) * (1 + s) / 2 - a2 * (1 - S) * (1 - s) / 2).
  { unfold A, a1, a2. field. }
  assert (HN : r / 2 - p * s = a1 * (1 + s) / 2 + a2 * (1 - s) / 2).
  { unfold a1, a2. field. }
  assert (Hs1p : 0 <= 1 + s) by lra.
  assert (Hs1m : 0 <= 1 - s) by lra.
  assert (HSa1 : 0 <= Rabs S - S) by (pose proof (Rle_abs S); lra).
  assert (HSa2 : 0 <= Rabs S + S) by (pose proof (Rle_abs (- S)); rewrite Rabs_Ropp in H; lra).
  assert (T1 : 0 <= a1 * (1 + s) * (Rabs S - S)) by (apply Rmult_le_pos; [apply Rmult_le_pos |]; assumption).
  assert (T2 : 0 <= a2 * (1 - s) * (2 + Rabs S - S)) by (apply Rmult_le_pos; [apply Rmult_le_pos | lra]; assumption).
  assert (T3 : 0 <= a1 * (1 + s) * (2 + Rabs S + S)) by (apply Rmult_le_pos; [apply Rmult_le_pos | lra]; assumption).
  assert (T4 : 0 <= a2 * (1 - s) * (Rabs S + S)) by (apply Rmult_le_pos; [apply Rmult_le_pos |]; assumption).
  assert (HAb : Rabs A <= (1 + Rabs S) * (r / 2 - p * s)).
  { rewrite HN. rewrite HA.
    rewrite Rabs_le_between. split; nra. }
  assert (HQ : Qf r p s = (r / 2 - p * s) / (1 - s * s)) by reflexivity.
  assert (HNN : 0 <= r / 2 - p * s).
  { rewrite HN. assert (0 <= a1 * (1 + s)) by (apply Rmult_le_pos; assumption).
    assert (0 <= a2 * (1 - s)) by (apply Rmult_le_pos; assumption). lra. }
  rewrite Hdiff, HQ.
  assert (HD : 0 < (1 - S * S) * (1 - s * s)) by nra.
  rewrite Rabs_div_pos by exact HD. rewrite Rabs_mult.
  assert (H1S : 0 < 1 - Rabs S) by lra.
  assert (Hden : 1 - S * S = (1 - Rabs S) * (1 + Rabs S)).
  { pose proof (Rabs_sq S). nra. }
  assert (Hstep : Rabs (S - s) * Rabs A / ((1 - S * S) * (1 - s * s))
                  <= Rabs (S - s) * ((1 + Rabs S) * (r / 2 - p * s)) / ((1 - S * S) * (1 - s * s))).
  { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact HD |].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact HAb]. }
  eapply Rle_trans; [exact Hstep |].
  right. rewrite Hden. field. split; [lra | split; [lra | lra]].
Qed.

Lemma Qf_nonneg r p s : 0 <= r -> Rabs p <= r / 2 -> Rabs s < 1 -> 0 <= Qf r p s.
Proof.
  intros Hr Hp Hs. unfold Qf.
  assert (Hs1 : -1 < s < 1) by (apply Rabs_lt_between; exact Hs).
  destruct Hs1 as [Hs1a Hs1b].
  apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat; nra].
  assert (Hps : Rabs (p * s) <= r / 2).
  { rewrite Rabs_mult. pose proof (Rabs_pos p). pose proof (Rabs_pos s). nra. }
  apply Rabs_le_inv in Hps. lra.
Qed.

Lemma exp_two_sided D : 0 <= D -> (1 + u) * exp D + (1 - u) * exp (- D) >= 2.
Proof.
  intros HD. pose proof u_pos as Hu. pose proof u_val as Huv.
  pose proof (exp_ineq1_le D) as H1. pose proof (exp_ineq1_le (- D)) as H2.
  nra.
Qed.

Definition termf (x y sh ch wh : R) : R :=
  rndF (wh * rndF (exp (argf x y sh ch))).

(** The error of one term. [th] is the computed angle, [t] the exact node
    angle, [W] the exact weight and [wh] the stored one. *)
Lemma node_err x y t th W wh dth sg hs_ hc_ zt Eh :
  dom x -> dom y ->
  Rabs (th - t) <= dth -> Rabs (sin t) < 1 ->
  bpow radix2 (-100) <= Rabs (rndF (sin th)) -> Rabs (rndF (sin th)) <= 1 ->
  0 < cos th -> Rabs (sin th) <= sg -> sg < 1 ->
  Rabs (rndF (sin th) - sin th) <= hs_ -> Rabs (rndF (cos th) - cos th) <= hc_ ->
  0 <= hs_ -> 0 <= hc_ -> bpow radix2 (-100) <= rndF (cos th) ->
  zt = hc_ * (2 + hc_) / (1 - sg * sg) -> zt <= / 2 ->
  Eh = hs_ + 2 * (2 * u + u * u) ->
  0 <= W -> 0 <= wh -> wh <= 1 -> Rabs (wh - W) <= u * W ->
  let r := x * x + y * y in
  let p := x * y in
  let ar1 := ar0 zt Eh sg * (1 + u) + u in
  let eps1 := dth / (1 - sg) in
  let theta := eps1 + (1 + eps1) * ar1 in
  Rabs (termf x y (rndF (sin th)) (rndF (cos th)) wh - W * exp (- Qf r p (sin t)))
    <= W * exp (- Qf r p (sin t)) * ((1 + u) ^ 3 * exp (theta * Qf r p (sin t) + z) - 1) + 3 * z.
Proof.
  intros Hx Hy Hdth Hst Hsh1 Hsh2 HC HS Hsg Hshe Hche Hhs Hhc Hch Hzt Hzh HEh HW Hwh Hwh1 HwW r p ar1 eps1 theta.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz0.
  set (S := sin th) in *. set (s := sin t) in *.
  set (sh := rndF S) in *. set (ch := rndF (cos th)) in *.
  set (C := cos th) in *.
  assert (Hr : 0 <= r) by (unfold r; nra).
  assert (Hp : Rabs p <= r / 2).
  { unfold p, r. pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2.
    unfold Rsqr in h1, h2. apply Rabs_le. split; nra. }
  assert (HSC : S * S + C * C = 1).
  { unfold S, C. pose proof (sin2_cos2 th). unfold Rsqr in H. nra. }
  assert (HSg : Rabs S < 1) by lra.
  assert (Hsg0 : 0 <= sg) by (pose proof (Rabs_pos S); lra).
  pose proof (arg_err x y sh S C ch sg hs_ hc_ zt Eh Hx Hy Hsh1 Hsh2 HSC HC HS Hsg Hshe Hche Hhs Hhc Hch Hzt Hzh HEh) as Harg.
  fold r in Harg. fold p in Harg.
  set (a := argf x y sh ch) in *.
  set (QS := Qf r p S) in *. set (Qs := Qf r p s) in *.
  pose proof (Qf_nonneg r p s Hr Hp Hst) as HQs0. fold Qs in HQs0.
  pose proof (Qf_nonneg r p S Hr Hp HSg) as HQS0. fold QS in HQS0.
  (* the angle perturbation *)
  assert (HSs : Rabs (S - s) <= dth).
  { eapply Rle_trans; [apply sin_lip |]. exact Hdth. }
  assert (Hdth0 : 0 <= dth) by (eapply Rle_trans; [apply Rabs_pos | exact Hdth]).
  assert (H1S : 0 < 1 - sg) by lra.
  assert (HqD : Rabs (QS - Qs) <= eps1 * Qs).
  { pose proof (Q_diff r p S s Hr Hp HSg Hst) as H.
    fold QS in H. fold Qs in H.
    assert (Hc : Rabs (S - s) / (1 - Rabs S) <= eps1).
    { unfold eps1. apply Rle_trans with (dth / (1 - Rabs S)).
      - unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact HSs].
      - unfold Rdiv. apply Rmult_le_compat_l; [exact Hdth0 |].
        apply Rinv_le_contravar; lra. }
    eapply Rle_trans; [exact H |]. apply Rmult_le_compat_r; [exact HQs0 | exact Hc]. }
  assert (Heps0 : 0 <= eps1) by (unfold eps1; apply Rmult_le_pos; [exact Hdth0 | apply Rlt_le, Rinv_0_lt_compat; lra]).
  assert (HQSle : QS <= (1 + eps1) * Qs).
  { apply Rabs_le_inv in HqD. nra. }
  assert (Har0 : 0 <= ar1).
  { unfold ar1, ar0.
    assert (Hzt0 : 0 <= zt).
    { rewrite Hzt. apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]. }
    assert (HEh0 : 0 <= Eh) by (rewrite HEh; nra).
    assert (Hq0 : 0 <= (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) / ((1 - zt) * (1 - u))).
    { apply Rmult_le_pos.
      - assert (0 <= (1 + u) * Eh / (1 - sg)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]).
        nra.
      - apply Rlt_le, Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
    nra. }
  (* the exponent against Q(sin t) *)
  assert (HD : Rabs (a + Qs) <= theta * Qs + z).
  { assert (E : a + Qs = (a + QS) + (Qs - QS)) by ring.
    rewrite E. eapply Rle_trans; [apply Rabs_triang |].
    assert (Rabs (Qs - QS) <= eps1 * Qs) by (rewrite Rabs_minus_sym; exact HqD).
    assert (Harg' : Rabs (a + QS) <= ar1 * QS + z) by exact Harg.
    assert (Hm : ar1 * QS <= ar1 * ((1 + eps1) * Qs)) by (apply Rmult_le_compat_l; [exact Har0 | exact HQSle]).
    unfold theta. nra. }
  set (D := Rabs (a + Qs)) in *.
  assert (HD0 : 0 <= D) by apply Rabs_pos.
  (* exp *)
  set (E := exp a). set (f := exp (- Qs)). set (g := exp (a + Qs)).
  assert (HEfg : E = f * g).
  { unfold E, f, g. rewrite <- exp_plus. f_equal. ring. }
  assert (HgU : g <= exp D).
  { unfold g. apply exp_mono. apply Rle_abs. }
  assert (HgL : exp (- D) <= g).
  { unfold g. apply exp_mono. destruct (Rabs_le_inv (a + Qs) D (Rle_refl _)) as [H1 _]. exact H1. }
  assert (Hf0 : 0 < f) by apply exp_pos.
  assert (Hg0 : 0 < g) by apply exp_pos.
  assert (HE0 : 0 < E) by apply exp_pos.
  (* the two roundings *)
  pose proof (rnd_rel_z E) as Hr1. rewrite (Rabs_pos_eq E) in Hr1 by lra.
  set (e1 := rndF E) in *.
  pose proof (rnd_rel_z (wh * e1)) as Hr2.
  unfold termf. fold a. fold E. fold e1.
  set (tm := rndF (wh * e1)) in *.
  assert (He1 : Rabs e1 <= E * (1 + u) + z) by (apply Rabs_le_inv in Hr1; apply Rabs_le; split; nra).
  assert (Hwe1 : Rabs (wh * e1) <= wh * (E * (1 + u) + z)).
  { rewrite Rabs_mult, (Rabs_pos_eq wh) by lra. apply Rmult_le_compat_l; [lra | exact He1]. }
  assert (Htm1 : Rabs (tm - wh * E) <= wh * E * (2 * u + u * u) + 3 * z).
  { assert (E3 : tm - wh * E = (tm - wh * e1) + wh * (e1 - E)) by ring.
    rewrite E3. eapply Rle_trans; [apply Rabs_triang |].
    rewrite Rabs_mult, (Rabs_pos_eq wh) by lra.
    assert (Ha : Rabs (tm - wh * e1) <= u * (wh * (E * (1 + u) + z)) + z).
    { eapply Rle_trans; [exact Hr2 |]. apply Rplus_le_compat_r. apply Rmult_le_compat_l; [lra | exact Hwe1]. }
    assert (Hb : wh * Rabs (e1 - E) <= wh * (u * E + z)) by (apply Rmult_le_compat_l; [lra | exact Hr1]).
    assert (Hwz : wh * z <= z) by nra.
    assert (Huz : u * (wh * z) <= z) by nra.
    nra. }
  (* against the exact term *)
  assert (HW1 : (1 - u) * W <= wh <= (1 + u) * W).
  { apply Rabs_le_inv in HwW. nra. }
  destruct HW1 as [HW1a HW1b].
  assert (HwE : Rabs (wh * E - W * f) <= W * f * ((1 + u) * exp D - 1)).
  { assert (Hgd : exp (- D) * exp D = 1) by (rewrite <- exp_plus; replace (- D + D) with 0 by ring; apply exp_0).
    pose proof (exp_two_sided D HD0) as Hts.
    pose proof (exp_pos D) as HeD. pose proof (exp_pos (- D)) as HeD'.
    assert (Hwg1 : wh * g <= W * ((1 + u) * exp D)) by nra.
    assert (Hwg2 : W * ((1 - u) * exp (- D)) <= wh * g) by nra.
    rewrite HEfg.
    assert (HL1 : f * (wh * g) <= f * (W * ((1 + u) * exp D))) by (apply Rmult_le_compat_l; [lra | exact Hwg1]).
    assert (HL2 : f * (W * ((1 - u) * exp (- D))) <= f * (wh * g)) by (apply Rmult_le_compat_l; [lra | exact Hwg2]).
    assert (HL3 : W * f * 2 <= W * f * ((1 + u) * exp D + (1 - u) * exp (- D)))
      by (apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra]).
    apply Rabs_le. split; nra. }
  assert (HeD : exp D <= exp (theta * Qs + z)) by (apply exp_mono; lra).
  assert (HwE' : wh * E <= W * f * ((1 + u) * exp D)).
  { rewrite HEfg.
    assert (HwgU : wh * g <= (1 + u) * W * exp D)
      by (apply Rmult_le_compat; [lra | lra | exact HW1b | exact HgU]).
    assert (HfwU : f * (wh * g) <= f * ((1 + u) * W * exp D)) by (apply Rmult_le_compat_l; [lra | exact HwgU]).
    nra. }
  assert (Hfin : Rabs (tm - W * f) <= W * f * ((1 + u) ^ 3 * exp D - 1) + 3 * z).
  { assert (E4 : tm - W * f = (tm - wh * E) + (wh * E - W * f)) by ring.
    rewrite E4. eapply Rle_trans; [apply Rabs_triang |].
    assert (Hc2 : wh * E * (2 * u + u * u) <= W * f * ((1 + u) * exp D) * (2 * u + u * u))
      by (apply Rmult_le_compat_r; [nra | exact HwE']).
    assert (E5 : W * f * ((1 + u) ^ 3 * exp D - 1)
                 = W * f * ((1 + u) * exp D - 1) + W * f * ((1 + u) * exp D) * (2 * u + u * u)) by ring.
    nra. }
  eapply Rle_trans; [exact Hfin |].
  assert (Hwf : 0 <= W * f) by (apply Rmult_le_pos; lra).
  assert (Hc3 : (1 + u) ^ 3 * exp D <= (1 + u) ^ 3 * exp (theta * Qs + z))
    by (apply Rmult_le_compat_l; [apply pow_le; lra | exact HeD]).
  nra.
Qed.
