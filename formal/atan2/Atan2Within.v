(** Real-analysis facts for atan2's fast and accurate paths: the variation of
    [atan x - x], its Taylor bounds near zero, the series branch's
    approximation of [atan], and the composition of an approximation error
    with an evaluation error (AsinWithin's [fast_compose]). *)
From Coq Require Import Reals ZArith Lra Psatz Ratan.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinWithin Atan2SeriesSmall.
Open Scope R_scope.

(** The mean value theorem for [atan x - x]. *)
Lemma atan_id_diff a b : 0 <= a -> a < b ->
  exists c, a < c < b /\ (atan b - b) - (atan a - a) = - (c * c / (1 + c * c)) * (b - a).
Proof.
  intros Ha Hab.
  set (f := fun x => atan x - x).
  assert (pr : derivable f).
  { intros x. change (derivable_pt (fun x => atan x - x) x).
    apply (derivable_pt_minus atan id x (derivable_pt_atan x) (derivable_pt_id x)). }
  destruct (MVT_cor1 f a b pr Hab) as [c [E Hc]].
  exists c. split; [exact Hc | ].
  assert (D : derive_pt f c (pr c) = / (1 + c ^ 2) - 1).
  { apply derive_pt_eq_0.
    exact (derivable_pt_lim_minus atan id c (/ (1 + c ^ 2)) 1 (derivable_pt_lim_atan c) (derivable_pt_lim_id c)). }
  rewrite D in E. unfold f in E. rewrite E.
  assert (Hc3 : 1 + c * c <> 0) by nra.
  replace (c ^ 2) with (c * c) by ring.
  apply Rmult_eq_compat_r. field. exact Hc3.
Qed.

(** [|(atan b - atan a) - (b - a)| <= b^2 (b - a)] for [0 <= a <= b]. *)
Lemma atan_var a b : 0 <= a -> a <= b -> Rabs ((atan b - atan a) - (b - a)) <= b * b * (b - a).
Proof.
  intros Ha Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
  - destruct (atan_id_diff a b Ha Hlt) as [c [[Hc1 Hc2] E]].
    replace ((atan b - atan a) - (b - a)) with ((atan b - b) - (atan a - a)) by ring. rewrite E.
    assert (Hq : 0 <= c * c / (1 + c * c) <= c * c).
    { split; [apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra] | ].
      apply Rmult_le_reg_r with (1 + c * c); [nra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. nra. }
    rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (c * c / (1 + c * c))) by lra. rewrite (Rabs_pos_eq (b - a)) by lra.
    apply Rle_trans with (c * c * (b - a)).
    + apply Rmult_le_compat_r; [lra | apply Hq].
    + assert (c * c <= b * b) by nra. nra.
  - subst b. replace ((atan a - atan a) - (a - a)) with 0 by ring. rewrite Rabs_R0. nra.
Qed.

(** The shift of [atan]'s argument by [d], [|d| <= z/2]. *)
Lemma atan_shift z d : 0 < z -> Rabs d <= z / 2 -> Rabs (atan (z + d) - atan z - d) <= (z + Rabs d) * (z + Rabs d) * Rabs d.
Proof.
  intros Hz Hd. pose proof (Rabs_pos d) as D0. apply Rabs_le_inv in Hd as [Hd1 Hd2].
  destruct (Rle_dec 0 d) as [Dp | Dn].
  - rewrite (Rabs_pos_eq d) by exact Dp.
    pose proof (atan_var z (z + d) ltac:(lra) ltac:(lra)) as V.
    replace (atan (z + d) - atan z - d) with ((atan (z + d) - atan z) - (z + d - z)) by ring.
    apply Rle_trans with (1 := V). replace (z + d - z) with d by ring. apply Rle_refl.
  - assert (Dn' : d < 0) by lra. rewrite (Rabs_left d) by exact Dn'.
    pose proof (atan_var (z + d) z ltac:(lra) ltac:(lra)) as V.
    replace (atan (z + d) - atan z - d) with (- ((atan z - atan (z + d)) - (z - (z + d)))) by ring.
    rewrite Rabs_Ropp. apply Rle_trans with (1 := V).
    replace (z - (z + d)) with (- d) by ring. assert (z * z <= (z + - d) * (z + - d)) by nra. nra.
Qed.

(** [atan x] against [x] near zero. *)
Lemma atan_le_id x : 0 <= x -> atan x <= x.
Proof.
  intros Hx. destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hlt | Heq].
  - pose proof (atan_var 0 x ltac:(lra) ltac:(lra)) as V. rewrite atan_0 in V.
    apply Rabs_le_inv in V as [V1 V2]. assert (atan x - 0 - (x - 0) <= x * x * (x - 0)) by lra.
    (* atan x - x <= 0 follows from the sign of the derivative *)
    destruct (atan_id_diff 0 x ltac:(lra) Hlt) as [c [Hc E]]. rewrite atan_0 in E.
    assert (Hq : 0 <= c * c / (1 + c * c)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
    nra.
  - subst x. rewrite atan_0. lra.
Qed.

Lemma atan_ge_cube x : 0 <= x -> x - x * x * x <= atan x.
Proof.
  intros Hx. destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hlt | Heq].
  - pose proof (atan_var 0 x ltac:(lra) ltac:(lra)) as V. rewrite atan_0 in V.
    apply Rabs_le_inv in V as [V1 V2]. nra.
  - subst x. rewrite atan_0. lra.
Qed.

(** [atan] positive on the positive reals. *)
Lemma atan_pos x : 0 < x -> 0 < atan x.
Proof. intros H. pose proof (atan_increasing 0 x H) as I. rewrite atan_0 in I. exact I. Qed.

(** The first Taylor terms of [atan], with the alternating series' remainder. *)
Lemma atan_taylor x : 0 < x < 1 -> Rabs (atan x - (x - x * x * x / 3 + x * x * x * x * x / 5)) <= x * x * x * x * x * x * x / 7.
Proof.
  intros [H0 H1].
  assert (Hr : 0 <= x <= 1) by lra.
  rewrite atan_eq_ps_atan by (split; assumption).
  unfold ps_atan. destruct (Ratan.in_int x) as [h | h]; [ | exfalso; apply h; lra].
  destruct (ps_atan_exists_1 x h) as [l Hl].
  pose proof (alternated_series_ineq (Ratan_seq x) l 2 (Ratan_seq_decreasing x Hr) (Ratan_seq_converging x Hr) Hl) as [A B].
  unfold tg_alt, Ratan_seq in A, B. simpl in A, B.
  assert (Hxx : 0 < x * x < 1) by nra.
  assert (P7 : 0 <= x * x * x * x * x * x * x) by (repeat apply Rmult_le_pos; lra).
  assert (P9 : x * x * x * x * x * x * x * x * x <= x * x * x * x * x * x * x) by nra.
  assert (P11 : x * x * x * x * x * x * x * x * x * x * x <= x * x * x * x * x * x * x * x * x) by nra.
  assert (P9p : 0 <= x * x * x * x * x * x * x * x * x) by (repeat apply Rmult_le_pos; lra).
  apply Rabs_le. split; nra.
Qed.

(** The series branch's polynomial against [atan]: relative to the cubic term, on
    [[2^-17, 0.0078126]] by interval arithmetic. *)
Lemma approx_series_mid z : / 131072 <= z <= 0.0078126 ->
  Rabs (atan z - (z - z * z * z * aQ (z * z))) <= 17 / 50 / 18014398509481984 * (z * z * z).
Proof.
  intros H. unfold aQ, aq0, aq1, aq2, aq3. bpow_num. apply Rabs_le. split.
  - assert (G : 0 <= 17 / 50 / 18014398509481984 * (z * z * z) + (atan z - (z - z * z * z * (/ 18014398509481984 * 6004799503160661 - z * z * (/ 36028797018963968 * 7205759403705275 - z * z * (/ 36028797018963968 * 5146968125827051 - z * z * (/ 72057594037927936 * 7952018364870011))))))).
    { interval with (i_bisect z, i_taylor z, i_prec 240, i_degree 14, i_depth 60). }
    lra.
  - assert (G : 0 <= 17 / 50 / 18014398509481984 * (z * z * z) - (atan z - (z - z * z * z * (/ 18014398509481984 * 6004799503160661 - z * z * (/ 36028797018963968 * 7205759403705275 - z * z * (/ 36028797018963968 * 5146968125827051 - z * z * (/ 72057594037927936 * 7952018364870011))))))).
    { interval with (i_bisect z, i_taylor z, i_prec 240, i_degree 14, i_depth 60). }
    lra.
Qed.

(** The same below [2^-17], from [atan]'s Taylor series and the polynomial's
    leading coefficients: [q0 = (2^54 - 1)/(3 2^54)] and [q1] within [2^-54] of [1/5]. *)
Lemma approx_series_small z : bpow radix2 (-100) <= z <= / 131072 ->
  Rabs (atan z - (z - z * z * z * aQ (z * z))) <= 17 / 50 / 18014398509481984 * (z * z * z).
Proof.
  intros [L U]. pose proof (bpow_gt_0 radix2 (-100)) as P.
  assert (Hz : 0 < z < 1) by (split; lra).
  pose proof (atan_taylor z Hz) as T.
  destruct aq_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]].
  assert (D0e : aq0 = 1 / 3 - 1 / 54043195528445952) by (unfold aq0; bpow_num; lra).
  assert (D1e : 1 / 5 - 1 / 300000000000 <= aq1 <= 1 / 5) by (unfold aq1; bpow_num; split; interval with (i_prec 120)).
  assert (W0 : 0 <= (z * z)) by (nra).
  assert (W1 : (z * z) <= / 17179869184) by (nra).
  assert (WW : (z * z) * (z * z) <= / 295147905179352825856) by (pose proof (Rmult_le_compat (z * z) (/ 17179869184) (z * z) (/ 17179869184) W0 W0 W1 W1); lra).
  assert (Z3 : 0 <= z * z * z) by (apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra).
  assert (Id : atan z - (z - z * z * z * aQ (z * z))
    = (atan z - (z - z * z * z / 3 + z * z * z * z * z / 5))
      + z * z * z * ((aq0 - 1 / 3) - (z * z) * (aq1 - 1 / 5) + (z * z) * (z * z) * (aq2 - (z * z) * aq3))) by (unfold aQ; field).
  rewrite Id.
  assert (HK : Rabs ((aq0 - 1 / 3) - (z * z) * (aq1 - 1 / 5) + (z * z) * (z * z) * (aq2 - (z * z) * aq3)) <= 0.3334 / 18014398509481984).
  { apply Rabs_le. assert (0 <= (z * z) * (1 / 300000000000)) by nra.
    assert ((z * z) * (1 / 300000000000) <= 1 / 295147905179352825856 * 10) by nra.
    assert (Hww : 0 <= (z * z) * (z * z)) by nra.
    assert (Hf0 : 0 <= aq2 - (z * z) * aq3) by nra.
    assert (Hf1 : aq2 - (z * z) * aq3 <= 1) by nra.
    assert (Hp0 : 0 <= (z * z) * (z * z) * (aq2 - (z * z) * aq3)) by (apply Rmult_le_pos; assumption).
    pose proof (Rmult_le_compat_l ((z * z) * (z * z)) _ _ Hww Hf1) as Hp1.
    split; nra. }
  assert (HE : Rabs (atan z - (z - z * z * z / 3 + z * z * z * z * z / 5)) <= z * z * z * ((z * z) * (z * z)) / 7).
  { apply Rle_trans with (1 := T). apply Req_le. field. }
  apply Rle_trans with (Rabs (atan z - (z - z * z * z / 3 + z * z * z * z * z / 5)) + Rabs (z * z * z * ((aq0 - 1 / 3) - (z * z) * (aq1 - 1 / 5) + (z * z) * (z * z) * (aq2 - (z * z) * aq3)))); [apply Rabs_triang | ].
  rewrite Rabs_mult, (Rabs_pos_eq (z * z * z)) by exact Z3.
  assert (z * z * z * Rabs ((aq0 - 1 / 3) - (z * z) * (aq1 - 1 / 5) + (z * z) * (z * z) * (aq2 - (z * z) * aq3)) <= z * z * z * (0.3334 / 18014398509481984)) by (apply Rmult_le_compat_l; [exact Z3 | exact HK]).
  assert (z * z * z * ((z * z) * (z * z)) / 7 <= z * z * z * (0.0001 / 18014398509481984)) by nra.
  nra.
Qed.

Lemma approx_series_a z : bpow radix2 (-100) <= z <= 0.0078126 ->
  Rabs (atan z - (z - z * z * z * aQ (z * z))) <= 17 / 50 / 18014398509481984 * (z * z * z).
Proof.
  intros [L U]. destruct (Rle_dec z (/ 131072)) as [S | B].
  - apply approx_series_small; split; assumption.
  - apply approx_series_mid; split; lra.
Qed.
