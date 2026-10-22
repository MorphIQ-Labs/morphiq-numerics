(** The accurate path's [q_sin_cos] against [sin] and [cos], at the exact [Q256]
    argument: both within [2^-196], relatively, for [0 <= r <= 0.7854]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSeries AsinQSeries AsinFacts.
Import ListNotations.
Open Scope R_scope.

Lemma pow22_small x : 0 <= x <= 0.6171 -> x ^ 22 <= / 2 ^ 15.
Proof.
  intros [H0 H1]. assert (x ^ 22 <= 0.6171 ^ 22) by (apply pow_incr; lra).
  assert (0.6171 ^ 22 <= / 2 ^ 15) by (interval with (i_prec 60)). lra.
Qed.

Lemma pow24_small x : 0 <= x <= 0.6171 -> x ^ 24 <= / 2 ^ 15.
Proof.
  intros [H0 H1]. assert (x ^ 24 <= 0.6171 ^ 24) by (apply pow_incr; lra).
  assert (0.6171 ^ 24 <= / 2 ^ 15) by (interval with (i_prec 60)). lra.
Qed.

Lemma prodf_sin_pos i : 0 < prodf f_sin 1 i.
Proof.
  change 1%nat with (S 0). rewrite prodf_sin. pose proof (INR_fact_pos (2 * 0 + 1)). pose proof (INR_fact_pos (2 * 0 + 2 * i + 1)).
  apply Rdiv_lt_0_compat; assumption.
Qed.

Lemma prodf_cos_pos i : 0 < prodf f_cos 1 i.
Proof.
  change 1%nat with (S 0). rewrite prodf_cos. pose proof (INR_fact_pos (2 * 0)). pose proof (INR_fact_pos (2 * 0 + 2 * i)).
  apply Rdiv_lt_0_compat; assumption.
Qed.

Lemma err_prod hd d2 U0 A0 : Rabs hd <= 5 * U0 -> Rabs d2 <= U0 / 2 -> 0 <= A0 <= 1 -> 0 < U0 <= / 1000000 ->
  Rabs (hd * (1 + d2) + A0 * d2) <= 6 * U0.
Proof.
  intros H1 H2 [A1 A2] [U1 U2].
  apply Rle_trans with (Rabs (hd * (1 + d2)) + Rabs (A0 * d2)); [apply Rabs_triang | ].
  rewrite !Rabs_mult. rewrite (Rabs_pos_eq A0) by lra.
  assert (Hd2 : Rabs (1 + d2) <= 1.0001).
  { apply Rle_trans with (Rabs 1 + Rabs d2); [apply Rabs_triang | ]. rewrite Rabs_R1. lra. }
  pose proof (Rabs_pos hd). pose proof (Rabs_pos d2). pose proof (Rabs_pos (1 + d2)).
  assert (Rabs hd * Rabs (1 + d2) <= 5 * U0 * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact H1 | exact Hd2]).
  assert (A0 * Rabs d2 <= 1 * (U0 / 2)) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact H2]).
  lra.
Qed.

Theorem q_sin_cos_error r : Q256Real.valid r -> 0 <= qval r <= 0.7854 ->
  Q256Real.valid (fst (q_sin_cos r)) /\ Q256Real.valid (snd (q_sin_cos r)) /\
  Rabs (qval (fst (q_sin_cos r)) - sin (qval r)) <= bpow radix2 (-196) * sin (qval r) /\
  Rabs (qval (snd (q_sin_cos r)) - cos (qval r)) <= bpow radix2 (-196) * cos (qval r).
Proof.
  intros Vr Hr. unfold q_sin_cos. cbn [fst snd].
  set (rv := qval r) in *.
  destruct (mul_relative r r Vr Vr) as [Vs [d [Dd Es]]].
  set (s := Q256.mul r r) in *.
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  rewrite B255 in Dd.
  assert (Hsv : qval s = rv * rv * (1 + d)) by exact Es.
  assert (Hrr : 0 <= rv * rv <= 0.6169) by (split; nra).
  assert (Hsr : 0 <= qval s <= 0.62).
  { rewrite Hsv. apply Rabs_le_inv in Dd. split; nra. }
  assert (HsD : Rabs (qval s - rv * rv) <= U * 0.31).
  { rewrite Hsv. replace (rv * rv * (1 + d) - rv * rv) with (rv * rv * d) by ring.
    rewrite Rabs_mult, (Rabs_pos_eq (rv * rv)) by lra.
    apply Rle_trans with (0.6169 * (U / 2)); [ | lra].
    apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Dd]. }
  pose proof (series_error asin_sin_steps (cs_gen f_sin 1 22) s sin_const_ok Vs Hsr) as [Vh Eh].
  pose proof (series_error asin_cos_steps (cs_gen f_cos 1 23) s cos_const_ok Vs Hsr) as [Vh' Eh'].
  pose proof (const_ok_forall _ _ sin_const_ok) as Fsin. pose proof (const_ok_forall _ _ cos_const_ok) as Fcos.
  pose proof (ser_lip _ (qval s) (rv * rv) Fsin Hsr ltac:(lra)) as Lsin.
  pose proof (ser_lip _ (qval s) (rv * rv) Fcos Hsr ltac:(lra)) as Lcos.
  pose proof (ser_range _ (rv * rv) Fsin ltac:(lra)) as Rsin. pose proof (ser_range _ (rv * rv) Fcos ltac:(lra)) as Rcos.
  pose proof (sin_trunc rv ltac:(lra)) as Tsin. pose proof (cos_trunc rv ltac:(lra)) as Tcos.
  pose proof (pow22_small (rv * rv) ltac:(lra)) as P22. pose proof (pow24_small (rv * rv) ltac:(lra)) as P24.
  pose proof prodf_sin_small as Q22. pose proof prodf_cos_small as Q24.
  set (E := bpow radix2 (-200)).
  assert (Hnum : bpow radix2 (-196) = 16 * E /\ 0 < E /\ U <= E / 1000000000000000 /\ / 2 ^ 15 * / 2 ^ 186 <= E / 2 /\ / 2 ^ 15 * / 2 ^ 202 <= E / 100000).
  { unfold E, U. repeat split.
    - replace (-196)%Z with (-200 + 4)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 4) with 16. ring.
    - apply bpow_gt_0.
    - bpow_num. interval with (i_prec 300).
    - bpow_num. interval with (i_prec 300).
    - bpow_num. interval with (i_prec 300). }
  destruct Hnum as [HE16 [HEp [HUE [H15 H17]]]].
  rewrite HE16.
  assert (Hrv : 0 <= rv <= 0.7854) by exact Hr.
  (* sine *)
  destruct (mul_relative r (q_series s asin_sin_steps) Vr Vh) as [Vsn [d2 [D2 E2]]].
  rewrite B255 in D2. change (qval r) with rv in E2.
  set (hv := qval (q_series s asin_sin_steps)) in *.
  set (A := ser (rv * rv) (cs_gen f_sin 1 22)) in *.
  set (Bs := ser (qval s) (cs_gen f_sin 1 22)) in *.
  assert (HhA : Rabs (hv - A) <= 5 * U).
  { apply Rle_trans with (Rabs (hv - Bs) + Rabs (Bs - A)); [ | rewrite B252 in Eh; nra].
    replace (hv - A) with ((hv - Bs) + (Bs - A)) by ring. apply Rabs_triang. }
  assert (Hp22 : 0 <= (rv * rv) ^ 22) by (apply pow_le; nra).
  assert (Hp24 : 0 <= (rv * rv) ^ 24) by (apply pow_le; nra).
  assert (HTs : 0 <= rv * A - sin rv <= rv * (E / 2)).
  { destruct Tsin as [T1 T2]. split; [exact T1 | ].
    apply Rle_trans with (1 := T2). apply Rmult_le_compat_l; [lra | ].
    pose proof (prodf_sin_pos 22) as Pp.
    apply Rle_trans with (/ 2 ^ 15 * / 2 ^ 186); [apply Rmult_le_compat; [exact Hp22 | lra | exact P22 | exact Q22] | exact H15]. }
  assert (HUs : 0 < U <= / 1000000) by (split; [exact Upos | ]; apply Rle_trans with (1 := Usmall); apply Rinv_le_contravar; lra).
  assert (HA01 : 0 <= A <= 1) by (split; lra).
  assert (HX1 : Rabs ((hv - A) * (1 + d2) + A * d2) <= 6 * U) by (apply err_prod; [exact HhA | exact D2 | exact HA01 | exact HUs]).
  assert (Hsn : qval (Q256.mul r (q_series s asin_sin_steps)) - sin rv = rv * ((hv - A) * (1 + d2) + A * d2) + (rv * A - sin rv)).
  { rewrite E2. ring. }
  assert (Hsin_lo : 0.89 * rv <= sin rv).
  { pose proof (sin_taylor_pos rv ltac:(lra)) as [L _]. nra. }
  assert (Hcos_lo : 0.69 <= cos rv).
  { pose proof (cos_taylor rv ltac:(apply Rabs_le; lra)) as [L _]. nra. }
  refine (conj Vsn (conj Vh' (conj _ _))).
  - rewrite Hsn. apply Rle_trans with (Rabs (rv * ((hv - A) * (1 + d2) + A * d2)) + Rabs (rv * A - sin rv)); [apply Rabs_triang | ].
    rewrite Rabs_mult, (Rabs_pos_eq rv) by lra. rewrite (Rabs_pos_eq (rv * A - sin rv)) by lra.
    destruct HTs as [_ HT2].
    assert (rv * Rabs ((hv - A) * (1 + d2) + A * d2) <= rv * (6 * U)) by (apply Rmult_le_compat_l; [lra | exact HX1]).
    assert (rv * (6 * U) <= rv * (E / 2)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (rv * E <= 16 * E * sin rv) by nra.
    nra.
  - (* cosine *)
    set (hc := qval (q_series s asin_cos_steps)) in *.
    set (A' := ser (rv * rv) (cs_gen f_cos 1 23)) in *.
    set (Bc := ser (qval s) (cs_gen f_cos 1 23)) in *.
    assert (HhA' : Rabs (hc - A') <= 5 * U).
    { apply Rle_trans with (Rabs (hc - Bc) + Rabs (Bc - A')); [ | rewrite B252 in Eh'; nra].
      replace (hc - A') with ((hc - Bc) + (Bc - A')) by ring. apply Rabs_triang. }
    destruct Tcos as [T1 T2].
    assert (HT : cos rv - A' <= E / 100000).
    { apply Rle_trans with (1 := T2). pose proof (prodf_cos_pos 24) as Pp.
      apply Rle_trans with (/ 2 ^ 15 * / 2 ^ 202); [apply Rmult_le_compat; [exact Hp24 | lra | exact P24 | exact Q24] | exact H17]. }
    assert (Habs : Rabs (hc - cos rv) <= E).
    { apply Rabs_le_inv in HhA'. apply Rabs_le. split; nra. }
    apply Rle_trans with E; [exact Habs | nra].
Qed.
