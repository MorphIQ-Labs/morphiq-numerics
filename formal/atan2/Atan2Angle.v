(** atan2's magnitude for finite nonzero operands, outside the tiny ratios: the rounding
    decision accepts only the correctly rounded value; the accurate path returns the
    correctly rounded value of a [Q256] value within [5.2e-58] of the angle, hence within
    [(1/2 + 2^-137)] ulp of it, and exactly the correctly rounded angle when no midpoint
    lies within [2^-190] (relatively) of it ([Stable190]). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinSeries AsinTables AsinKernel AsinSqrtStep AsinRecip AsinCorrect ErfcxAccurateInputs
  Atan2Tables Atan2Kernel Atan2Within Atan2Approx Atan2Decide Atan2Forms Atan2FastPath Atan2Newton Atan2NewtonReal Atan2Accurate.
Open Scope R_scope.

(** No binary64 midpoint within [2^-190] (relatively) of the true value. *)
Definition Stable190 (z : R) : Prop :=
  forall w, Rabs (w - z) <= bnd190 * Rabs z -> rndF w = rndF z.

Notation ulpF := (ulp radix2 (FLT_exp (-1074) 53)).

Lemma half_ulp_rn z : Rabs (rndF z - z) <= / 2 * ulpF (rndF z).
Proof. exact (error_le_half_ulp_round radix2 (FLT_exp (-1074) 53) ne z). Qed.

Lemma rndF_le_four v : v <= 4 -> rndF v <= 4.
Proof.
  intros H. apply Rle_trans with (rndF 4).
  - apply round_le; [exact _ | exact _ | exact H].
  - rewrite round_generic; [lra | exact _ | ].
    change 4 with (bpow radix2 2). apply fmt_bpow. lia.
Qed.

Lemma bndM_small : bndM * (9007199254740992 + 1) * (1 + 2 * bndM) <= bpow radix2 (-137).
Proof. unfold bndM. bpow_num. interval with (i_prec 200). Qed.

(** The correctly rounded value of a [Q256] value close to [Z] is within [(1/2 + 2^-137)] ulp of [Z]. *)
Lemma accurate_ulp q Z : Q256Real.valid q -> Rabs (qval q - Z) <= bndM * Z -> 0 < Z -> Z <= 4 ->
  finite (Q256.to_f64 q) /\ B (Q256.to_f64 q) = rndF (qval q) /\ 0 <= B (Q256.to_f64 q) /\
  Rabs (B (Q256.to_f64 q) - Z) <= (/ 2 + bpow radix2 (-137)) * ulpF (B (Q256.to_f64 q)) /\
  (Stable190 Z -> B (Q256.to_f64 q) = rndF Z).
Proof.
  intros Vq Err Z0 Z4.
  assert (HM0 : 0 < bndM) by (unfold bndM; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  assert (HM1 : bndM <= / 1000000) by (unfold bndM; bpow_num; interval with (i_prec 100)).
  apply Rabs_le_inv in Err as [E1 E2].
  assert (Hv0 : 0 < qval q) by nra.
  assert (Hv4 : qval q <= 5) by nra.
  assert (Hr : Rabs (rndF (qval q)) < bpow radix2 1024).
  { assert (Hge : 0 <= rndF (qval q)) by (apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | lra]).
    assert (Hle : rndF (qval q) <= 8) by (apply Rle_trans with (rndF 8); [apply round_le; [exact _ | exact _ | lra] | rewrite round_generic; [lra | exact _ | change 8 with (bpow radix2 3); apply fmt_bpow; lia]]).
    rewrite Rabs_pos_eq by exact Hge.
    apply Rle_lt_trans with 8; [exact Hle | ]. change 8 with (bpow radix2 3). apply bpow_lt; lia. }
  destruct (q_to_float_round q Vq Hr) as [Fq Bq].
  refine (conj Fq (conj Bq (conj _ (conj _ _)))).
  - rewrite Bq. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | lra].
  - rewrite Bq. set (v := qval q) in *. set (R := rndF v) in *.
    pose proof (error_le_half_ulp_round radix2 (FLT_exp (-1074) 53) ne v) as Hh. change (round radix2 (FLT_exp (-1074) 53) (Znearest ne) v) with R in Hh.
    pose proof (ulp_FLT_gt radix2 (-1074) 53 R) as Hu.
    assert (HR0 : 0 <= R) by (apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | lra]).
    rewrite (Rabs_pos_eq R) in Hu by exact HR0.
    assert (Hp : bpow radix2 (Z.opp 53) = / 9007199254740992) by (change (Z.opp 53) with (-53)%Z; bpow_num; reflexivity).
    rewrite Hp in Hu.
    set (u := ulpF R) in *.
    pose proof bndM_small as Hs.
    assert (HRu : R < 9007199254740992 * u).
    { pose proof (Rmult_lt_compat_r 9007199254740992 _ _ ltac:(lra) Hu) as Hm. rewrite Rmult_assoc, Rinv_l in Hm by lra. lra. }
    pose proof Hh as Hh'. apply Rabs_le_inv in Hh' as [H1 H2].
    assert (Hvu : v <= (9007199254740992 + 1) * u) by (clear - H1 H2 HRu Hu HR0; lra).
    assert (HZu : Z <= (9007199254740992 + 1) * u * (1 + 2 * bndM)).
    { assert (Hz1 : Z * (1 - bndM) <= v) by nra.
      assert (Hz2 : Z <= v * (1 + 2 * bndM)) by nra.
      nra. }
    assert (Hu0 : 0 < u) by (pose proof (Rabs_pos R); nra).
    assert (HbZ : bndM * Z <= bpow radix2 (-137) * u) by nra.
    apply Rabs_le. split; nra.
  - intros St. rewrite Bq. apply St. rewrite (Rabs_pos_eq Z) by lra. pose proof bndM_le190 as Hle190. apply Rabs_le. split; nra.
Qed.

Lemma atan2_eps_val : finite atan2_eps /\ B atan2_eps = bpow radix2 (-62) * (1 + bpow radix2 (-50)).
Proof. exact eps_val. Qed.

(** The magnitude of the angle once the ratio is not tiny. *)
Definition atan2_main (n d : f64) (f : form) : f64 :=
  let '(y, phi) := atan2_fast n d f in
  match atan2_decide y with
  | Some r => r
  | None => Q256.to_f64 (atan2_accurate_value n d f phi)
  end.

Lemma form_range f Y : 0 < Y -> Y <= PI / 4 -> 0 < form_value f Y /\ form_value f Y <= 4.
Proof.
  intros Y0 Y4. pose proof pi_gt_3 as P3. pose proof pi4_le as P4.
  assert (P5 : PI < 3.1416) by (interval with (i_prec 60)).
  destruct f; cbn [form_value]; split; lra.
Qed.

Theorem atan2_main_ok n d f : finite n -> finite d -> 0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  finite (atan2_main n d f) /\ 0 <= B (atan2_main n d f) /\
  Rabs (B (atan2_main n d f) - form_value f (atan (B n / B d))) <=
    (/ 2 + bpow radix2 (-137)) * ulpF (B (atan2_main n d f)) /\
  (atan2_decide (fst (atan2_fast n d f)) <> None -> B (atan2_main n d f) = rndF (form_value f (atan (B n / B d)))) /\
  (Stable190 (form_value f (atan (B n / B d))) -> B (atan2_main n d f) = rndF (form_value f (atan (B n / B d)))).
Proof.
  intros Fn Fd Hn0 Hnd Hq.
  destruct (atan2_fast_ok n d f Fn Fd Hn0 Hnd Hq) as [yh [yl [ph [pl [Hf [Fyh [Fyl [Fph [Fpl [Dy [Dp [Ly [Uy [Ey [Ep [Hph0 [Hpl Hs]]]]]]]]]]]]]]]]].
  set (t := B n / B d) in *.
  set (Z := form_value f (atan t)).
  assert (Ht0 : 0 < t) by (pose proof (bpow_gt_0 radix2 (-901)); lra).
  assert (Ht1 : t <= 1).
  { unfold t. assert (Hd0 : 0 < B d) by lra. apply Rmult_le_reg_r with (B d); [exact Hd0 | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  pose proof (atan_pos t Ht0) as Y0.
  assert (HY4 : atan t <= PI / 4) by (rewrite <- atan_1; apply atan_le; exact Ht1).
  destruct (form_range f (atan t) Y0 HY4) as [Z0 Z4]. fold Z in Z0, Z4.
  unfold atan2_main. rewrite Hf. cbv iota.
  destruct (atan2_decide (yh, yl)) as [v | ] eqn:Hd.
  - (* decided *)
    destruct atan2_eps_val as [Fe Ve].
    assert (Hpos : 0 < B yh) by (apply Rlt_le_trans with (bpow radix2 (-905)); [apply bpow_gt_0 | exact Ly]).
    assert (Hrng : bpow radix2 (-80) <= bpow radix2 (-62) <= bpow radix2 (-60)) by (split; apply bpow_le; lia).
    assert (Habs : bpow radix2 (-905) <= Rabs (B yh) <= bpow radix2 1000).
    { rewrite Rabs_pos_eq by lra. split; [exact Ly | apply Rle_trans with 4; [exact Uy | ]].
      apply Rle_trans with (bpow radix2 2); [change 4 with (bpow radix2 2); apply Rle_refl | apply bpow_le; lia]. }
    assert (Err : Rabs (Z - (B yh + B yl)) <= bpow radix2 (-62) * Rabs Z).
    { rewrite Rabs_minus_sym, (Rabs_pos_eq Z) by lra. exact Ey. }
    destruct (decide_with_ok_a yh yl atan2_eps Z (bpow radix2 (-62)) v Fyh Fyl Fe Habs Dy Hrng
      ltac:(rewrite Ve; split; [apply Rle_refl | bpow_num; interval with (i_prec 100)]) Err Hd) as [Hv Hr].
    rewrite Hv.
    assert (Hb : Rabs (B yh - Z) <= (/ 2 + bpow radix2 (-137)) * ulpF (B yh)).
    { pose proof (half_ulp_rn Z) as Hh. rewrite Hr in Hh.
      pose proof (ulp_ge_0 radix2 (FLT_exp (-1074) 53) (B yh)) as Hu0. pose proof (bpow_gt_0 radix2 (-137)).
      apply Rle_trans with (1 := Hh). nra. }
    refine (conj Fyh (conj (Rlt_le _ _ Hpos) (conj Hb (conj _ _)))).
    + intros _. symmetry. exact Hr.
    + intros _. symmetry. exact Hr.
  - (* accurate *)
    destruct (atan2_accurate_ok n d f ph pl Fn Fd Fph Fpl Hn0 Hnd Hq Hph0 Hpl Ep) as [Vq Eq].
    fold t in Eq. fold Z in Eq.
    assert (Eq' : Rabs (qval (atan2_accurate_value n d f (ph, pl)) - Z) <= bndM * Z).
    { exact Eq. }
    destruct (accurate_ulp _ Z Vq Eq' Z0 Z4) as [Fq [Bq [Nn [Ub St]]]].
    refine (conj Fq (conj Nn (conj Ub (conj _ St)))).
    intros Hc. exfalso. apply Hc. cbn [fst]. exact Hd.
Qed.
