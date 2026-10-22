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
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinRecip AsinCorrect ErfcxAccurateInputs
  Atan2Tables Atan2Kernel Atan2Within Atan2Decide Atan2Forms Atan2FastPath Atan2Newton Atan2NewtonReal Atan2Accurate.
Open Scope R_scope.

(** No binary64 midpoint within [2^-190] (relatively) of the true value. *)
Definition Stable190 (z : R) : Prop :=
  forall w, Rabs (w - z) <= bnd190 * Rabs z -> rndF w = rndF z.

Notation ulpF := (ulp radix2 (FLT_exp (-1074) 53)).

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
  finite (Q256.to_f64 q) /\ B (Q256.to_f64 q) = rndF (qval q) /\
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
  refine (conj Fq (conj Bq (conj _ _))).
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
