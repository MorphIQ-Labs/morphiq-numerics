(** The composed bounds also exclude zero throughout the finite-output domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxGaussianReflection
  ErfcxTailIntegral ErfcxScaledAnalytic ErfcxTableEntry ErfcxTableBound ErfcxTableFast
  ErfcxTableAnalyticEntry ErfcxRounding ErfcxReflectionSquare
  ErfcxPublicModel ErfcxPublicBounds ErfcxPublicEntry.
Open Scope R_scope.
Lemma table_target_floor x : finite x -> -/2<=B x<16 -> bpow radix2 (-10)<=gaussian_erfcx(B x).
Proof.
  intros Fx X. destruct(table_approximation_ieee x Fx X) as [F Approx].
  pose proof(table_evaluation_error x Fx X) as Eval.
  pose proof(table_eval_normalized_ieee x Fx X) as Normal.
  destruct(table_eval64 x) as [h l].
  destruct Eval as [_ [_ Eval]]. destruct Normal as [_ [_ [_ [Norm [Lower Upper]]]]].
  pose proof(table_composed_error (B h+B l)(table_exact x)(gaussian_erfcx(B x)) F Approx Eval) as Error.
  rewrite (Rabs_pos_eq(gaussian_erfcx(B x))) in Error by lra.
  apply Rabs_le_inv in Error.
  destruct(rounding_decomposition (B h+B l)) as [d [a [D [A Round]]]].
  rewrite <- Norm in Round.
  set(f:=gaussian_erfcx(B x)) in *;set(y:=B h+B l) in *.
  assert (Y : 0<y) by (bpow_num_all;nra).
  assert (H : B h<=y*2+bpow radix2 (-1075)) by (bpow_num_all;nra).
  bpow_num_all;nra.
Qed.
Lemma positive_tail_floor x : finite x -> 16<=B x -> bpow radix2 (-1026)<=positive_erfcx(B x).
Proof.
  intros Fx X.
  assert (Upper : B x<=bpow radix2 1024).
  { pose proof(abs_B2R_lt_emax 53 1024 x) as H.
    change (Rabs(B x)<bpow radix2 1024) in H.
    rewrite Rabs_pos_eq in H by lra;lra. }
  assert (Y : bpow radix2 (-1024)<=/B x<=/16).
  { split.
    - replace (bpow radix2 (-1024)) with (/bpow radix2 1024) by (bpow_num;field).
      apply Rinv_le_contravar;[lra|exact Upper].
    - apply Rinv_le_contravar;lra. }
  assert (T : 0<=(/B x)*(/B x)<=/256).
  { pose proof(bpow_gt_0 radix2 (-1024));split;nra. }
  pose proof(tail_integral_correction ((/B x)*(/B x)) (proj1 T)) as J.
  assert (C : /2<=inv_sqrt_pi) by (unfold inv_sqrt_pi;interval with(i_prec 80)).
  assert (Product : /2*bpow radix2 (-1024)<=inv_sqrt_pi*/B x).
  { apply Rmult_le_compat;[lra|apply bpow_ge_0|exact C|apply Y]. }
  unfold positive_erfcx,Rdiv.
  eapply Rle_trans with ((/2*bpow radix2 (-1024))*(/2)).
  - bpow_num;lra.
  - apply Rmult_le_compat;[pose proof(bpow_gt_0 radix2 (-1024));lra|lra|exact Product|lra].
Qed.
Lemma bounded_positive f dmax amax y floor : 0<floor -> floor<=f ->
  dmax<=/2 -> amax<=floor/4 -> erfcx_bounded f dmax amax y -> 0<B y.
Proof.
  intros Positive F Dmax Amax [Fy [d [a [D [A Value]]]]].
  apply Rabs_le_inv in D,A;rewrite Value;nra.
Qed.
Theorem erfcx_entry_positive x : finite x -> B reflection_limit<B x -> 0<B(erfcx_entry64 x).
Proof.
  intros Fx X. destruct(Rlt_dec (B x)(-/2)) as [Negative|Nonnegative].
  - pose proof(gaussian_negative_at_least_one (B x) ltac:(lra)) as Floor.
    eapply bounded_positive with (floor:=1);[lra|exact Floor| | |apply erfcx_entry_negative;[exact Fx|lra]];
      bpow_num;lra.
  - destruct(Rlt_dec (B x)16) as [Table|Tail].
    + pose proof(table_target_floor x Fx ltac:(lra)) as Floor.
      eapply bounded_positive with(floor:=bpow radix2 (-10));[apply bpow_gt_0|exact Floor| | |apply erfcx_entry_table;[exact Fx|lra]];
        bpow_num;lra.
    + pose proof(positive_tail_floor x Fx ltac:(lra)) as Floor.
      eapply bounded_positive with(floor:=bpow radix2 (-1026));[apply bpow_gt_0|exact Floor| | |apply erfcx_entry_tail;[exact Fx|lra]];
        bpow_num;lra.
Qed.
