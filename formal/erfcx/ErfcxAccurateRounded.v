(** Binary64 conversion of the accurate positive tail, including underflow.
    This is an error bound, not a correct-rounding claim. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxConstants ErfcxTailIntegral ErfcxScaledAnalytic
  ErfcxRounding ErfcxAccurateInputs ErfcxAccurateProduct.
Open Scope R_scope.

Lemma positive_tail_range x : 16<=x -> 0<positive_erfcx x<=/16.
Proof.
  intros X. assert (Y : 0</x<=/16).
  { split; [apply Rinv_0_lt_compat | apply Rinv_le_contravar]; lra. }
  assert (T : 0<=(/x)*(/x)<=/2^8).
  { split; [nra | ]. eapply Rle_trans with ((/16)*(/16));
      [apply Rmult_le_compat; lra | right; field]. }
  pose proof (tail_integral_correction _ (proj1 T)) as J.
  assert (C : 0<inv_sqrt_pi<=1) by (unfold inv_sqrt_pi; interval with (i_prec 64)).
  assert (Jrange : 0<tail_integral ((/x)*(/x))<=1) by (cbn [pow] in T; lra).
  unfold positive_erfcx,Rdiv. split.
  - repeat apply Rmult_lt_0_compat; lra.
  - eapply Rle_trans with (1*(/16)*1); [ | lra].
    apply Rmult_le_compat; nra.
Qed.

Lemma rounded_product_error e d : Rabs e<=bpow radix2 (-224) ->
  -bpow radix2 (-53)<=d<=bpow radix2 (-53) ->
  Rabs ((1+e)*(1+d)-1)<=bpow radix2 (-53)+bpow radix2 (-223).
Proof.
  intros E D. apply Rabs_le_inv in E.
  replace ((1+e)*(1+d)-1) with (e+d+e*d) by ring.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Theorem q_asym_rounded x : finite x -> 16<=B x ->
  finite (Q256.to_f64 (q_asym x)) /\ exists d a,
    Rabs d<=bpow radix2 (-53)+bpow radix2 (-223) /\
    Rabs a<=bpow radix2 (-1075) /\
    B (Q256.to_f64 (q_asym x))=positive_erfcx (B x)*(1+d)+a.
Proof.
  intros F X. destruct (q_asym_error x F X) as [Q [e [E Value]]].
  pose proof (positive_tail_range _ X) as Range.
  destruct (rounding_decomposition (qval (q_asym x))) as [d [a [D [A Round]]]].
  assert (Qrange : 0<=qval (q_asym x)<=/8).
  { rewrite Value. apply Rabs_le_inv in E.
    assert (Factor : 0<=1+e<=2) by (bpow_num_all; lra). nra. }
  assert (RoundedRange : Rabs (rndF (qval (q_asym x)))<=1).
  { rewrite Round. apply Rabs_le. bpow_num_all. split; nra. }
  assert (FiniteBound : Rabs (rndF (qval (q_asym x)))<bpow radix2 1024).
  { eapply Rle_lt_trans; [exact RoundedRange | ].
    change 1 with (bpow radix2 0). apply bpow_lt; lia. }
  destruct (q_to_float_round _ Q FiniteBound) as [Result Rounded].
  split; [exact Result | ]. exists ((1+e)*(1+d)-1),a. split.
  - apply rounded_product_error; assumption.
  - split; [apply Rabs_le; exact A | ]. rewrite Rounded,Round,Value. ring.
Qed.
