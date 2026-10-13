(** Accurate positive-tail setup from the actual finite binary64 input. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import ErfcxReciprocal ErfcxAccurateReciprocal ErfcxAccurateInputs
  ErfcxAccurateNewton ErfcxAccurateSquare ErfcxAccurateLoop.
Open Scope R_scope.

Definition q_recip x :=
  q_refine3 x (q_float (fdiv one (Q256.to_f64 x))).

Theorem q_recip_float_error x : finite x -> 16<=B x ->
  valid (q_recip (q_float x)) /\ exists e,
    Rabs e<=bpow radix2 (-252) /\ qval (q_recip (q_float x))=(/B x)*(1+e).
Proof.
  intros F X. destruct (q_float_ok x F) as [Q Value].
  destruct (q_float_roundtrip x F) as [Fround Round].
  destruct (accurate_reciprocal_seed_ieee (Q256.to_f64 (q_float x)) Fround
    ltac:(rewrite Round; exact X)) as [Fseed Seed].
  destruct (q_float_ok _ Fseed) as [Y Yvalue].
  assert (SeedBound : Rabs (qval (q_float x)*
    qval (q_float (fdiv one (Q256.to_f64 (q_float x))))-1)<=bpow radix2 (-50)).
  { rewrite Value,Yvalue, <- Round. eapply Rle_trans; [exact Seed | apply bpow_le; lia]. }
  destruct (q_refine3_error _ _ Q Y SeedBound) as [Result Error].
  unfold q_recip. split; [exact Result | ].
  rewrite Value in Error. exists (B x*qval (q_refine3 (q_float x)
    (q_float (fdiv one (Q256.to_f64 (q_float x)))))-1).
  split; [exact Error | field; lra].
Qed.

Definition q_tail_series x := q_asym_series (q_half_square (q_recip (q_float x))) q_odd.

Theorem q_tail_series_integral x : finite x -> 16<=B x ->
  valid (q_tail_series x) /\
  Rabs (qval (q_tail_series x)-ErfcxTailIntegral.tail_integral ((/B x)*(/B x)))
    <=bpow radix2 (-226).
Proof.
  intros F X. destruct (q_recip_float_error x F X) as [Y Error].
  destruct (q_half_square_error _ (/B x) Y Error) as [Qt Square].
  assert (Reciprocal : 0</B x<=/16).
  { split; [apply Rinv_0_lt_compat | apply Rinv_le_contravar]; lra. }
  assert (T : 0<=(/B x)*(/B x)<=/2^8).
  { split; [nra | ]. eapply Rle_trans with ((/16)*(/16));
      [apply Rmult_le_compat; lra | right; field]. }
  unfold q_tail_series. apply q_asym_series_integral; try assumption.
  exact q_odd_ok.
Qed.
