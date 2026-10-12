(** The complete fallback, including its Q128-to-binary64 conversion. Correct
    rounding on the accurate branch retains the published LM midpoint-distance
    hypothesis explicitly, as the exponential kernel's theorem does. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Q Require Q128 QRound QSpec.
From Binary64 Require Import Binary64Add IEEE64.
Require Import ExpAccurate Exp2FallbackAccurate Exp2FallbackFast Exp2Range.
Open Scope R_scope.

Lemma q128_round_finite q : QSpec.normalized 128 (Q128.m q) ->
 Rabs (rndF (Q128.qval q)) < bpow radix2 1024 -> finite (Q128.to_f64 q).
Proof.
 intros N Ov. rewrite Q128.to_f64_ok by exact N. unfold QRound.bn.
 pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE
   (QRound.signed (Q128.neg q) (Q128.m q)) (Q128.e q) (Q128.neg q)) as C.
 rewrite Rlt_bool_true in C by exact Ov. exact (proj1 (proj2 C)).
Qed.

Theorem exp2_accurate_round_ok x : finite x ->
 bpow radix2 (-55) <= Rabs (B x) -> -1075 < B x < 1024 ->
 midpoint_far (exp (B x * ln 2)) (/ 2 ^ 113) ->
 finite (Q128.to_f64 (exp2_fallback_accurate x)) /\
 B (Q128.to_f64 (exp2_fallback_accurate x)) = rndF (exp (B x * ln 2)).
Proof.
 intros Fx Xlo X Far.
 destruct (exp2_fallback_accurate_bound x Fx Xlo ltac:(apply Rabs_le; lra)) as [N E].
 assert (Weak : Rabs (Q128.qval (exp2_fallback_accurate x) - exp (B x * ln 2)) <= / 2 ^ 120 * exp (B x * ln 2)).
 { apply Rle_trans with (1 := E). apply Rmult_le_compat_r;
   [apply Rlt_le, exp_pos | interval with (i_prec 160)]. }
 pose proof (same_rounding _ _ (exp_pos _) Far Weak) as Rnd.
 assert (Ov : Rabs (rndF (Q128.qval (exp2_fallback_accurate x))) < bpow radix2 1024).
 { rewrite Rnd. apply exp2_round_finite; [exact Fx | lra]. }
 split; [apply q128_round_finite; assumption | rewrite to_f64_val by assumption; exact Rnd].
Qed.

Definition exp2_fallback x :=
 match exp2_fallback_fast x with
 | Some y => y
 | None => Q128.to_f64 (exp2_fallback_accurate x)
 end.
Theorem exp2_fallback_ok x : finite x ->
 bpow radix2 (-55) <= Rabs (B x) -> -1075 < B x < 1024 ->
 midpoint_far (exp (B x * ln 2)) (/ 2 ^ 113) ->
 finite (exp2_fallback x) /\ B (exp2_fallback x) = rndF (exp (B x * ln 2)).
Proof.
 intros Fx Xlo X Far. unfold exp2_fallback.
 destruct (exp2_fallback_fast x) as [y | ] eqn:F.
 - exact (exp2_fallback_fast_ok x y Fx Xlo X F).
 - exact (exp2_accurate_round_ok x Fx Xlo X Far).
Qed.
