(** Correct rounding throughout the sine identity screen, including
    subnormals and both signs. The upper endpoint is certified separately. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps.
From Interval Require Import Tactic.
Require Import TrigScreenConstants TrigAccurate AsinFacts.
Open Scope R_scope.

Lemma trig_sin_loss_monotone x y : x<=y -> x-sin x<=y-sin y.
Proof.
 intro XY. pose proof (trig_sin_lipschitz y x) as L.
 rewrite (Rabs_pos_eq (y-x)) in L by lra.
 apply Rabs_le_inv in L;lra.
Qed.

Lemma trig_sin_tiny_round x : fmtF x -> Rabs x<=bpow radix2 (-26) -> rndF(sin x)=x.
Proof.
 intros F Range. destruct (Req_dec x 0) as [Zero|Nonzero].
 - subst x;rewrite sin_0,round_0 by exact _;reflexivity.
 - apply (round_relative_close x (sin x) F Nonzero).
   assert (X:Rabs x<=1) by (apply Rle_trans with (1:=Range);clear;interval).
   pose proof (sin_taylor x X) as Error.
   assert (Coefficient:x*x/6</2^54).
   { clear - Range. apply Rabs_le_inv in Range. interval with (i_prec 100). }
   pose proof (Rabs_pos_lt x Nonzero). nra.
Qed.

Lemma trig_sin_upper_round x : fmtF x -> bpow radix2 (-26)<x<=B trig_sin_is_x ->
 rndF(sin x)=x.
Proof.
 intros F [Lo Hi]. pose proof trig_sin_is_x_bounds as Endpoint.
 assert (Pos:0<x) by (pose proof (bpow_gt_0 radix2 (-26));lra).
 assert (Mag:(mag radix2 x:Z)=(-25)%Z).
 { apply mag_unique;rewrite Rabs_pos_eq by lra;change (bpow radix2 (-26)<=x<bpow radix2 (-25));lra. }
 assert (Ulp:ulp radix2 (FLT_exp emin prec) x=bpow radix2 (-78)).
 { rewrite ulp_neq_0 by lra. unfold cexp;rewrite Mag;reflexivity. }
 pose proof (gap_below x F Pos) as [_ Gap].
 assert (Power:x<>bpow radix2 (mag radix2 x-1)) by (rewrite Mag;change (x<>bpow radix2 (-26));lra).
 specialize (Gap Power). change (x-pred radix2 (FLT_exp emin prec) x=ulp radix2 (FLT_exp emin prec) x) in Gap.
 rewrite Ulp in Gap.
 apply (round_within x (sin x) (bpow radix2 (-78)) F Pos).
 - change (bpow radix2 (-78)<=ulp radix2 (FLT_exp emin prec) x);rewrite Ulp;lra.
 - change (bpow radix2 (-78)<=x-pred radix2 (FLT_exp emin prec) x);rewrite Gap;lra.
 - pose proof (trig_sin_loss_monotone 0 x ltac:(lra)) as Lower;rewrite sin_0 in Lower.
   pose proof (trig_sin_loss_monotone x (B trig_sin_is_x) Hi) as Upper.
   pose proof trig_sin_is_x_error as Error.
   rewrite Rabs_left1 by lra.
   assert (Half:bpow radix2 (-78)/2=bpow radix2 (-79)).
   { replace (-79)%Z with ((-78)+(-1))%Z by lia;rewrite bpow_plus;reflexivity. }
   rewrite Half;lra.
Qed.

Theorem trig_sin_screen_round x : fmtF x -> Rabs x<=B trig_sin_is_x -> rndF(sin x)=x.
Proof.
 intros F Bound. destruct (Rle_lt_dec (Rabs x) (bpow radix2 (-26))) as [Tiny|Large].
 - apply trig_sin_tiny_round;assumption.
 - destruct (Rle_lt_dec 0 x) as [Positive|Negative].
   + rewrite Rabs_pos_eq in Bound,Large by exact Positive.
     apply trig_sin_upper_round;[exact F|lra].
   + rewrite Rabs_left in Bound,Large by exact Negative.
     assert (Round:rndF(sin(-x))= -x).
     { apply trig_sin_upper_round;[apply generic_format_opp;exact F|lra]. }
     rewrite sin_neg,round_NE_opp_ne in Round;lra.
Qed.
