(** Correct rounding throughout the tangent identity screen, including
    subnormals and both signs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps.
From Interval Require Import Tactic.
Require Import TrigTanScreenConstants AsinFacts.
Open Scope R_scope.

Lemma trig_tan_loss_monotone x y : 0<=x<=y -> y<=1 ->
 tan x-x<=tan y-y.
Proof.
 intros [X XY] Y. destruct (Req_dec x y) as [Eq|Ne];[subst;lra|].
 assert (D:forall c, x<=c<=y ->
   derivable_pt_lim (fun z=>tan z-z) c (tan c^2)).
 { intros c C.
   assert (Domain:-PI/2<c<PI/2) by (assert (Pi:2<PI) by interval;lra).
   assert (T:derivable_pt_lim tan c (1+tan c^2)).
   { rewrite <-(derive_pt_tan c Domain).
     exact (proj2_sig (derivable_pt_tan c Domain)). }
   replace (tan c^2) with ((1+tan c^2)-1) by ring.
   exact (derivable_pt_lim_minus tan id c _ _ T (derivable_pt_lim_id c)). }
 destruct (MVT_cor2 (fun z=>tan z-z) (fun z=>tan z^2) x y ltac:(lra) D)
   as [c [Value C]].
 assert (Square:0<=tan c^2) by nra.
 assert (Product:0<=tan c^2*(y-x)) by (apply Rmult_le_pos;lra).
 cbn in Value;lra.
Qed.

Lemma trig_tan_tiny_round x : fmtF x -> Rabs x<=bpow radix2 (-27) -> rndF(tan x)=x.
Proof.
 intros F Range. destruct (Req_dec x 0) as [Zero|Nonzero].
 - subst x;rewrite tan_0,round_0 by exact _;reflexivity.
 - apply (round_relative_close x (tan x) F Nonzero).
   assert (Small:Rabs x<=1) by (apply Rle_trans with (1:=Range);clear;interval).
   pose proof (sin_taylor x Small) as Sin.
   pose proof (cos_taylor x Small) as [CosLo CosHi].
   assert (X2:x*x<=bpow radix2 (-54)).
   { apply Rabs_le_inv in Range. interval with (i_prec 100). }
   assert (CosPos:0<cos x) by (assert (bpow radix2 (-54)<1) by interval;nra).
   assert (CN:cos x<>0) by lra.
   assert (Id:tan x-x=((sin x-x)+x*(1-cos x))/cos x).
   { unfold tan;field;exact CN. }
   rewrite Id. unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact CN.
   rewrite (Rabs_pos_eq (cos x)) by lra.
   apply Rmult_lt_reg_r with (cos x);[exact CosPos|].
   rewrite Rmult_assoc,Rinv_l,Rmult_1_r by exact CN.
   pose proof (Rabs_triang (sin x-x) (x*(1-cos x))) as T.
   rewrite Rabs_mult,(Rabs_pos_eq (1-cos x)) in T by lra.
   assert (Budget:x*x/6+(1-cos x)</2^54*cos x).
   { assert (Scale:bpow radix2 (-54)=/2^54) by (change (/18014398509481984=/2^54);field).
     assert (Tiny:0</2^54<1/4) by interval.
     rewrite Scale in X2;nra. }
   pose proof (Rabs_pos_lt x Nonzero);nra.
Qed.

Lemma trig_tan_upper_round x : fmtF x -> bpow radix2 (-27)<x<=B trig_tan_is_x ->
 rndF(tan x)=x.
Proof.
 intros F [Lo Hi]. pose proof trig_tan_is_x_bounds as Endpoint.
 assert (Pos:0<x) by (pose proof (bpow_gt_0 radix2 (-27));lra).
 assert (Mag:(mag radix2 x:Z)=(-26)%Z).
 { apply mag_unique;rewrite Rabs_pos_eq by lra;change (bpow radix2 (-27)<=x<bpow radix2 (-26));lra. }
 assert (Ulp:ulp radix2 (FLT_exp emin prec) x=bpow radix2 (-79)).
 { rewrite ulp_neq_0 by lra. unfold cexp;rewrite Mag;reflexivity. }
 pose proof (gap_below x F Pos) as [_ Gap].
 assert (Power:x<>bpow radix2 (mag radix2 x-1)) by (rewrite Mag;change (x<>bpow radix2 (-27));lra).
 specialize (Gap Power). change (x-pred radix2 (FLT_exp emin prec) x=ulp radix2 (FLT_exp emin prec) x) in Gap.
 rewrite Ulp in Gap.
 assert (EndpointSmall:B trig_tan_is_x<=1).
 { apply Rle_trans with (bpow radix2 (-26));[lra|clear;interval]. }
 apply (round_within x (tan x) (bpow radix2 (-79)) F Pos).
 - change (bpow radix2 (-79)<=ulp radix2 (FLT_exp emin prec) x);rewrite Ulp;lra.
 - change (bpow radix2 (-79)<=x-pred radix2 (FLT_exp emin prec) x);rewrite Gap;lra.
 - pose proof (trig_tan_loss_monotone 0 x ltac:(lra) ltac:(lra)) as Lower;rewrite tan_0 in Lower.
   pose proof (trig_tan_loss_monotone x (B trig_tan_is_x) ltac:(lra) EndpointSmall) as Upper.
   pose proof trig_tan_is_x_error as Error.
   rewrite Rabs_pos_eq by lra.
   assert (Half:bpow radix2 (-79)/2=bpow radix2 (-80)).
   { replace (-80)%Z with ((-79)+(-1))%Z by lia;rewrite bpow_plus;reflexivity. }
   rewrite Half;lra.
Qed.

Theorem trig_tan_screen_round x : fmtF x -> Rabs x<=B trig_tan_is_x -> rndF(tan x)=x.
Proof.
 intros F Bound. destruct (Rle_lt_dec (Rabs x) (bpow radix2 (-27))) as [Tiny|Large].
 - apply trig_tan_tiny_round;assumption.
 - destruct (Rle_lt_dec 0 x) as [Positive|Negative].
   + rewrite Rabs_pos_eq in Bound,Large by exact Positive.
     apply trig_tan_upper_round;[exact F|lra].
   + rewrite Rabs_left in Bound,Large by exact Negative.
     assert (Round:rndF(tan(-x))= -x).
     { apply trig_tan_upper_round;[apply generic_format_opp;exact F|lra]. }
     rewrite tan_neg,round_NE_opp_ne in Round;lra.
Qed.
