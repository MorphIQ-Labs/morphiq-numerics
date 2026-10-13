(** The public entry screens, including subnormal inputs and signed zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps Grid Encodings.
From Interval Require Import Tactic.
Require Import Expm1Tables Expm1Series Ln1pLemmas StageGappa Exp2Thresholds ExpFast.
Open Scope R_scope.

Lemma relative_gaps u : fmtF u -> 0 < u ->
 u*bpow radix2 (-53) <= ulp radix2 (FLT_exp emin prec) u /\
 u*bpow radix2 (-53) <= u-pred radix2 (FLT_exp emin prec) u.
Proof.
 intros Fu Pu. assert (U0 : u <> 0) by lra.
 pose proof (bpow_mag_gt radix2 u) as M. rewrite Rabs_pos_eq in M by lra.
 assert (Ur : ulp radix2 (FLT_exp emin prec) u = bpow radix2 (Z.max (mag radix2 u-53) (-1074))).
 { rewrite ulp_neq_0 by exact U0. reflexivity. }
 assert (Pow : bpow radix2 (mag radix2 u-53) <= ulp radix2 (FLT_exp emin prec) u).
 { rewrite Ur. apply bpow_le. lia. }
 assert (A : u*bpow radix2 (-53) <= ulp radix2 (FLT_exp emin prec) u).
 { apply Rle_trans with (bpow radix2 (mag radix2 u)*bpow radix2 (-53)).
   - apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
   - rewrite <-bpow_plus. exact Pow. }
 split; [exact A | ]. destruct (Req_dec u (bpow radix2 (mag radix2 u-1))) as [Eq | Ne].
 - destruct (gap_below u Fu Pu) as [L _]. apply Rle_trans with (1:=Rle_refl (u*bpow radix2 (-53))).
   apply Rle_trans with (ulp radix2 (FLT_exp emin prec) u/2); [ | exact L].
   rewrite Eq at 1. rewrite <-bpow_plus.
   assert (P : bpow radix2 (mag radix2 u-1 + -53) = bpow radix2 (mag radix2 u-53)/2).
   { replace (mag radix2 u-1 + -53)%Z with ((mag radix2 u-53)+(-1))%Z by lia.
     rewrite bpow_plus. change (bpow radix2 (-1)) with (/2). reflexivity. }
   rewrite P. lra.
 - destruct (gap_below u Fu Pu) as [_ E]. specialize (E Ne).
   change (u-pred radix2 (FLT_exp emin prec) u = ulp radix2 (FLT_exp emin prec) u) in E.
   rewrite E. exact A.
Qed.
Lemma round_relative_close x y : fmtF x -> x <> 0 -> Rabs (y-x) < Rabs x/2^54 -> rndF y = x.
Proof.
 intros Fx X0 E. destruct (Rlt_dec 0 x) as [Pos | Neg].
 - rewrite (Rabs_pos_eq x) in E by lra. destruct (relative_gaps x Fx Pos) as [A B].
   apply (round_within x y (x*bpow radix2 (-53)) Fx Pos A B).
   apply Rlt_le_trans with (1:=E). bpow_num. right. field.
 - assert (Px : 0 < -x) by lra.
   destruct (relative_gaps (-x) (generic_format_opp _ _ _ Fx) Px) as [A B].
   assert (R : rndF (-y) = -x).
   { apply (round_within (-x) (-y) ((-x)*bpow radix2 (-53)) (generic_format_opp _ _ _ Fx) Px A B).
     replace (-y - -x) with (-(y-x)) by ring. rewrite Rabs_Ropp.
     rewrite (Rabs_left x) in E by lra. apply Rlt_le_trans with (1:=E). bpow_num. right. field. }
   rewrite round_NE_opp_ne in R. lra.
Qed.
Theorem em_tiny_round x : Rabs x < /2^54 -> fmtF x -> rndF (exp x-1) = x.
Proof.
 intros X Fx. destruct (Req_dec x 0) as [-> | X0].
 - rewrite exp_0. replace (1-1) with 0 by ring. apply round_0; auto with typeclass_instances.
 - apply round_relative_close; [exact Fx | exact X0 | ].
   assert (XA : Rabs x <= 0.0312501).
   { apply Rle_trans with (/2^54); [lra | interval with (i_prec 80)]. }
   pose proof (exp_taylor_bound 1 x XA) as E.
   assert (S : esum 1 x = 1+x) by (unfold esum; cbn [sum_f_R0]; factorial_reals; small_numerals; field).
   rewrite S in E. change (INR (fact 2)) with 2 in E.
   replace (exp x-1-x) with (exp x-(1+x)) by ring.
   apply Rle_lt_trans with (1:=E).
   pose proof (Rabs_pos_lt x X0). simpl pow. nra.
Qed.

Theorem em_overflow_screen x : B em_overflow <= x -> bpow radix2 1024 <= exp x-1.
Proof.
 intros X. apply Rle_trans with (exp (B em_overflow)-1).
 - rewrite em_overflow_val. interval with (i_prec 180).
 - pose proof (exp_le (B em_overflow) x X). lra.
Qed.
Theorem em_minus_one_round x : x <= B em_minus_one_screen -> rndF (exp x-1) = -1.
Proof.
 intros X. pose proof (exp_pos x) as P.
 assert (Hi : exp x < /2^54).
 { apply Rle_lt_trans with (exp (B em_minus_one_screen)); [apply exp_le; exact X | ].
   rewrite em_minus_one_screen_val. interval with (i_prec 180). }
 assert (R : rndF (1-exp x) = 1).
 { destruct one_neighbors as [Pred Succ].
   assert (F1 : fmtF 1) by (apply (fmt_pow 0); lia).
   apply Rle_antisym.
   - apply round_N_le_midp; [exact _ | exact F1 | rewrite Succ; lra].
   - apply round_N_ge_midp; [exact _ | exact F1 | rewrite Pred; lra]. }
 replace (exp x-1) with (-(1-exp x)) by ring. rewrite round_NE_opp_ne,R. reflexivity.
Qed.
Lemma em_screens_values :
 B em_tiny = /2^54 /\ B em_small = /32 /\ B em_minus_one = -1 /\
 -37.43 <= B em_minus_one_screen /\ B em_overflow = B c_x_overflow.
Proof.
 rewrite em_tiny_val, em_small_val, em_minus_one_val, em_minus_one_screen_val.
 repeat split; try (apply Rle_antisym; interval with (i_prec 160)); try (interval with (i_prec 80)).
Qed.
