(** The public entry screens, including subnormal inputs and signed zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps Grid Encodings.
From Interval Require Import Tactic.
Require Import Expm1Tables Expm1Series Ln1pLemmas StageGappa Exp2Thresholds ExpFast.
Open Scope R_scope.

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
