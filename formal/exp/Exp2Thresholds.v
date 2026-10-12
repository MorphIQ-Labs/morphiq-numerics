(** The entry thresholds, including the underflow tie and the discrete
    predecessor of the exclusive upper endpoint of the interval rounding to 1. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Grid Encodings RoundingConstant.
Require Import ExpFast Exp2Range Exp2ThresholdConstants Ln1pLemmas Ln1pReduction.
Open Scope R_scope.

Lemma e2_edges : B e2_overflow = 1024 /\ B e2_zero = -1075.
Proof. rewrite e2_overflow_val, e2_zero_val. split; field. Qed.

Lemma exp2_overflow x : 1024 <= x -> bpow radix2 1024 <= exp (x * ln 2).
Proof.
 intros X. rewrite <- exp2_integer. apply exp_monotone.
 assert (0 < ln 2) by interval with (i_prec 64). simpl (IZR 1024). nra.
Qed.

Lemma round_underflow_tie : rndF (bpow radix2 (-1075)) = 0.
Proof.
 set (m := b64_of_bits 1).
 assert (M : finite m /\ B m = bpow radix2 (-1074)).
 { split; [exact (bits_finite 1 false 1 (-1074) eq_refl) | ].
   unfold m. rewrite (bits_val 1 false 1 1074 eq_refl).
   change (-1074)%Z with (- Z.of_nat 1074)%Z. rewrite ExpFast.bpow_m. change (1 / 2 ^ 1074 = / 2 ^ 1074). unfold Rdiv. apply Rmult_1_l. }
 destruct M as [Fm Bm].
 assert (Product : B m * B c_half = bpow radix2 (-1075)).
 { rewrite Bm, c_half_val. replace (4503599627370496 / 2 ^ 53) with (bpow radix2 (-1)) by (bpow_num; field).
   rewrite <- bpow_plus. reflexivity. }
 destruct (fmul_s m c_half Fm c_half_finite) as [Fv Bv].
 { rewrite Product, Rabs_pos_eq by apply bpow_ge_0. apply bpow_le; lia. }
 rewrite Product in Bv. rewrite <- Bv. vm_compute. reflexivity.
Qed.
Lemma exp2_underflow x : x <= -1075 -> rndF (exp (x * ln 2)) = 0.
Proof.
 intros X.
 assert (Hi : exp (x * ln 2) <= bpow radix2 (-1075)).
 { rewrite <- exp2_integer. apply exp_monotone.
   assert (0 < ln 2) by interval with (i_prec 64). simpl (IZR (-1075)). nra. }
 apply Rle_antisym.
 - rewrite <- round_underflow_tie. apply round_le; auto with typeclass_instances.
 - apply round_ge_generic; auto with typeclass_instances; [apply generic_format_0 | apply Rlt_le, exp_pos].
Qed.

Lemma exp2_one_predecessor x : B x < B e2_one_high -> B x <= B e2_one_last.
Proof.
 intros X. destruct (Rlt_or_le (B x) (bpow radix2 (-53))) as [S | S].
 - assert (bpow radix2 (-53) <= B e2_one_last) by (rewrite e2_one_last_val; bpow_num; interval with (i_prec 120)). lra.
 - assert (G : on_grid (-105) (B e2_one_high - B x)).
   { apply grid_minus.
     - rewrite e2_one_high_val. exact (val_grid 6497320848556798 105 105 ltac:(lia)).
     - apply (grid_fmt_bound (FLT_exp emin prec) (-53)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
       right. rewrite Rabs_pos_eq; [exact S | pose proof (bpow_gt_0 radix2 (-53)); lra]. }
   pose proof (grid_nonzero _ _ G ltac:(lra)) as Gn. rewrite Rabs_pos_eq in Gn by lra.
   assert (Gap : B e2_one_high - B e2_one_last = bpow radix2 (-105)).
   { rewrite e2_one_high_val, e2_one_last_val. bpow_num. field. }
   lra.
Qed.

Lemma one_neighbors :
 pred radix2 (FLT_exp emin prec) 1 = 1 - / 2 ^ 53 /\
 succ radix2 (FLT_exp emin prec) 1 = 1 + / 2 ^ 52.
Proof.
 assert (Lo : bpow radix2 (-1021) <= B ExpFast.c_one).
 { rewrite c_one_1. change 1 with (bpow radix2 0). apply bpow_le; lia. }
 destruct (bits_down ExpFast.c_one c_one_finite Lo) as [_ D].
 assert (Range : bpow radix2 (-1022) <= B ExpFast.c_one < bpow radix2 1023).
 { rewrite c_one_1. change 1 with (bpow radix2 0). split; [apply bpow_le | apply bpow_lt]; lia. }
 destruct (bits_up ExpFast.c_one c_one_finite Range) as [_ U].
 rewrite c_one_1 in D, U.
 change (B (b64_of_bits 4607182418800017407) = pred radix2 (FLT_exp (-1074) 53) 1) in D.
 change (B (b64_of_bits 4607182418800017409) = succ radix2 (FLT_exp (-1074) 53) 1) in U.
 rewrite (bits_val 4607182418800017407 false 9007199254740991 53 eq_refl) in D.
 rewrite (bits_val 4607182418800017409 false 4503599627370497 52 eq_refl) in U.
 change (9007199254740991 / 2 ^ 53 = pred radix2 (FLT_exp (-1074) 53) 1) in D.
 change (4503599627370497 / 2 ^ 52 = succ radix2 (FLT_exp (-1074) 53) 1) in U.
 unfold emin, prec. split; [rewrite <- D | rewrite <- U]; field.
Qed.

Lemma exp2_round_one x : B e2_one_low <= B x < B e2_one_high -> rndF (exp (B x * ln 2)) = 1.
Proof.
 intros X. pose proof (exp2_one_predecessor x (proj2 X)) as Hi.
 assert (L : 0 < ln 2) by interval with (i_prec 64).
 assert (Low : 1 - / 2 ^ 54 < exp (B x * ln 2)).
 { apply Rlt_le_trans with (exp (B e2_one_low * ln 2)).
   - rewrite e2_one_low_val. interval with (i_prec 240).
   - apply exp_monotone. nra. }
 assert (High : exp (B x * ln 2) < 1 + / 2 ^ 53).
 { apply Rle_lt_trans with (exp (B e2_one_last * ln 2)).
   - apply exp_monotone. nra.
   - rewrite e2_one_last_val. interval with (i_prec 240). }
 assert (F1 : fmtF 1) by (change 1 with (bpow radix2 0); apply fmt_pow; lia).
 destruct one_neighbors as [P S]. apply Rle_antisym.
 - apply round_N_le_midp; [exact _ | exact F1 | rewrite S; lra].
 - apply round_N_ge_midp; [exact _ | exact F1 | rewrite P; lra].
Qed.

Lemma exp2_outside_one x :
 (B x < B e2_one_low \/ B e2_one_high <= B x) -> bpow radix2 (-55) <= Rabs (B x).
Proof.
 intros [Lo | Hi].
 - assert (B e2_one_low <= - bpow radix2 (-55)) by (rewrite e2_one_low_val; bpow_num; interval with (i_prec 120)).
   rewrite Rabs_left1 by (pose proof (bpow_gt_0 radix2 (-55)); lra). lra.
 - assert (bpow radix2 (-55) <= B e2_one_high) by (rewrite e2_one_high_val; bpow_num; interval with (i_prec 120)).
   rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-55)); lra). lra.
Qed.

Lemma exp2_round_positive x : -1075 < x -> 0 < rndF (exp (x * ln 2)).
Proof.
 intros X.
 assert (P : bpow radix2 (-1075) < exp (x * ln 2)).
 { rewrite <- exp2_integer. apply exp_increasing.
   assert (0 < ln 2) by interval with (i_prec 64). simpl (IZR (-1075)). nra. }
 assert (S0 : succ radix2 (FLT_exp emin prec) 0 = bpow radix2 (-1074)).
 { rewrite succ_0, ulp_FLT_0; try reflexivity. }
 assert (Pred : pred radix2 (FLT_exp emin prec) (bpow radix2 (-1074)) = 0).
 { rewrite <- S0, pred_succ; auto with typeclass_instances. apply generic_format_0. }
 assert (R : bpow radix2 (-1074) <= rndF (exp (x * ln 2))).
 { apply round_N_ge_midp; [exact _ | apply fmt_pow; lia | ].
   rewrite Pred, Rplus_0_r.
   replace (bpow radix2 (-1074) / 2) with (bpow radix2 (-1075)).
   - exact P.
   - change 2 with (bpow radix2 1). unfold Rdiv. rewrite <- bpow_opp, <- bpow_plus. reflexivity. }
 apply Rlt_le_trans with (2 := R). apply bpow_gt_0.
Qed.
