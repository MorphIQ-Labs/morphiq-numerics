(** The public [exp] entry (exp/mod.rs, [exp] and [fallback]), transcribed
    through every comparison, the stages, the fallback's rounding test and both
    accurate paths, and composed from their theorems. The published worst-case
    distances stay explicit hypotheses; no axiom is added. *)
From Coq Require Import ZArith Reals Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Q Require Q128.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingConstant.
From Binary64 Require RoundingTest.
Require Import ExpFast ExpAccurate Expm1GeneralReduction Ln1pLemmas Ln1pReduction.
Require Import Exp2 Exp2Range Exp2Thresholds.
Require ExpReduction ExpStageB ExpSmall.
Open Scope R_scope.

(** exp/mod.rs's [X_OVERFLOW] is [ExpFast.c_x_overflow]; the others follow. *)
Definition c_x_zero : f64 := b64_of_bits 13873137513782915154.      (* 0xc0874910d52d3052 *)
Definition c_x_zero_next : f64 := b64_of_bits 13873137513782915153. (* its successor *)
Definition c_one_low : f64 := b64_of_bits 13587360075776786432.     (* 0xbc90000000000000 *)
Definition c_one_high : f64 := b64_of_bits 4368491638549381120.     (* 0x3ca0000000000000 *)
Definition c_one_last : f64 := b64_of_bits 4368491638549381119.     (* its predecessor *)
Definition c_small : f64 := b64_of_bits 4472074429978902528.        (* 0x3e10000000000000 *)
Definition c_infinity : f64 := b64_of_bits 9218868437227405312.     (* 0x7ff0000000000000 *)

Lemma c_x_zero_finite : finite c_x_zero.
Proof. exact (bits_finite 13873137513782915154 _ _ _ eq_refl). Qed.
Lemma c_x_zero_val : B c_x_zero = (-6554261109157970) / 2 ^ 43.
Proof. exact (bits_val 13873137513782915154 true 6554261109157970 43 eq_refl). Qed.
Lemma c_x_zero_next_val : B c_x_zero_next = (-6554261109157969) / 2 ^ 43.
Proof. exact (bits_val 13873137513782915153 true 6554261109157969 43 eq_refl). Qed.
Lemma c_one_low_finite : finite c_one_low.
Proof. exact (bits_finite 13587360075776786432 _ _ _ eq_refl). Qed.
Lemma c_one_low_val : B c_one_low = (-4503599627370496) / 2 ^ 106.
Proof. exact (bits_val 13587360075776786432 true 4503599627370496 106 eq_refl). Qed.
Lemma c_one_high_finite : finite c_one_high.
Proof. exact (bits_finite 4368491638549381120 _ _ _ eq_refl). Qed.
Lemma c_one_high_val : B c_one_high = 4503599627370496 / 2 ^ 105.
Proof. exact (bits_val 4368491638549381120 false 4503599627370496 105 eq_refl). Qed.
Lemma c_one_last_val : B c_one_last = 9007199254740991 / 2 ^ 106.
Proof. exact (bits_val 4368491638549381119 false 9007199254740991 106 eq_refl). Qed.
Lemma c_small_finite : finite c_small.
Proof. exact (bits_finite 4472074429978902528 _ _ _ eq_refl). Qed.
(** The decimal significands as powers of two, proved rather than converted. *)
Lemma two52 : 4503599627370496 = 2 ^ 52.
Proof. ring. Qed.
Lemma two53_pred : 9007199254740991 = 2 ^ 53 - 1.
Proof. ring. Qed.
Lemma c_small_val : B c_small = / 2 ^ 30.
Proof.
 unfold c_small. rewrite (bits_val 4472074429978902528 false 4503599627370496 82 eq_refl).
 change (IZR (cond_Zopp false 4503599627370496)) with 4503599627370496. rewrite two52.
 change 82%nat with (52 + 30)%nat. rewrite pow_add. field; repeat split; apply pow_nonzero; lra.
Qed.
Lemma c_x_overflow_finite : finite c_x_overflow.
Proof. exact (bits_finite 4649454530587146736 _ _ _ eq_refl). Qed.

(** * The transcription *)

Definition exp_fallback (x : f64) : f64 :=
 if is_nan 53 1024 x then x else
 if fle c_x_overflow x then c_infinity else
 if fle x c_x_zero then ExpFast.c_zero else
 if fle c_one_low x && flt x c_one_high then ExpFast.c_one else
 let '(n, r1, p2, e2, rh, rl) := ExpReduction.reduce x in
 let j := Z.to_nat (Z.modulo (em_index x) 128) in
 let k := Z.div (em_index x) 128 in
 match (if (-1021 <=? k)%Z
        then RoundingTest.decide_scaled (fst (fast_at rh rl j)) (snd (fast_at rh rl j)) c_eps k
        else None) with
 | Some y => y
 | None =>
     if fle c_small (b64_abs x)
     then Q128.to_f64 (accurate_at (acc_r n r1 p2 e2) j k)
     else ExpSmall.small x
 end.

Definition exp_entry (x : f64) : f64 :=
 match ExpStageB.exp_stages x with
 | Some y => y
 | None => exp_fallback x
 end.

(** * The screens *)

Lemma exp_overflows x : B c_x_overflow <= x -> bpow radix2 1024 <= exp x.
Proof.
 intros X.
 assert (P : bpow radix2 1024 = exp (1024 * ln 2)).
 { rewrite bpow_exp. reflexivity. }
 rewrite P. apply exp_monotone. apply Rle_trans with (2 := X).
 rewrite c_x_overflow_val. interval with (i_prec 120).
Qed.

Lemma exp_underflows x : x <= B c_x_zero -> rndF (exp x) = 0.
Proof.
 intros X.
 assert (P : bpow radix2 (-1075) = exp (-1075 * ln 2)).
 { rewrite bpow_exp. reflexivity. }
 assert (Hi : exp x <= bpow radix2 (-1075)).
 { rewrite P. apply exp_monotone. apply Rle_trans with (1 := X).
   rewrite c_x_zero_val. interval with (i_prec 120). }
 apply Rle_antisym.
 - rewrite <- round_underflow_tie. apply round_le; auto with typeclass_instances.
 - apply round_ge_generic; auto with typeclass_instances; [apply generic_format_0 | apply Rlt_le, exp_pos].
Qed.

Lemma above_x_zero x : finite x -> B c_x_zero < B x -> B c_x_zero_next <= B x.
Proof.
 intros Fx X. destruct (Rlt_or_le (-512) (B x)) as [S | S].
 - rewrite c_x_zero_next_val. apply Rlt_le, Rle_lt_trans with (2 := S).
   interval with (i_prec 80).
 - assert (G : on_grid (- Z.of_nat 43) (B x - B c_x_zero)).
   { apply grid_minus.
     - apply (grid_fmt_bound (FLT_exp emin prec) 9); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
       right. rewrite Rabs_left1 by lra. change (bpow radix2 9) with 512. lra.
     - rewrite c_x_zero_val. apply val_grid. lia. }
   pose proof (grid_nonzero _ _ G ltac:(lra)) as Gn. rewrite bpow_m, Rabs_pos_eq in Gn by lra.
   assert (Gap : B c_x_zero_next - B c_x_zero = / 2 ^ 43).
   { rewrite c_x_zero_next_val, c_x_zero_val. field; apply pow_nonzero; lra. }
   lra.
Qed.

(** Above [c_x_zero] the exponential does not round to zero. *)
Lemma exp_rounds_positive x : finite x -> B c_x_zero < B x -> 0 < rndF (exp (B x)).
Proof.
 intros Fx X.
 assert (P : bpow radix2 (-1075) < exp (B x)).
 { rewrite bpow_exp. apply Rlt_le_trans with (exp (B c_x_zero_next)).
   - apply exp_increasing. rewrite c_x_zero_next_val.
     simpl (IZR (-1075)). simpl (IZR radix2). interval with (i_prec 120).
   - apply exp_monotone, above_x_zero; assumption. }
 assert (S0 : succ radix2 (FLT_exp emin prec) 0 = bpow radix2 (-1074)).
 { rewrite succ_0, ulp_FLT_0; try reflexivity. }
 assert (Pred : pred radix2 (FLT_exp emin prec) (bpow radix2 (-1074)) = 0).
 { rewrite <- S0, pred_succ; auto with typeclass_instances. apply generic_format_0. }
 assert (R : bpow radix2 (-1074) <= rndF (exp (B x))).
 { apply round_N_ge_midp; [exact _ | apply fmt_pow; lia | ].
   rewrite Pred, Rplus_0_r.
   replace (bpow radix2 (-1074) / 2) with (bpow radix2 (-1075)).
   - exact P.
   - change 2 with (bpow radix2 1). unfold Rdiv. rewrite <- bpow_opp, <- bpow_plus. reflexivity. }
 apply Rlt_le_trans with (2 := R). apply bpow_gt_0.
Qed.

Lemma below_one_high x : B x < B c_one_high -> B x <= B c_one_last.
Proof.
 intros X.
 assert (H : B c_one_high = bpow radix2 (-53)).
 { rewrite c_one_high_val. change (-53)%Z with (- Z.of_nat 53)%Z. rewrite bpow_m.
   rewrite two52. change 105%nat with (52 + 53)%nat.
   rewrite pow_add. field; repeat split; apply pow_nonzero; lra. }
 assert (L : B c_one_last = pred radix2 (FLT_exp emin prec) (bpow radix2 (-53))).
 { rewrite pred_bpow. change (FLT_exp emin prec (-53)) with (-106)%Z.
   rewrite c_one_last_val. change (-53)%Z with (- Z.of_nat 53)%Z.
   change (-106)%Z with (- Z.of_nat 106)%Z. rewrite !bpow_m.
   rewrite two53_pred. change 106%nat with (53 + 53)%nat.
   rewrite pow_add. field; apply pow_nonzero; lra. }
 rewrite L. apply pred_ge_gt; auto with typeclass_instances.
 - apply B_fmt.
 - apply fmt_pow; lia.
 - rewrite <- H. exact X.
Qed.

Lemma exp_rounds_to_one x : B c_one_low <= B x < B c_one_high -> rndF (exp (B x)) = 1.
Proof.
 intros X. pose proof (below_one_high x (proj2 X)) as Hi.
 assert (Low : 1 - / 2 ^ 54 < exp (B x)).
 { apply Rlt_le_trans with (exp (B c_one_low)).
   - rewrite c_one_low_val. interval with (i_prec 240).
   - apply exp_monotone. exact (proj1 X). }
 assert (High : exp (B x) < 1 + / 2 ^ 53).
 { apply Rle_lt_trans with (exp (B c_one_last)).
   - apply exp_monotone. exact Hi.
   - rewrite c_one_last_val. interval with (i_prec 240). }
 assert (F1 : fmtF 1) by (change 1 with (bpow radix2 0); apply fmt_pow; lia).
 destruct one_neighbors as [P S]. apply Rle_antisym.
 - apply round_N_le_midp; [exact _ | exact F1 | rewrite S; lra].
 - apply round_N_ge_midp; [exact _ | exact F1 | rewrite P; lra].
Qed.

Lemma outside_one x :
 (B x < B c_one_low \/ B c_one_high <= B x) -> / 2 ^ 54 <= Rabs (B x).
Proof.
 intros [Lo | Hi].
 - assert (B c_one_low = - / 2 ^ 54).
   { rewrite c_one_low_val. replace (-4503599627370496) with (- 2 ^ 52) by (rewrite <- two52; ring).
     change 106%nat with (52 + 54)%nat. rewrite pow_add. field; repeat split; apply pow_nonzero; lra. }
   assert (0 < / 2 ^ 54) by (apply Rinv_0_lt_compat, pow_lt; lra).
   rewrite Rabs_left1 by lra. lra.
 - assert (/ 2 ^ 54 <= B c_one_high).
   { rewrite c_one_high_val. interval with (i_prec 120). }
   assert (0 < / 2 ^ 54) by (apply Rinv_0_lt_compat, pow_lt; lra).
   rewrite Rabs_pos_eq by lra. lra.
Qed.

(** * The fallback, and the entry *)

Theorem exp_fallback_ok x : finite x -> B c_x_zero < B x < B c_x_overflow ->
 (/ 2 ^ 30 <= Rabs (B x) -> midpoint_far (exp (B x)) (/ 2 ^ 113)) ->
 (/ 2 ^ 54 <= Rabs (B x) < / 2 ^ 30 -> midpoint_far (exp (B x)) (/ 2 ^ 158)) ->
 finite (exp_fallback x) /\ B (exp_fallback x) = rndF (exp (B x)).
Proof.
 intros Fx [Lo Hi] Far Small. unfold exp_fallback.
 assert (Nan : is_nan 53 1024 x = false) by (destruct x; try reflexivity; discriminate).
 rewrite Nan.
 assert (Over : fle c_x_overflow x = false)
   by (apply fle_false; [exact c_x_overflow_finite | exact Fx | exact Hi]).
 assert (Zero : fle x c_x_zero = false)
   by (apply fle_false; [exact Fx | exact c_x_zero_finite | exact Lo]).
 rewrite Over, Zero.
 destruct (fle c_one_low x && flt x c_one_high) eqn:One.
 { apply andb_true_iff in One as [L H].
   apply (fle_true _ _ c_one_low_finite Fx) in L.
   apply (flt_true _ _ Fx c_one_high_finite) in H.
   split; [exact ExpFast.c_one_finite | rewrite ExpFast.c_one_1; symmetry; apply exp_rounds_to_one; lra]. }
 assert (Away : / 2 ^ 54 <= Rabs (B x)).
 { apply outside_one. apply andb_false_iff in One as [L | H].
   - left. apply (fle_false _ _ c_one_low_finite Fx). exact L.
   - right. apply (flt_false _ _ Fx c_one_high_finite). exact H. }
 assert (Xl : -745.1333 <= B x).
 { apply Rlt_le, Rle_lt_trans with (2 := Lo). rewrite c_x_zero_val. interval with (i_prec 80). }
 assert (Xh : B x <= 709.79).
 { apply Rlt_le, Rlt_le_trans with (1 := Hi). rewrite c_x_overflow_val. interval with (i_prec 80). }
 assert (X99 : bpow radix2 (-99) <= Rabs (B x)).
 { apply Rle_trans with (2 := Away). change (-99)%Z with (- Z.of_nat 99)%Z. rewrite bpow_m.
   apply Rinv_le; [apply pow_lt; lra | apply Rle_pow; [lra | lia]]. }
 pose proof (em_index_ok x Fx (conj Xl Xh)) as Index.
 set (j := Z.to_nat (Z.modulo (em_index x) 128)).
 set (k := Z.div (em_index x) 128).
 assert (Hj : (j < 128)%nat).
 { unfold j. pose proof (Z.mod_pos_bound (em_index x) 128 ltac:(lia)). lia. }
 assert (Split : em_index x = (128 * k + Z.of_nat j)%Z).
 { unfold j, k. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). apply Z.div_mod. lia. }
 pose proof (fun v => exp_fast_ok x v k j Fx Xl Hi X99 Hj) as Fast.
 pose proof (fun v => exp_accurate_ok x k j v Fx Xl Hi Hj) as Accurate.
 unfold ExpReduction.reduce in Fast, Accurate, Index |- *.
 destruct (two_prod64 _ ExpReduction.c_l2) as [p2 e2].
 destruct (two_sum64 _ (fneg p2)) as [s t].
 destruct (two_sum64 s _) as [rh rl].
 cbv beta iota zeta in Fast, Accurate |- *.
 set (n := fsub (fadd (fmul x ExpReduction.c_inv_l) ExpReduction.shifter) ExpReduction.shifter) in *.
 assert (N : B n = IZR (128 * k + Z.of_nat j)) by (rewrite <- Split; exact Index).
 destruct (if (-1021 <=? k)%Z
   then RoundingTest.decide_scaled (fst (fast_at rh rl j)) (snd (fast_at rh rl j)) c_eps k
   else None) as [y | ] eqn:Decided.
 - destruct (-1021 <=? k)%Z eqn:K; [ | discriminate].
   apply Z.leb_le in K. exact (Fast y K N Decided).
 - assert (Abs : B (b64_abs x) = Rabs (B x)) by (apply RoundingTest.B_abs).
   assert (Fabs : finite (b64_abs x))
     by (unfold b64_abs; rewrite is_finite_Babs; exact Fx).
   destruct (fle c_small (b64_abs x)) eqn:Large.
   + apply (fle_true _ _ c_small_finite Fabs) in Large. rewrite c_small_val, Abs in Large.
     pose proof (Accurate _ (Far Large) N eq_refl) as V.
     split; [ | exact V].
     (* a nonzero rounded value cannot come from an infinity or a NaN *)
     pose proof (exp_rounds_positive x Fx Lo) as P. rewrite <- V in P.
     destruct (Q128.to_f64 (accurate_at (acc_r n _ p2 e2) j k)); try reflexivity;
       simpl in P; lra.
   + apply (fle_false _ _ c_small_finite Fabs) in Large. rewrite c_small_val, Abs in Large.
     exact (ExpSmall.exp_small_ok x Fx (conj Away Large) (Small (conj Away Large))).
Qed.

(** Every finite argument: overflow returns [+∞] where [e^x >= 2^1024]; below
    the threshold the result is [RN(e^x)]. *)
Theorem exp_entry_finite x : finite x ->
 (B c_x_zero < B x < B c_x_overflow ->
   (/ 2 ^ 30 <= Rabs (B x) -> midpoint_far (exp (B x)) (/ 2 ^ 113)) /\
   (/ 2 ^ 54 <= Rabs (B x) < / 2 ^ 30 -> midpoint_far (exp (B x)) (/ 2 ^ 158))) ->
 let y := exp_entry x in
 (B c_x_overflow <= B x -> y = c_infinity /\ bpow radix2 1024 <= exp (B x)) /\
 (B x < B c_x_overflow -> finite y /\ B y = rndF (exp (B x))).
Proof.
 intros Fx Far. unfold exp_entry.
 destruct (ExpStageB.exp_stages x) as [y | ] eqn:Stages.
 - assert (Screen : ExpStageB.screen x = true).
   { unfold ExpStageB.exp_stages in Stages. destruct (ExpStageB.screen x); [reflexivity | discriminate]. }
   destruct (ExpStageB.screen_ok x Screen) as [_ Small].
   apply Rabs_lt_inv in Small.
   split.
   + intros Over. rewrite c_x_overflow_val in Over. exfalso.
     assert (704 < 6243314768165360 / 2 ^ 43) by interval with (i_prec 64). lra.
   + intros _. exact (ExpStageB.exp_stages_ok x y Stages).
 - assert (Nan : is_nan 53 1024 x = false) by (destruct x; try reflexivity; discriminate).
   split.
   + intros Over. split; [ | apply exp_overflows; exact Over].
     unfold exp_fallback. rewrite Nan.
     now rewrite (proj2 (fle_true _ _ c_x_overflow_finite Fx) Over).
   + intros Below.
     destruct (Rle_or_lt (B x) (B c_x_zero)) as [Under | Above].
     * unfold exp_fallback. rewrite Nan.
       rewrite (proj2 (fle_false _ _ c_x_overflow_finite Fx) Below).
       rewrite (proj2 (fle_true _ _ Fx c_x_zero_finite) Under).
       split; [exact ExpFast.c_zero_finite | rewrite ExpFast.c_zero_val; symmetry; apply exp_underflows; exact Under].
     * destruct (Far (conj Above Below)) as [Large Tiny].
       exact (exp_fallback_ok x Fx (conj Above Below) Large Tiny).
Qed.

Theorem exp_entry_positive x : finite x -> B c_x_zero < B x < B c_x_overflow ->
 (/ 2 ^ 30 <= Rabs (B x) -> midpoint_far (exp (B x)) (/ 2 ^ 113)) ->
 (/ 2 ^ 54 <= Rabs (B x) < / 2 ^ 30 -> midpoint_far (exp (B x)) (/ 2 ^ 158)) ->
 0 < B (exp_entry x).
Proof.
 intros Fx X Large Small.
 destruct (exp_entry_finite x Fx ltac:(intros _; split; assumption)) as [_ H].
 destruct (H (proj2 X)) as [_ V]. rewrite V. apply exp_rounds_positive; [exact Fx | exact (proj1 X)].
Qed.

Theorem exp_entry_nan x : is_nan 53 1024 x = true -> exp_entry x = x.
Proof.
 intros N. unfold exp_entry.
 assert (S : ExpStageB.exp_stages x = None).
 { unfold ExpStageB.exp_stages. destruct (ExpStageB.screen x) eqn:E; [ | reflexivity].
   destruct (ExpStageB.screen_ok x E) as [F _]. destruct x; discriminate. }
 rewrite S. unfold exp_fallback. now rewrite N.
Qed.

Theorem exp_entry_infinities :
 exp_entry c_infinity = c_infinity /\
 exp_entry (b64_of_bits 18442240474082181120) = ExpFast.c_zero.
Proof. split; vm_compute; reflexivity. Qed.

Theorem exp_entry_signed_zeros :
 exp_entry (b64_of_bits 0) = ExpFast.c_one /\
 exp_entry (b64_of_bits 9223372036854775808) = ExpFast.c_one.
Proof. split; vm_compute; reflexivity. Qed.
