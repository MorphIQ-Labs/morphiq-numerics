(** The public exp2 entry, transcribed through every comparison, stage,
    fallback decision and final conversion. The numerical theorem keeps LM's
    published worst-case distance explicit; it adds no axiom. *)
From Coq Require Import ZArith Reals Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import ExpAccurate Exp2Fallback Exp2ThresholdConstants Exp2Thresholds.
Require Exp2Stages ExpFast.
Open Scope R_scope.

Definition fle a b := match Bcompare 53 1024 a b with Some Lt | Some Eq => true | _ => false end.
Definition flt a b := match Bcompare 53 1024 a b with Some Lt => true | _ => false end.
Lemma fle_true a b : finite a -> finite b -> (fle a b = true <-> B a <= B b).
Proof.
 intros Fa Fb. unfold fle. rewrite Bcompare_correct by assumption.
 destruct (Rcompare (B a) (B b)) eqn:C;
 [apply Rcompare_Eq_inv in C | apply Rcompare_Lt_inv in C | apply Rcompare_Gt_inv in C];
 split; intros; try discriminate; try reflexivity; lra.
Qed.
Lemma fle_false a b : finite a -> finite b -> (fle a b = false <-> B b < B a).
Proof.
 intros Fa Fb. unfold fle. rewrite Bcompare_correct by assumption.
 destruct (Rcompare (B a) (B b)) eqn:C;
 [apply Rcompare_Eq_inv in C | apply Rcompare_Lt_inv in C | apply Rcompare_Gt_inv in C];
 split; intros; try discriminate; try reflexivity; lra.
Qed.
Lemma flt_true a b : finite a -> finite b -> (flt a b = true <-> B a < B b).
Proof.
 intros Fa Fb. unfold flt. rewrite Bcompare_correct by assumption.
 destruct (Rcompare (B a) (B b)) eqn:C;
 [apply Rcompare_Eq_inv in C | apply Rcompare_Lt_inv in C | apply Rcompare_Gt_inv in C];
 split; intros; try discriminate; try reflexivity; lra.
Qed.
Lemma flt_false a b : finite a -> finite b -> (flt a b = false <-> B b <= B a).
Proof.
 intros Fa Fb. unfold flt. rewrite Bcompare_correct by assumption.
 destruct (Rcompare (B a) (B b)) eqn:C;
 [apply Rcompare_Eq_inv in C | apply Rcompare_Lt_inv in C | apply Rcompare_Gt_inv in C];
 split; intros; try discriminate; try reflexivity; lra.
Qed.
Definition exp2_entry x :=
 if is_nan 53 1024 x then x else
 if fle e2_overflow x then b64_of_bits 9218868437227405312 else
 if fle x e2_zero then ExpFast.c_zero else
 if fle e2_one_low x && flt x e2_one_high then ExpFast.c_one else
 match Exp2Stages.exp2_stages x with
 | Some y => y
 | None => exp2_fallback x
 end.

Theorem exp2_entry_finite x : finite x ->
 (-1075 < B x < 1024 -> midpoint_far (exp (B x * ln 2)) (/ 2 ^ 113)) ->
 let y := exp2_entry x in
 (1024 <= B x -> y = b64_of_bits 9218868437227405312 /\ bpow radix2 1024 <= exp (B x * ln 2)) /\
 (B x < 1024 -> finite y /\ B y = rndF (exp (B x * ln 2))).
Proof.
 intros Fx Far. unfold exp2_entry.
 assert (Nan : is_nan 53 1024 x = false) by (destruct x; try reflexivity; discriminate).
 rewrite Nan. destruct e2_edges as [Ov Ze].
 destruct (fle e2_overflow x) eqn:Over.
 - apply (fle_true _ _ e2_overflow_finite Fx) in Over. rewrite Ov in Over.
   split; [intros _; split; [reflexivity | apply exp2_overflow; exact Over] | intros; lra].
 - apply (fle_false _ _ e2_overflow_finite Fx) in Over. rewrite Ov in Over.
   split; [intros; lra | intros _].
   destruct (fle x e2_zero) eqn:Zero.
   + apply (fle_true _ _ Fx e2_zero_finite) in Zero. rewrite Ze in Zero.
     split; [exact ExpFast.c_zero_finite | rewrite ExpFast.c_zero_val; symmetry; apply exp2_underflow; exact Zero].
   + apply (fle_false _ _ Fx e2_zero_finite) in Zero. rewrite Ze in Zero.
     destruct (fle e2_one_low x && flt x e2_one_high) eqn:One.
     * apply andb_true_iff in One as [Lo Hi].
       apply (fle_true _ _ e2_one_low_finite Fx) in Lo.
       apply (flt_true _ _ Fx e2_one_high_finite) in Hi.
       split; [exact ExpFast.c_one_finite | rewrite ExpFast.c_one_1; symmetry; apply exp2_round_one; lra].
     * assert (Away : bpow radix2 (-55) <= Rabs (B x)).
       { apply exp2_outside_one. apply andb_false_iff in One as [Lo | Hi].
         - left. apply (fle_false _ _ e2_one_low_finite Fx). exact Lo.
         - right. apply (flt_false _ _ Fx e2_one_high_finite). exact Hi. }
       destruct (Exp2Stages.exp2_stages x) as [y | ] eqn:Stage.
       -- exact (Exp2Stages.exp2_stages_ok x y Stage).
       -- apply exp2_fallback_ok; [exact Fx | exact Away | lra | apply Far; lra].
Qed.

Theorem exp2_entry_nan x : is_nan 53 1024 x = true -> exp2_entry x = x.
Proof. intros N. unfold exp2_entry. rewrite N. reflexivity. Qed.
Theorem exp2_entry_infinities :
 exp2_entry (b64_of_bits 9218868437227405312) = b64_of_bits 9218868437227405312 /\
 exp2_entry (b64_of_bits 18442240474082181120) = ExpFast.c_zero.
Proof. split; reflexivity. Qed.

Theorem exp2_entry_zero x : finite x -> B x <= -1075 -> exp2_entry x = ExpFast.c_zero.
Proof.
 intros Fx X. unfold exp2_entry.
 assert (Nan : is_nan 53 1024 x = false) by (destruct x; try reflexivity; discriminate).
 rewrite Nan.
 assert (Over : fle e2_overflow x = false).
 { apply fle_false; [exact e2_overflow_finite | exact Fx | rewrite (proj1 e2_edges); lra]. }
 assert (Zero : fle x e2_zero = true).
 { apply fle_true; [exact Fx | exact e2_zero_finite | rewrite (proj2 e2_edges); exact X]. }
 now rewrite Over, Zero.
Qed.
Theorem exp2_entry_positive x : finite x -> -1075 < B x < 1024 ->
 midpoint_far (exp (B x * ln 2)) (/ 2 ^ 113) -> 0 < B (exp2_entry x).
Proof.
 intros Fx X Far. destruct (exp2_entry_finite x Fx ltac:(intros _; exact Far)) as [_ H].
 destruct (H (proj2 X)) as [_ V]. rewrite V. apply exp2_round_positive. lra.
Qed.
Theorem exp2_entry_signed_zeros :
 exp2_entry (b64_of_bits 0) = ExpFast.c_one /\
 exp2_entry (b64_of_bits 9223372036854775808) = ExpFast.c_one.
Proof. split; reflexivity. Qed.
