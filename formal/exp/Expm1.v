(** The public entry, with all screens and both fallback paths composed.
    The fallback theorem gives a rounded approximation with its proved
    relative bound; it assumes no worst-case separation for expm1. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require Q128.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Interval Require Import Tactic.
Require Import Exp2 Expm1Tables Expm1Thresholds Expm1SmallFast Expm1SmallAccurate
 Expm1GeneralFast Expm1GeneralAccurate Expm1Stages.
Open Scope R_scope.
Definition expm1_entry x :=
 if is_nan 53 1024 x then x else
 if fle em_overflow x then b64_of_bits 9218868437227405312 else
 if fle x em_minus_one_screen then em_minus_one else
 if flt (b64_abs x) em_tiny then x else
 if flt (b64_abs x) em_small then
   match em_small_fast x with Some y => y | None => Q128.to_f64 (em_small_accurate x) end
 else match expm1_stages x with
 | Some y => y
 | None => match em_general_fast x with Some y => y | None => Q128.to_f64 (em_general_accurate x) end
 end.
Definition em_bounded_result x y := finite y /\ exists z,
 B y = rndF z /\ Rabs (z-(exp (B x)-1)) <= /2^118*Rabs (exp (B x)-1).
Lemma em_exact_result x y : finite y -> B y = rndF (exp (B x)-1) -> em_bounded_result x y.
Proof.
 intros Fy V. split; [exact Fy | ]. exists (exp (B x)-1). split; [exact V | ].
 replace (exp (B x)-1-(exp (B x)-1)) with 0 by ring. rewrite Rabs_R0.
 apply Rmult_le_pos; [left; apply Rinv_0_lt_compat; apply pow_lt; lra | apply Rabs_pos].
Qed.
Theorem expm1_entry_finite x : finite x ->
 (B em_overflow <= B x -> expm1_entry x = b64_of_bits 9218868437227405312 /\ bpow radix2 1024 <= exp (B x)-1) /\
 (B x < B em_overflow -> em_bounded_result x (expm1_entry x)).
Proof.
 intros Fx. unfold expm1_entry.
 assert (Nan : is_nan 53 1024 x = false) by (destruct x; try reflexivity; discriminate).
 assert (Fa : finite (b64_abs x)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fx).
 rewrite Nan. destruct em_screens_values as [Tiny [Small [Minus [Low Over]]]].
 destruct (fle em_overflow x) eqn:O.
 - apply (fle_true _ _ em_overflow_finite Fx) in O.
   split; [intros _; split; [reflexivity | apply em_overflow_screen; exact O] | intros; lra].
 - apply (fle_false _ _ em_overflow_finite Fx) in O.
   split; [intros; lra | intros _].
   destruct (fle x em_minus_one_screen) eqn:M.
   + apply (fle_true _ _ Fx em_minus_one_screen_finite) in M.
     apply em_exact_result; [exact em_minus_one_finite | rewrite Minus; symmetry; apply em_minus_one_round; exact M].
   + apply (fle_false _ _ Fx em_minus_one_screen_finite) in M.
     destruct (flt (b64_abs x) em_tiny) eqn:T.
     * apply (flt_true _ _ Fa em_tiny_finite) in T. rewrite B_abs,Tiny in T.
       apply em_exact_result; [exact Fx | symmetry; apply em_tiny_round; [exact T | apply B_fmt]].
     * apply (flt_false _ _ Fa em_tiny_finite) in T. rewrite B_abs,Tiny in T.
       destruct (flt (b64_abs x) em_small) eqn:S.
       -- apply (flt_true _ _ Fa em_small_finite) in S. rewrite B_abs,Small in S.
          destruct (em_small_fast x) as [y | ] eqn:F.
          ++ destruct (em_small_fast_ok x y Fx ltac:(lra) F) as [Fy Vy]. apply em_exact_result; assumption.
          ++ destruct (em_small_accurate_round x Fx ltac:(lra)) as [Fy Vy].
             destruct (em_small_accurate_bound x Fx ltac:(lra)) as [_ E].
             split; [exact Fy | ]. exists (Q128.qval (em_small_accurate x)). split; [exact Vy | ].
             apply Rle_trans with (1:=E). apply Rmult_le_compat_r; [apply Rabs_pos | interval with (i_prec 160)].
       -- apply (flt_false _ _ Fa em_small_finite) in S. rewrite B_abs,Small in S.
          destruct (expm1_stages x) as [y | ] eqn:St.
          ++ destruct (expm1_stages_ok x y St) as [Fy Vy]. apply em_exact_result; assumption.
          ++ assert (L : -37.43 <= B x) by lra. rewrite Over in O.
             destruct (em_general_fast x) as [y | ] eqn:F.
             ** destruct (em_general_fast_ok x y Fx L O S F) as [Fy Vy]. apply em_exact_result; assumption.
             ** destruct (em_general_accurate_round x Fx L O S) as [Fy Vy].
                destruct (em_general_accurate_bound x Fx L O S) as [_ E].
                split; [exact Fy | ]. exists (Q128.qval (em_general_accurate x)). split; assumption.
Qed.
Theorem expm1_entry_nan x : is_nan 53 1024 x = true -> expm1_entry x = x.
Proof. intros N. unfold expm1_entry. rewrite N. reflexivity. Qed.
Theorem expm1_entry_infinities :
 expm1_entry (b64_of_bits 9218868437227405312) = b64_of_bits 9218868437227405312 /\
 expm1_entry (b64_of_bits 18442240474082181120) = em_minus_one.
Proof. split; reflexivity. Qed.
Theorem expm1_entry_signed_zeros :
 expm1_entry (b64_of_bits 0) = b64_of_bits 0 /\
 expm1_entry (b64_of_bits 9223372036854775808) = b64_of_bits 9223372036854775808.
Proof. split; reflexivity. Qed.
