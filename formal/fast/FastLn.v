(** Bounded ln: round the certified reciprocal stage once, without Ziv. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings RoundingTest.
Require Import Exp2 ExpFast LnReduction Ln1pReduction Ln1pLemmas Ln1pTest LnStageEvaluation LnEntry.
Open Scope R_scope.

Definition fast_ln_regular64 (x : f64) : f64 :=
 let '(e, _, h, _) := LnReduction.reduce x in
 let E := (e + rd_e (bits_of_b64 h))%Z in
 let '(s, lo, _) := ln_parts E h in fadd s lo.

Theorem fast_ln_regular_ok x : finite x -> 0 < B x -> B x <> 1 ->
 finite (fast_ln_regular64 x) /\
 Rabs (B (fast_ln_regular64 x) - ln (B x)) <=
 bpow radix2 (-53) * Rabs (ln (B x)) + bpow radix2 (-65).
Proof.
  intros Fx Px Nx.
  pose proof (LnReduction.reduce_ok x Fx Px) as RD.
  unfold fast_ln_regular64. revert RD.
  generalize (LnReduction.reduce x). intros [[[e i] h] r] RD.
  destruct RD as [Hi [_ [Fh [Iy [_ [Ex Er]]]]]].
  destruct (LnReduction.ln_range i Hi) as [Yl [Yu _]].
  assert (Hr : bpow radix2 (-53) <= B h <= bpow radix2 1020).
  { split; [bpow_num; lra | apply Rle_trans with 2; [lra | change 2 with (bpow radix2 1); apply bpow_le; lia]]. }
  pose proof (Ln1pReduction.reduce_ok h Fh Hr) as R1. cbv zeta in R1.
  destruct R1 as [_ [_ [_ [Y _]]]].
  set (re := rd_e (bits_of_b64 h)) in *.
  set (y := B h * bpow radix2 (- re)) in *.
  assert (Hy : B h = y * bpow radix2 re).
  { unfold y. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. simpl. ring. }
  assert (Re : (-1 <= re <= 1)%Z).
  { split.
    - apply Z.nlt_ge. intros Hre.
      assert (bpow radix2 re <= / 4) by (change (/ 4) with (bpow radix2 (-2)); apply bpow_le; lia).
      pose proof (bpow_gt_0 radix2 re). nra.
    - apply Z.nlt_ge. intros Hre.
      assert (4 <= bpow radix2 re) by (change 4 with (bpow radix2 2); apply bpow_le; lia). nra. }
  set (E := (e + re)%Z).
  assert (HE : (-1100 <= E <= 1100)%Z) by (unfold E; lia).
  assert (XY : B x = bpow radix2 E * y).
  { rewrite Ex, Hy. unfold E. rewrite bpow_plus. ring. }
  assert (Ne : E = 0%Z -> y <> 1).
  { intros E0 Y1. apply Nx. rewrite XY, E0, Y1. change (1 * 1 = 1). ring. }
  assert (Lv : ln (B x) = IZR E * ln 2 + ln y).
  { rewrite XY, ln_mult, ln_bpow; [reflexivity | apply bpow_gt_0 | lra]. }

  pose proof (ln_eval_bounded E h Fh Hr HE Ne) as EV. fold re y in EV.
  rewrite <- Lv in EV. revert EV.
  generalize (ln_parts E h). intros [[s lo] eps] EV.
  destruct EV as [Fs [Flo [Feps [[E0 Eu] [Hs [Hl Main]]]]]].
  specialize (Main (ln (B x))).
  assert (Zero : Rabs (ln (B x) - ln (B x)) <= / 2 ^ 123 * Rabs (ln (B x))).
  { rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | apply Rabs_pos]. }
  specialize (Main Zero).
  assert (Sum : Rabs (B s + B lo) <= bpow radix2 1000).
  { apply Rle_trans with (1 := Rabs_triang _ _).
    assert (bpow radix2 1000 = 2 * bpow radix2 999)
      by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
    assert (1 <= bpow radix2 999)
      by (change 1 with (bpow radix2 0); apply bpow_le; lia).
    lra. }
  destruct (fadd_s s lo Fs Flo Sum) as [Fy Vy].
  split; [exact Fy | rewrite Vy].
  pose proof (rnd_sum_err (B s) (B lo) (B_fmt _) (B_fmt _)) as Round.
  pose proof (Rabs_triang_inv (B s + B lo) (ln (B x))) as Mag.
  pose proof (Rabs_pos (B lo)) as Lo0.
  pose proof (Rabs_pos (ln (B x) - (B s + B lo))) as Err0.
  assert (Total : Rabs (rndF (B s + B lo) - ln (B x)) <=
    Rabs (rndF (B s + B lo) - (B s + B lo)) +
    Rabs (ln (B x) - (B s + B lo))).
  { replace (rndF (B s + B lo) - ln (B x)) with
      ((rndF (B s + B lo) - (B s + B lo)) + ((B s + B lo) - ln (B x))) by ring.
    eapply Rle_trans; [apply Rabs_triang | rewrite (Rabs_minus_sym (B s + B lo) (ln (B x))); lra]. }
  rewrite Rabs_minus_sym in Mag.
  bpow_num_in Main. bpow_num_in Round. bpow_num_in Eu. bpow_num. lra.
Qed.

Definition fast_ln_public64 x :=
 if is_nan 53 1024 x then x else
 if flt x c_zero then lf_nan else
 if lf_eq x c_zero then lf_neg_inf else
 if lf_infinite x then x else
 if lf_eq x c_one then c_zero else fast_ln_regular64 x.

Theorem fast_ln_public_ok x : finite x -> 0 < B x ->
 finite (fast_ln_public64 x) /\
 Rabs (B (fast_ln_public64 x) - ln (B x)) <=
 bpow radix2 (-53) * Rabs (ln (B x)) + bpow radix2 (-65).
Proof.
 intros Fx Px. destruct (lf_finite_screens x Fx) as [Nan Inf].
 assert (Neg : flt x c_zero=false)
   by (apply (proj2 (flt_false _ _ Fx c_zero_finite)); rewrite c_zero_val; lra).
 assert (Zero : lf_eq x c_zero=false)
   by (apply lf_not_eq; try assumption; [exact c_zero_finite | rewrite c_zero_val; lra]).
 unfold fast_ln_public64; rewrite Nan,Neg,Zero,Inf.
 destruct (lf_eq x c_one) eqn:One.
 - pose proof (proj1 (lf_eq_ok x c_one Fx c_one_finite) One) as Value.
   rewrite (proj2 Ln1pReduction.c_one_ok) in Value.
   split; [exact c_zero_finite | rewrite c_zero_val, Value, ln_1, Rminus_diag_eq, Rabs_R0 by reflexivity].
   pose proof (bpow_gt_0 radix2 (-65)). nra.
 - apply fast_ln_regular_ok; try assumption.
   intro X; assert (lf_eq x c_one=true)
     by (apply lf_eq_ok; try assumption; [exact c_one_finite | rewrite (proj2 Ln1pReduction.c_one_ok); exact X]).
   congruence.
Qed.

Theorem fast_ln_specials :
 fast_ln_public64 (b64_of_bits 0)=lf_neg_inf /\
 fast_ln_public64 (b64_of_bits 9223372036854775808)=lf_neg_inf /\
 fast_ln_public64 (b64_of_bits 4607182418800017408)=c_zero /\
 fast_ln_public64 (b64_of_bits 9218868437227405312)=b64_of_bits 9218868437227405312 /\
 fast_ln_public64 (b64_of_bits 18442240474082181120)=lf_nan.
Proof. vm_compute; repeat split; reflexivity. Qed.

Theorem fast_ln_nan x : is_nan 53 1024 x=true -> fast_ln_public64 x=x.
Proof. intros H; unfold fast_ln_public64; rewrite H; reflexivity. Qed.

(** The positive SIMD packet includes one without a scalar lane fallback. *)
Theorem fast_ln_regular_one : fast_ln_regular64 (b64_of_bits 4607182418800017408) = c_zero.
Proof. vm_compute; reflexivity. Qed.
