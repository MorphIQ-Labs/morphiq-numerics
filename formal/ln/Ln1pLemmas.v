(** Helpers shared by ln_1p's stage proofs (formal/ln/Ln1pStageH.v,
    Ln1pStageB.v): constants by their encodings, dyadic equalities, ranges
    in the form the certificates state them, and exact or relative roundings. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings RoundingCore.
Require Import Ln1pCheck Ln1pTables Ln1pReduction.
Import ListNotations.

Open Scope R_scope.

Definition st_l1 : f64 := b64_of_bits st_l1_bits.
Definition st_l0 : f64 := b64_of_bits st_l0_bits.
(** [2^k] by its encoding. *)
Lemma enc_pow2 k : (-1022 <= k <= 1023)%Z ->
  finite (b64_of_bits ((1023 + k) * 2 ^ 52)) /\ B (b64_of_bits ((1023 + k) * 2 ^ 52)) = bpow radix2 k.
Proof.
  intros H. destruct (normal_bits ((1023 + k) * 2 ^ 52) ltac:(lia)) as [F V]. split; [exact F | rewrite V].
  rewrite Z.mod_mul, Z.div_mul by lia. rewrite Z.add_0_l, IZR_pow2', <- bpow_plus by lia. f_equal. ring.
Qed.

(** [m1·2^e1 = m2·2^e2] from [m1·2^(e1 − e2) = m2]. *)
Lemma dy_eq m1 e1 m2 e2 : (e2 <= e1)%Z -> (m1 * 2 ^ (e1 - e2) = m2)%Z ->
  IZR m1 * bpow radix2 e1 = IZR m2 * bpow radix2 e2.
Proof.
  intros H E. rewrite <- E, mult_IZR, IZR_pow2' by lia. rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

Lemma coef_ok n m e m' e' : dec n = Some (m, e) -> (e <= e')%Z -> (m' * 2 ^ (e' - e) = m)%Z ->
  finite (b64_of_bits n) /\ B (b64_of_bits n) = IZR m' * bpow radix2 e'.
Proof.
  intros D H E. destruct (dec_ok n _ D) as [F V]. split; [exact F | ]. rewrite V. unfold dval. cbn [fst snd].
  symmetry. apply dy_eq; [exact H | exact E].
Qed.

(** * Arithmetic helpers *)

(** [bpow radix2 k] as a rational numeral, for [lra]. *)
Ltac bpow_num :=
  repeat match goal with
  | |- context [bpow radix2 (Zneg ?p)] =>
      let v := eval vm_compute in (Z.pow_pos 2 p) in change (bpow radix2 (Zneg p)) with (/ IZR v)
  | |- context [bpow radix2 (Zpos ?p)] =>
      let v := eval vm_compute in (Z.pow_pos 2 p) in change (bpow radix2 (Zpos p)) with (IZR v)
  end.
Ltac bpow_num_in H :=
  repeat match type of H with
  | context [bpow radix2 (Zneg ?p)] =>
      let v := eval vm_compute in (Z.pow_pos 2 p) in change (bpow radix2 (Zneg p)) with (/ IZR v) in H
  | context [bpow radix2 (Zpos ?p)] =>
      let v := eval vm_compute in (Z.pow_pos 2 p) in change (bpow radix2 (Zpos p)) with (IZR v) in H
  end.

Lemma rng_abs v (m : positive) e : Rabs v <= IZR (Zpos m) * bpow radix2 e ->
  IZR (Zneg m) * bpow radix2 e <= v <= IZR (Zpos m) * bpow radix2 e.
Proof. intros H. apply Rabs_le_inv in H. change (IZR (Zneg m)) with (- IZR (Zpos m)). lra. Qed.

Lemma abs_rng v (m : positive) e : IZR (Zneg m) * bpow radix2 e <= v <= IZR (Zpos m) * bpow radix2 e ->
  Rabs v <= IZR (Zpos m) * bpow radix2 e.
Proof. intros H. change (IZR (Zneg m)) with (- IZR (Zpos m)) in H. apply Rabs_le. lra. Qed.

(** Scaling by [2^k] is exact while the result stays normal. *)
Lemma rnd_scale a k m : fmtF a -> (a = 0 \/ bpow radix2 m <= Rabs a) -> (-1022 - m <= k)%Z ->
  rndF (a * bpow radix2 k) = a * bpow radix2 k.
Proof.
  intros F H Hk. apply exact_round.
  destruct H as [Z | H]; [rewrite Z, Rmult_0_l; apply generic_format_0 | ].
  apply mult_bpow_exact_FLT; [exact F | ].
  assert (M : (m + 1 <= mag radix2 a)%Z) by (apply mag_ge_bpow; replace (m + 1 - 1)%Z with m by ring; exact H).
  unfold emin, prec. lia.
Qed.

(** [ln(2^E) = E·ln 2]. *)
Lemma ln_bpow E : ln (bpow radix2 E) = IZR E * ln 2.
Proof. rewrite bpow_exp, ln_exp. reflexivity. Qed.

Lemma rnd_bound v c : fmtF c -> Rabs v <= c -> Rabs (rndF v) <= c.
Proof. intros F H. apply abs_round_le_generic; [exact _ | exact _ | exact F | exact H]. Qed.

Lemma fmt_pow k : (-1074 <= k)%Z -> fmtF (bpow radix2 k).
Proof. intros H. apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. Qed.

(** The rounding error is at most [2^-53] of the rounded value, above [2^-1022]. *)
Lemma rnd_err_out a : bpow radix2 (-1022) <= Rabs (rndF a) -> Rabs (rndF a - a) <= bpow radix2 (-53) * Rabs (rndF a).
Proof.
  intros H. apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) (rndF a)); [apply error_le_half_ulp_round; exact _ | ].
  pose proof (ulp_FLT_le radix2 emin prec (rndF a) ltac:(apply Rle_trans with (2 := H); apply bpow_le; unfold emin, prec; lia)) as U.
  replace (bpow radix2 (1 - prec)) with (2 * bpow radix2 (-53)) in U
    by (unfold prec; change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
  lra.
Qed.

Lemma ratio_bound a b c : 0 < Rabs b -> Rabs a <= c * Rabs b -> Rabs (a / b) <= c.
Proof.
  intros P H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by (intros Z; rewrite Z, Rabs_R0 in P; lra).
  apply Rmult_le_reg_r with (Rabs b); [exact P | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact H.
Qed.

(** [x·(1 + d)] between [x·(1 − u)] and [x·(1 + u)] for [x >= 0], [|d| <= u]. *)
Lemma rel_lo x d u : 0 <= x -> Rabs d <= u -> x * (1 - u) <= x * (1 + d).
Proof. intros H D. apply Rabs_le_inv in D. apply Rmult_le_compat_l; lra. Qed.
Lemma rel_hi x d u : 0 <= x -> Rabs d <= u -> x * (1 + d) <= x * (1 + u).
Proof. intros H D. apply Rabs_le_inv in D. apply Rmult_le_compat_l; lra. Qed.

