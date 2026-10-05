(** The Rust operations are IEEE 754 binary64 operations with round to
    nearest, ties to even: Flocq's [b64_plus], [b64_minus], [b64_mult] and
    [b64_div] at [mode_NE], which have overflow, infinities and NaNs. Each
    returns the binary64-model rounding ([rndF]) and a finite value whenever
    that rounding is below [2^1024] in magnitude. The lemmas here carry a
    magnitude bound [k * 2^e] through each operation, so a computation whose
    every bound stays below [2^1024] never overflows and equals its
    binary64-model counterpart. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add.

Open Scope R_scope.

Notation f64 := binary64.
Notation B := (B2R 53 1024).
Notation finite x := (is_finite 53 1024 x = true).

Definition fadd (x y : f64) : f64 := b64_plus mode_NE x y.
Definition fsub (x y : f64) : f64 := b64_minus mode_NE x y.
Definition fmul (x y : f64) : f64 := b64_mult mode_NE x y.
Definition fdiv (x y : f64) : f64 := b64_div mode_NE x y.

(** [|v| <= k 2^e]. *)
Definition bnd (k e : Z) (v : R) : Prop := Rabs v <= IZR k * bpow radix2 e.

Lemma B_fmt x : fmtF (B x).
Proof. apply generic_format_B2R. Qed.

Lemma bnd_fmt k e : (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z -> fmtF (IZR k * bpow radix2 e).
Proof.
  intros Hk He. apply generic_format_FLT.
  apply (FLT_spec radix2 emin prec _ (Float radix2 k e)); [reflexivity | | simpl; unfold emin; lia].
  simpl. rewrite Z.abs_eq by lia. unfold prec. lia.
Qed.

Lemma bnd_round k e z : (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  bnd k e z -> bnd k e (rndF z).
Proof.
  intros Hk He Hz. unfold bnd.
  apply abs_round_le_generic; auto with typeclass_instances. now apply bnd_fmt.
Qed.

Lemma bnd_lt k e : (0 <= k)%Z -> (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z ->
  IZR k * bpow radix2 e < bpow radix2 1024.
Proof.
  intros H0 H1 He.
  replace (bpow radix2 1024) with (IZR (2 ^ (1024 - e)) * bpow radix2 e).
  - apply Rmult_lt_compat_r; [apply bpow_gt_0 | now apply IZR_lt].
  - change (2 ^ (1024 - e))%Z with (Zpower radix2 (1024 - e)).
    rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. ring.
Qed.

Lemma bnd_plus kx ky e x y : bnd kx e x -> bnd ky e y -> bnd (kx + ky) e (x + y).
Proof.
  unfold bnd. intros Hx Hy. rewrite plus_IZR.
  pose proof (Rabs_triang x y). lra.
Qed.

Lemma bnd_minus kx ky e x y : bnd kx e x -> bnd ky e y -> bnd (kx + ky) e (x - y).
Proof.
  unfold bnd. intros Hx Hy. rewrite plus_IZR.
  pose proof (Rabs_triang x (- y)). rewrite Rabs_Ropp in *. unfold Rminus. lra.
Qed.

Lemma bnd_mult kx ky ex ey x y : bnd kx ex x -> bnd ky ey y -> bnd (kx * ky) (ex + ey) (x * y).
Proof.
  unfold bnd. intros Hx Hy. rewrite Rabs_mult, mult_IZR, bpow_plus.
  replace (IZR kx * IZR ky * (bpow radix2 ex * bpow radix2 ey))
    with ((IZR kx * bpow radix2 ex) * (IZR ky * bpow radix2 ey)) by ring.
  apply Rmult_le_compat; auto using Rabs_pos.
Qed.

Lemma bnd_up k e e' v : (0 <= k)%Z -> (e <= e')%Z -> bnd k e v -> bnd k e' v.
Proof.
  unfold bnd. intros Hk H Hv. apply Rle_trans with (1 := Hv).
  apply Rmult_le_compat_l; [now apply IZR_le | now apply bpow_le].
Qed.

(** A bound in units of [2^e] is also one in units of [2^e'], [e' <= e]. *)
Lemma bnd_rescale k e e' v : (e' <= e)%Z -> bnd k e v -> bnd (k * 2 ^ (e - e')) e' v.
Proof.
  unfold bnd. intros H Hv. change (2 ^ (e - e'))%Z with (Zpower radix2 (e - e')).
  rewrite mult_IZR, IZR_Zpower by lia.
  rewrite Rmult_assoc, <- bpow_plus. replace (e - e' + e')%Z with e by ring. exact Hv.
Qed.

Lemma bnd_weaken k k' e v : bnd k e v -> (k <= k')%Z -> bnd k' e v.
Proof.
  unfold bnd. intros Hv H. apply Rle_trans with (1 := Hv).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | now apply IZR_le].
Qed.

(** Each operation, on operands bounded so that the result's bound stays below
    [2^1024], is finite and rounds as the binary64 model does. *)
Lemma fadd_ok k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x + B y) ->
  finite (fadd x y) /\ B (fadd x y) = rndF (B x + B y).
Proof.
  intros Fx Fy Hk He Ho Hm Hb.
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y Fx Fy) as C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [exact C2 | exact C1].
  - eapply Rle_lt_trans; [apply (bnd_round k e _ Hk He Hb) | now apply bnd_lt; lia].
Qed.

Lemma fsub_ok k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x - B y) ->
  finite (fsub x y) /\ B (fsub x y) = rndF (B x - B y).
Proof.
  intros Fx Fy Hk He Ho Hm Hb.
  pose proof (Bminus_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y Fx Fy) as C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [exact C2 | exact C1].
  - eapply Rle_lt_trans; [apply (bnd_round k e _ Hk He Hb) | now apply bnd_lt; lia].
Qed.

Lemma fmul_ok k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x * B y) ->
  finite (fmul x y) /\ B (fmul x y) = rndF (B x * B y).
Proof.
  intros Fx Fy Hk He Ho Hm Hb.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y) as C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [ | exact C1].
    unfold fmul, b64_mult. rewrite C2, Fx, Fy. reflexivity.
  - eapply Rle_lt_trans; [apply (bnd_round k e _ Hk He Hb) | now apply bnd_lt; lia].
Qed.

Lemma fdiv_ok k e x y : finite x -> B y <> 0 -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x / B y) ->
  finite (fdiv x y) /\ B (fdiv x y) = rndF (B x / B y).
Proof.
  intros Fx Hy Hk He Ho Hm Hb.
  pose proof (Bdiv_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y Hy) as C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [ | exact C1].
    unfold fdiv, b64_div. rewrite C2. exact Fx.
  - eapply Rle_lt_trans; [apply (bnd_round k e _ Hk He Hb) | now apply bnd_lt; lia].
Qed.

(** The same, also bounding the result. *)
Lemma fadd_bnd k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x + B y) ->
  finite (fadd x y) /\ B (fadd x y) = rndF (B x + B y) /\ bnd k e (B (fadd x y)).
Proof.
  intros Fx Fy Hk He Ho Hm Hb. destruct (fadd_ok k e x y Fx Fy Hk He Ho Hm Hb) as [F E].
  repeat split; [exact F | exact E | rewrite E; now apply bnd_round].
Qed.

Lemma fsub_bnd k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x - B y) ->
  finite (fsub x y) /\ B (fsub x y) = rndF (B x - B y) /\ bnd k e (B (fsub x y)).
Proof.
  intros Fx Fy Hk He Ho Hm Hb. destruct (fsub_ok k e x y Fx Fy Hk He Ho Hm Hb) as [F E].
  repeat split; [exact F | exact E | rewrite E; now apply bnd_round].
Qed.

Lemma fmul_bnd k e x y : finite x -> finite y -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x * B y) ->
  finite (fmul x y) /\ B (fmul x y) = rndF (B x * B y) /\ bnd k e (B (fmul x y)).
Proof.
  intros Fx Fy Hk He Ho Hm Hb. destruct (fmul_ok k e x y Fx Fy Hk He Ho Hm Hb) as [F E].
  repeat split; [exact F | exact E | rewrite E; now apply bnd_round].
Qed.

Lemma fdiv_bnd k e x y : finite x -> B y <> 0 -> (0 <= k < 2 ^ 53)%Z -> (-1074 <= e)%Z ->
  (k < 2 ^ (1024 - e))%Z -> (e <= 1024)%Z -> bnd k e (B x / B y) ->
  finite (fdiv x y) /\ B (fdiv x y) = rndF (B x / B y) /\ bnd k e (B (fdiv x y)).
Proof.
  intros Fx Hy Hk He Ho Hm Hb. destruct (fdiv_ok k e x y Fx Hy Hk He Ho Hm Hb) as [F E].
  repeat split; [exact F | exact E | rewrite E; now apply bnd_round].
Qed.
