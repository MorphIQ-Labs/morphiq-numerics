(** The exact double-word square on erfcx's finite negative branch. This
    lemma uses the implemented branch threshold; its mathematical overflow
    classification is a separate obligation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul IEEE64Eft Encodings RoundingConstant.
From Interval Require Import Tactic.
Require Import StageGappa.
Require ExpReduction.
Open Scope R_scope.

Definition reflection_limit : f64 := b64_of_bits 13851560577301767119.

Lemma reflection_limit_value : -26.63 < B reflection_limit < -26.62.
Proof.
  unfold reflection_limit.
  rewrite (bits_val 13851560577301767119 true 7495322764862415 48 eq_refl).
  simpl. split; lra.
Qed.

Theorem reflection_square_ieee x : finite x -> B reflection_limit < B x < - /2 ->
  let '(s,se) := two_prod64 x x in
  finite s /\ finite se /\ B s + B se = B x * B x /\
  /4 <= B s < 710 /\ Rabs (B se) <= bpow radix2 (-44).
Proof.
  intros Fx Hx. pose proof reflection_limit_value as Limit.
  assert (X : -26.63 < B x < - /2) by lra.
  assert (Xb : Rabs (B x) <= bpow radix2 5).
  { change (bpow radix2 5) with 32. apply Rabs_le; lra. }
  assert (D : in_two_prod_domain (B x) (B x)).
  { right. rewrite Rabs_pos_eq by nra.
    apply Rle_trans with (bpow radix2 (-2)); [apply bpow_le; lia | ].
    change (bpow radix2 (-2)) with (/4). nra. }
  pose proof (two_prod_ieee 5 5 x x Fx Fx Xb Xb ltac:(lia) ltac:(lia) ltac:(lia) D) as TP.
  destruct (two_prod64 x x) as [s se]. destruct TP as [Fs [Fse [Bs Exact]]].
  assert (S : /4 <= B s <= 709.5).
  { rewrite Bs. split.
    - change (/4) with (bpow radix2 (-2)).
      apply round_ge_generic; [exact _ | exact _ | | change (bpow radix2 (-2)) with (/4); nra].
      apply generic_format_bpow; unfold FLT_exp, emin, prec; lia.
    - apply round_le_generic; [exact _ | exact _ | | nra].
      replace 709.5 with (IZR 1419 * bpow radix2 (-1)) by (change (bpow radix2 (-1)) with (/2); change (IZR 1419) with 1419; lra).
      apply ExpReduction.fmt_int; lia. }
  assert (Err : Rabs (B se) <= bpow radix2 (-44)).
  { assert (E := rnd_err_below (B x * B x) 10 ltac:(lia)
      ltac:(change (bpow radix2 10) with 1024; rewrite Rabs_pos_eq by nra; nra)).
    rewrite <- Bs in E. replace (B se) with (- (B s - B x * B x)) by lra.
    rewrite Rabs_Ropp. exact E. }
  split; [exact Fs | split; [exact Fse | split; [exact Exact | split; [split; lra | exact Err]]]].
Qed.
