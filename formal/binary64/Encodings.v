(** A binary64 encoding's value, for constants given by their bits: when the
    encoding decodes to a finite [±m·2^(−k)] (a computation, closed by
    [eq_refl]), its value is that rational, which CoqInterval can read. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid.

Open Scope R_scope.

Lemma bits_val (n : Z) (s : bool) (m : positive) (k : nat) :
  binary_float_of_bits_aux 52 11 n = F754_finite s m (- Z.of_nat k) ->
  B (b64_of_bits n) = IZR (cond_Zopp s (Zpos m)) / 2 ^ k.
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, D.
  unfold FF2R, F2R. cbn [Fnum Fexp]. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ.
  reflexivity.
Qed.

Lemma bits_zero (n : Z) (s : bool) :
  binary_float_of_bits_aux 52 11 n = F754_zero s -> B (b64_of_bits n) = 0.
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, D. reflexivity.
Qed.

Lemma bits_finite (n : Z) (s : bool) (m : positive) (e : Z) :
  binary_float_of_bits_aux 52 11 n = F754_finite s m e -> finite (b64_of_bits n).
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, D. reflexivity.
Qed.

(** Such a value is a multiple of [2^(−K)] for any [K >= k]. *)
Lemma val_grid (m : Z) (k K : nat) : (k <= K)%nat -> on_grid (- Z.of_nat K) (IZR m / 2 ^ k).
Proof.
  intros H. exists (m * 2 ^ Z.of_nat (K - k))%Z.
  rewrite mult_IZR, bpow_opp, bpow_powerRZ, <- pow_powerRZ.
  rewrite <- ?pow_IZR. change (IZR radix2) with 2.
  replace (2 ^ K) with (2 ^ (K - k) * 2 ^ k) by (rewrite <- pow_add; f_equal; lia).
  field. split; apply pow_nonzero; lra.
Qed.

Lemma bits_finite_zero (n : Z) (s : bool) :
  binary_float_of_bits_aux 52 11 n = F754_zero s -> finite (b64_of_bits n).
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, D. reflexivity.
Qed.
