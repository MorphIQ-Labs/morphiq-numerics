(** The proved IEEE 754 definitions (formal/binary64/IEEE64*.v), extracted to
    OCaml on raw binary64 bits, so formal/extraction/driver.ml can run them on
    the cross-check corpus and compare with the Rust library bit for bit. This
    ties the definitions the theorems describe to the code that ships: a
    mistranscribed operation shows as a mismatch. *)

From Coq Require Import ZArith List Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Div IEEE64Sqrt SqrtAlgorithm.
Require DwExp.
From Binary64 Require Reduce.

Definition of_bits (z : Z) : f64 := b64_of_bits z.
Definition pair_bits (p : f64 * f64) : Z * Z := (bits_of_b64 (fst p), bits_of_b64 (snd p)).

Definition x_two_sum a b := pair_bits (two_sum64 (of_bits a) (of_bits b)).
Definition x_fast_two_sum a b := pair_bits (fast_two_sum64 (of_bits a) (of_bits b)).
Definition x_two_prod a b := pair_bits (two_prod64 (of_bits a) (of_bits b)).
Definition x_add_f64 xh xl y := pair_bits (add_f64_64 (of_bits xh) (of_bits xl) (of_bits y)).
Definition x_add xh xl yh yl := pair_bits (add64 (of_bits xh) (of_bits xl) (of_bits yh) (of_bits yl)).
Definition x_sub xh xl yh yl := pair_bits (sub64 (of_bits xh) (of_bits xl) (of_bits yh) (of_bits yl)).
Definition x_mul_f64 xh xl y := pair_bits (mul_f64_64 (of_bits xh) (of_bits xl) (of_bits y)).
Definition x_mul xh xl yh yl := pair_bits (mul64 (of_bits xh) (of_bits xl) (of_bits yh) (of_bits yl)).
Definition x_div_f64 xh xl y := pair_bits (div_f64_64 (of_bits xh) (of_bits xl) (of_bits y)).
Definition x_div xh xl yh yl := pair_bits (div64 (of_bits xh) (of_bits xl) (of_bits yh) (of_bits yl)).
(** sqrt.rs's transcription, proved equal to [fsqrt] (SqrtAlgorithm.v). *)
Definition x_sqrt x := bits_of_b64 (sqrt_rs (of_bits x)).
(** exp_split's transcription (formal/fast/DwExp.v): a presence flag, the
    value's words and the exponent offset by 4096, or four zeros for [None]. *)
Definition x_exp_split xh xl : Z * Z * Z * Z :=
  match DwExp.dwexp64 (of_bits xh) (of_bits xl) with
  | Some (zh, zl, k) => (1%Z, bits_of_b64 zh, bits_of_b64 zl, (k + 4096)%Z)
  | None => (0%Z, 0%Z, 0%Z, 0%Z)
  end.

(** The slice reductions (formal/binary64/Reduce.v). *)
Definition of_list (l : list Z) : list f64 := List.map of_bits l.
Definition x_sum x := bits_of_b64 (Reduce.sum64 (of_list x)).
Definition x_sum2 x := bits_of_b64 (Reduce.sum2_64 (of_list x)).
Definition x_dot x y := bits_of_b64 (Reduce.dot64 (of_list x) (of_list y)).
Definition x_dot2 x y := bits_of_b64 (Reduce.dot2_64 (of_list x) (of_list y)).
Definition x_sum_squares x := bits_of_b64 (Reduce.sum_squares64 (of_list x)).
Definition x_sum_squares2 x := bits_of_b64 (Reduce.sum_squares2_64 (of_list x)).
Definition x_max_abs x := bits_of_b64 (Reduce.max_abs64 (of_list x)).

Extraction "crosscheck.ml" x_sum x_sum2 x_dot x_dot2 x_sum_squares x_sum_squares2 x_max_abs
  x_two_sum x_fast_two_sum x_two_prod x_add_f64 x_add x_sub
  x_mul_f64 x_mul x_div_f64 x_div x_sqrt x_exp_split.
