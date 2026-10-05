(** The proved IEEE 754 definitions (formal/binary64/IEEE64*.v), extracted to
    OCaml on raw binary64 bits, so formal/extraction/driver.ml can run them on
    the cross-check corpus and compare with the Rust library bit for bit. This
    ties the definitions the theorems describe to the code that ships: a
    mistranscribed operation shows as a mismatch. *)

From Coq Require Import ZArith Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Div.

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

Extraction "crosscheck.ml" x_two_sum x_fast_two_sum x_two_prod x_add_f64 x_add x_sub
  x_mul_f64 x_mul x_div_f64 x_div.
