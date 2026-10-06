(** The proved Q128 and Q256 transcriptions (formal/q) and rounding tests
    (formal/binary64/RoundingTest.v), extracted to OCaml so
    formal/extraction/internaldriver.ml can run them on the internal cross-check corpus and
    compare with q128.rs and q256.rs bit for bit. A value travels as its sign,
    its exponent and its significand's 64-bit limbs, least significant first. *)

From Coq Require Import ZArith List Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Q Require Import Limbs Digits64 Q128 Q256.
From Binary64 Require Import IEEE64 RoundingTest.
Import ListNotations.

Definition limbs (k : nat) (x : Z) : list Z := map (fun i => dig x (Z.of_nat i)) (seq 0 k).

Definition q128_in (n : bool) (e : Z) (l : list Z) : q128 := Q128.Q n (Limbs.v l) e.
Definition q128_out (x : q128) : bool * Z * list Z := (Q128.neg x, Q128.e x, limbs 2 (Q128.m x)).
Definition q256_in (n : bool) (e : Z) (l : list Z) : q256 := Q256.Q n l e.
Definition q256_out (x : q256) : bool * Z * list Z := (Q256.neg x, Q256.e x, Q256.m x).

Definition x_q128_mul n1 e1 l1 n2 e2 l2 := q128_out (Q128.mul (q128_in n1 e1 l1) (q128_in n2 e2 l2)).
Definition x_q128_add n1 e1 l1 n2 e2 l2 := q128_out (Q128.add (q128_in n1 e1 l1) (q128_in n2 e2 l2)).
Definition x_q128_to_f64 n e l := bits_of_b64 (Q128.to_f64 (q128_in n e l)).
Definition x_q128_from_f64 bits := q128_out (Q128.from_f64 bits).
Definition x_q256_mul n1 e1 l1 n2 e2 l2 := q256_out (Q256.mul (q256_in n1 e1 l1) (q256_in n2 e2 l2)).
Definition x_q256_add n1 e1 l1 n2 e2 l2 := q256_out (Q256.add (q256_in n1 e1 l1) (q256_in n2 e2 l2)).
Definition x_q256_to_f64 n e l := bits_of_b64 (Q256.to_f64 (q256_in n e l)).
Definition x_q256_from_f64 bits := q256_out (Q256.from_f64 bits).
Definition x_q256_from_limbs n e l := q256_out (Q256.from_limbs n l e).

(** The rounding tests (RoundingTest.v), on binary64 encodings. *)
Definition opt_bits (o : option f64) : option Z := match o with Some v => Some (bits_of_b64 v) | None => None end.
Definition x_decide_with hi lo eps := opt_bits (decide_with (b64_of_bits hi) (b64_of_bits lo) (b64_of_bits eps)).
Definition x_decide_scaled hi lo eps k := opt_bits (decide_scaled (b64_of_bits hi) (b64_of_bits lo) (b64_of_bits eps) k).

Extraction "internalcrosscheck.ml" x_decide_with x_decide_scaled x_q128_mul x_q128_add x_q128_to_f64 x_q128_from_f64
  x_q256_mul x_q256_add x_q256_to_f64 x_q256_from_f64 x_q256_from_limbs.
