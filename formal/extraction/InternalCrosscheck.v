(** The proved Q128 and Q256 transcriptions (formal/q), rounding tests
    (formal/binary64/RoundingTest.v), and exp's reduction, fast value, accurate path
    and small-argument path (formal/exp/ExpReduction.v, ExpFast.v, ExpAccurate.v,
    ExpSmall.v), extracted to OCaml so formal/extraction/internaldriver.ml can run
    them on the internal cross-check corpus and compare with the Rust code bit for
    bit. A value travels as its sign,
    its exponent and its significand's 64-bit limbs, least significant first. *)

From Coq Require Import ZArith List Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Q Require Import Limbs Digits64 Q128 Q256.
From Binary64 Require Import IEEE64 RoundingTest.
Require ExpReduction ExpFast ExpAccurate ExpSmall.
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

(** exp's reduction (ExpReduction.v): [n], [r1], [p2], [e2], [r_hi], [r_lo]. *)
Definition x_reduce x :=
  let '(n, r1, p2, e2, rh, rl) := ExpReduction.reduce (b64_of_bits x) in
  map bits_of_b64 [n; r1; p2; e2; rh; rl].

(** exp's fast value (ExpFast.v): [(y_hi, y_lo)] for [(r_hi, r_lo)] and [j]. *)
Definition x_fast rh rl j :=
  let '(yh, yl) := ExpFast.fast_at (b64_of_bits rh) (b64_of_bits rl) (Z.to_nat j) in
  map bits_of_b64 [yh; yl].

(** exp's accurate path (ExpAccurate.v): the 128-bit value at [x]'s reduced
    argument, for the table index and scale the Rust code computed. *)
Definition x_accurate x j k :=
  let '(n, r1, p2, e2, _, _) := ExpReduction.reduce (b64_of_bits x) in
  q128_out (ExpAccurate.accurate_at (ExpAccurate.acc_r n r1 p2 e2) (Z.to_nat j) k).

(** exp's small-argument path (ExpSmall.v): [h], [w] and the result. *)
Definition x_small x :=
  let '(h, w) := ExpSmall.small_parts (b64_of_bits x) in
  (bits_of_b64 h, q128_out w, bits_of_b64 (ExpSmall.small (b64_of_bits x))).

Extraction "internalcrosscheck.ml" x_small x_accurate x_fast x_reduce x_decide_with x_decide_scaled x_q128_mul x_q128_add x_q128_to_f64 x_q128_from_f64
  x_q256_mul x_q256_add x_q256_to_f64 x_q256_from_f64 x_q256_from_limbs.
