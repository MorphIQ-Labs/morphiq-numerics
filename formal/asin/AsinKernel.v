(** The transcription of asin (crates/morphiq-numerics/src/asin/mod.rs,
    docs/asin.md): the reduction, the fast path's series and its rounding
    decision, the accurate path's Newton step in Q256, and the public entry,
    each operation the proved IEEE 754 binary64 or Q256 operation the Rust
    computes, in the Rust's order. The constants are formal/asin/AsinTables.v.

    These are definitions only: formal/extraction/InternalCrosscheck.v extracts
    them and scripts/check_formal.sh runs them against the Rust code's results
    on the internal cross-check corpus, bit for bit. Proofs that they meet
    docs/asin.md's bounds are not written. *)

From Coq Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt RoundingTest.
From Q Require Import Q256.
Require Import AsinTables.
Import ListNotations.
Open Scope Z_scope.

Definition aw (z : Z) : f64 := b64_of_bits z.

(** The Rust constants, as binary64 encodings. *)
Definition asin_zero := aw 0x0000000000000000.
Definition asin_one := aw 0x3ff0000000000000.
Definition asin_half := aw 0x3fe0000000000000.
Definition asin_two := aw 0x4000000000000000.
Definition asin_64 := aw 0x4050000000000000.
Definition asin_inv64 := aw 0x3f90000000000000.
Definition asin_shifter := aw 0x4338000000000000.
(** [SPLIT], the largest binary64 below sqrt (1/2). *)
Definition asin_split := aw 0x3fe6a09e667f3bcc.
(** [ASIN_IS_X]: [asin x = x] below it. *)
Definition asin_is_x := aw 0x3e57137449123ef6.
(** The rounding test's [EPS = 2^-62 (1 + 2^-50)]. *)
Definition asin_eps := aw 0x3c10000000000004.
(** [RN(pi/2)], which is [asin 1]. *)
Definition asin_half_pi_f64 := aw 0x3ff921fb54442d18.
Definition asin_nan := aw 0x7ff8000000000000.

(** [x <= y] and the other comparisons on finite binary64 numbers. *)
Definition asin_cmp (x y : f64) : option comparison := Bcompare 53 1024 x y.
Definition asin_le (x y : f64) : bool :=
  match asin_cmp x y with Some Lt | Some Eq => true | _ => false end.

(** A finite binary64 holding a non-negative integer, as that integer: the
    table index [i as usize]. *)
Definition asin_index (f : f64) : Z :=
  match f with
  | B754_finite _ m e _ => if (e <? 0)%Z then Z.shiftr (Zpos m) (- e) else Z.shiftl (Zpos m) e
  | _ => 0
  end.

(** [Reduced::of]: [true] with [z = (x, 0)] on the direct branch, [false] with
    the double-word [z = sqrt ((1 - x)/2)] on the complement. *)
Definition asin_reduced (x : f64) : bool * (f64 * f64) :=
  if asin_le x asin_split then (true, (x, asin_zero))
  else
    let u := fmul (fsub asin_one x) asin_half in
    let s := fsqrt u in
    let '(sq, se) := two_prod64 s s in
    let residual := fsub (fsub u sq) se in
    (false, two_sum64 s (fdiv residual (fmul asin_two s))).

(** [series]: asin of the double-word [(zh, zl)] in [[0, SPLIT]]. *)
Definition asin_series (zh zl : f64) : f64 * f64 :=
  let i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter in
  match asin_cmp i asin_zero with
  | Some Eq =>
      let z2 := fmul zh zh in
      let q k := aw (nth (Z.to_nat k) asin_poly0 0) in
      let p := fadd (q 0) (fmul z2 (fadd (q 1) (fmul z2 (fadd (q 2) (fmul z2 (q 3)))))) in
      add_f64_64 zh zl (fmul (fmul zh z2) p)
  | _ =>
      let '(th, tl) := two_sum64 (fsub zh (fmul i asin_inv64)) zl in
      let row := nth (Z.to_nat (asin_index i - 1)) asin_segments [] in
      let c k := aw (nth (Z.to_nat k) row 0) in
      let g := fadd (c 4) (fmul th (fadd (c 5) (fmul th (fadd (c 6) (fmul th (fadd (c 7)
                (fmul th (fadd (c 8) (fmul th (fadd (c 9) (fmul th (fadd (c 10)
                (fmul th (fadd (c 11) (fmul th (c 12)))))))))))))))) in
      let '(ph, pl) := two_prod64 th (c 2) in
      let tail := fadd (fadd pl (fadd (fmul th (c 3)) (fmul tl (c 2)))) (fmul (fmul th th) g) in
      let '(yh, yl) := two_sum64 (c 0) (c 1) in
      let '(vh, vl) := fast_two_sum64 ph tail in
      add64 yh yl vh vl
  end.

(** [Reduced::fast]: the double-word [y] of the positive result and the value
    Newton's step starts from, [y] or, for the complement, [delta]. *)
Definition asin_fast (red : bool * (f64 * f64)) : (f64 * f64) * (f64 * f64) :=
  match red with
  | (true, (x, _)) => let y := asin_series x asin_zero in (y, y)
  | (false, (zh, zl)) =>
      let '(sh, sl) := asin_series zh zl in
      let '(dh, dl) := mul_f64_64 sh sl asin_two in
      let '(hh, hl) := two_sum64 (aw (fst asin_half_pi)) (aw (snd asin_half_pi)) in
      (sub64 hh hl dh dl, (dh, dl))
  end.

Definition asin_decide (y : f64 * f64) : option f64 := decide_with (fst y) (snd y) asin_eps.

(** The Q256 operations the accurate path uses. *)
Definition qf (f : f64) : q256 := Q256.from_f64 (bits_of_b64 f).
Definition q_one : q256 := Q false [0; 0; 0; 2 ^ 63] (-255).
Definition q_sub (a b : q256) : q256 := Q256.add a (Q256.neg_q b).
Definition q_half_pi : q256 := Q256.new false (fst asin_q_half_pi) (snd asin_q_half_pi).

(** [trig::accurate]'s series in [s = r^2], from the last step to the first. *)
Definition q_series (s : q256) (steps : list (list Z * Z)) : q256 :=
  fold_left (fun h '(m, e) => q_sub q_one (Q256.mul (Q256.mul s (Q256.new false m e)) h))
    (rev steps) q_one.

Definition q_sin_cos (r : q256) : q256 * q256 :=
  let s := Q256.mul r r in
  (Q256.mul r (q_series s asin_sin_steps), q_series s asin_cos_steps).

(** [Q256::recip]: [1/RN(c)] rounded, then three Newton steps. *)
Definition q_recip (c : q256) : q256 :=
  let y0 := qf (fdiv asin_one (Q256.to_f64 c)) in
  let step y := let error := q_sub q_one (Q256.mul c y) in Q256.add y (Q256.mul y error) in
  step (step (step y0)).

(** The start as a Q256 value: [start.hi + start.lo]. *)
Definition asin_start (start : f64 * f64) : q256 := Q256.add (qf (fst start)) (qf (snd start)).

(** [Reduced::accurate_value]: one Newton step from [start], before rounding. *)
Definition asin_accurate_value (direct : bool) (x : f64) (start : f64 * f64) : q256 :=
  let start := asin_start start in
  let '(sin, cos) := q_sin_cos start in
  if direct then
    let residual := q_sub (qf x) sin in
    Q256.add start (Q256.mul residual (q_recip cos))
  else
    let residual := q_sub cos (qf x) in
    let delta := Q256.add start (Q256.mul residual (q_recip sin)) in
    q_sub q_half_pi delta.

(** [Reduced::accurate]: that value rounded. *)
Definition asin_accurate (direct : bool) (x : f64) (start : f64 * f64) : f64 :=
  Q256.to_f64 (asin_accurate_value direct x start).

(** [asin]'s result for a magnitude in [[ASIN_IS_X, 1)]. *)
Definition asin_positive (x : f64) : f64 :=
  let red := asin_reduced x in
  let '(y, start) := asin_fast red in
  match asin_decide y with
  | Some r => r
  | None => asin_accurate (fst red) x start
  end.

Definition asin_is_nan (x : f64) : bool := match x with B754_nan _ _ _ => true | _ => false end.
Definition asin_sign_bit : Z := 2 ^ 63.
Definition asin_with_sign (v : f64) (x : f64) : f64 :=
  aw (Z.lor (Z.land (bits_of_b64 v) (asin_sign_bit - 1)) (Z.land (bits_of_b64 x) asin_sign_bit)).

(** The public [asin]. *)
Definition asin_entry (x : f64) : f64 :=
  if asin_is_nan x then x
  else
    let a := aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)) in
    match asin_cmp a asin_one with
    | Some Gt => asin_nan
    | Some Eq => asin_with_sign asin_half_pi_f64 x
    | _ =>
        match asin_cmp a asin_is_x with
        | Some Lt => x
        | _ => asin_with_sign (asin_positive a) x
        end
    end.
