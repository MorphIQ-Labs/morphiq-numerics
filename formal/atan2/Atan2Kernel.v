(** The transcription of atan2 (crates/morphiq-numerics/src/atan2/mod.rs,
    docs/atan2.md): the special values, the form and ratio of a finite pair, the
    tiny ratios, the scaled double-word quotient, the table and series for
    atan, the four forms, the rounding decision, the accurate path's Newton
    step in Q256, and the public entry, each operation the proved IEEE 754
    binary64 or Q256 operation the Rust computes, in the Rust's order. The
    constants are formal/atan2/Atan2Tables.v; the sine and cosine series and
    Q256 pi/2 are asin's (formal/asin/AsinKernel.v), which are trig's.

    These are definitions only: formal/extraction/InternalCrosscheck.v extracts
    them and scripts/check_formal.sh runs them against the Rust code's results
    on the internal cross-check corpus, bit for bit. Proofs that they meet
    docs/atan2.md's bounds are not written. *)

From Coq Require Import ZArith List.
From Flocq Require Import Zaux IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt RoundingTest.
From Q Require Import Q256 Q256Real.
Require Import AsinTables AsinKernel Atan2Tables.
Import ListNotations.
Open Scope Z_scope.

(** The Rust constants, as binary64 encodings. *)
Definition atan2_pi := aw 0x400921fb54442d18.
Definition atan2_half_pi_f64 := aw 0x3ff921fb54442d18.
Definition atan2_quarter_pi := aw 0x3fe921fb54442d18.
Definition atan2_three_quarter_pi := aw 0x4002d97c7f3321d2.
Definition atan2_infinity := aw 0x7ff0000000000000.
Definition atan2_min_positive := aw 0x0010000000000000.
(** The rounding test's [EPS = 2^-62 (1 + 2^-50)]. *)
Definition atan2_eps := aw 0x3c10000000000004.
(** [TINY = 2^-900]. *)
Definition atan2_tiny := aw 0x07b0000000000000.

(** The four forms of the angle. *)
Inductive form := Phi | HalfPiMinus | PiMinus | HalfPiPlus.
Definition form_of_z (z : Z) : form :=
  match z with 0 => Phi | 1 => HalfPiMinus | 2 => PiMinus | _ => HalfPiPlus end.

Definition atan2_cmp_is (x y : f64) (c : comparison) : bool :=
  match asin_cmp x y with Some r => match r, c with Lt, Lt | Eq, Eq | Gt, Gt => true | _, _ => false end | None => false end.

(** [series]: atan of the double-word [(zh, zl)] in [(0, 1]]. *)
Definition atan2_series (zh zl : f64) : f64 * f64 :=
  let i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter in
  match asin_cmp i asin_zero with
  | Some Eq =>
      let z2 := fmul zh zh in
      let q k := aw (nth (Z.to_nat k) atan2_poly0 0) in
      let p := fadd (q 0) (fmul z2 (fadd (q 1) (fmul z2 (fadd (q 2) (fmul z2 (q 3)))))) in
      add_f64_64 zh zl (fmul (fmul zh z2) p)
  | _ =>
      let '(th, tl) := two_sum64 (fsub zh (fmul i asin_inv64)) zl in
      let row := nth (Z.to_nat (asin_index i - 1)) atan2_segments [] in
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

(** [2^e] for [|e| <= 1023]. *)
Definition atan2_pow2 (e : Z) : f64 := aw (Z.shiftl (1023 + e) 52).

(** [x * 2^-k], in two exact multiplications. *)
Definition atan2_scale (x : f64) (k : Z) : f64 :=
  let half := Z.quot k 2 in
  fmul (fmul x (atan2_pow2 (- half))) (atan2_pow2 (- (k - half))).

(** The unbiased exponent of the leading bit of a finite positive [x]. *)
Definition atan2_exponent (x : f64) : Z :=
  let bits := bits_of_b64 x in
  let biased := Z.shiftr bits 52 in
  if biased =? 0 then
    let fraction := Z.land bits (2 ^ 52 - 1) in
    -1011 - (63 - Z.log2 fraction)
  else biased - 1023.

(** [fast]: the double-word of the angle and [phi] itself. *)
Definition atan2_fast (n d : f64) (f : form) : (f64 * f64) * (f64 * f64) :=
  let e := atan2_exponent d in
  let ns := atan2_scale n e in
  let ds := atan2_scale d e in
  let q := fdiv ns ds in
  let '(p, pe) := two_prod64 q ds in
  let residual := fsub (fsub ns p) pe in
  let '(th, tl) := fast_two_sum64 q (fdiv residual ds) in
  let '(ph, pl) := atan2_series th tl in
  let '(hh, hl) := two_sum64 (aw (fst atan2_half_pi)) (aw (snd atan2_half_pi)) in
  let y :=
    match f with
    | Phi => (ph, pl)
    | HalfPiMinus => sub64 hh hl ph pl
    | HalfPiPlus => add64 hh hl ph pl
    | PiMinus => let '(mh, ml) := mul_f64_64 hh hl asin_two in sub64 mh ml ph pl
    end in
  (y, (ph, pl)).

Definition atan2_decide (y : f64 * f64) : option f64 := decide_with (fst y) (snd y) atan2_eps.

(** [recip]: [1/c] with [c] scaled into [[1, 2)] first. *)
Definition atan2_recip (c : q256) : q256 :=
  let top := Q256Real.top c in
  Q256Real.mul_pow2 (q_recip (Q256Real.mul_pow2 c (- top))) (- top).

(** [accurate_value]: one Newton step from [phi], then the form's constant, before rounding. *)
Definition atan2_accurate_value (n d : f64) (f : form) (phi : f64 * f64) : q256 :=
  let phi0 := Q256.add (qf (fst phi)) (qf (snd phi)) in
  let '(sin, cos) := q_sin_cos phi0 in
  let nq := qf n in
  let dq := qf d in
  let numerator := Q256.add (Q256.mul nq cos) (Q256.neg_q (Q256.mul dq sin)) in
  let denominator := Q256.add (Q256.mul dq cos) (Q256.mul nq sin) in
  let phi1 := Q256.add phi0 (Q256.mul numerator (atan2_recip denominator)) in
  match f with
  | Phi => phi1
  | HalfPiMinus => Q256.add q_half_pi (Q256.neg_q phi1)
  | HalfPiPlus => Q256.add q_half_pi phi1
  | PiMinus => Q256.add (Q256Real.mul_pow2 q_half_pi 1) (Q256.neg_q phi1)
  end.

(** [x = m 2^e] with [m] odd, for a finite positive [x]. *)
Definition atan2_odd_part (x : f64) : Z * Z :=
  let bits := bits_of_b64 x in
  let biased := Z.shiftr bits 52 in
  let fraction := Z.land bits (2 ^ 52 - 1) in
  let '(m, e) := if biased =? 0 then (fraction, -1074) else (Z.lor fraction (2 ^ 52), biased - 1075) in
  let shift := Z.log2 (Z.land m (- m)) in
  (Z.shiftr m shift, e + shift).

(** [tiny_phi]: [atan (n/d)] for [n/d < 2^-900]. *)
Definition atan2_tiny_phi (n d quotient : f64) : f64 :=
  if atan2_cmp_is quotient atan2_min_positive Gt then quotient
  else
    let '(mn, en) := atan2_odd_part n in
    let '(md, ed) := atan2_odd_part d in
    if andb (mn mod md =? 0) (en - ed =? -1075) then aw ((mn / md - 1) / 2) else quotient.

(** [angle]: the magnitude for finite nonzero [a], [b]. *)
Definition atan2_angle (a b : f64) (negative : bool) : f64 :=
  let swap := atan2_cmp_is a b Gt in
  let f := match swap, negative with
           | false, false => Phi | true, false => HalfPiMinus
           | false, true => PiMinus | true, true => HalfPiPlus end in
  let n := if swap then b else a in
  let d := if swap then a else b in
  let quotient := fdiv n d in
  if atan2_cmp_is quotient atan2_tiny Lt then
    match f with
    | Phi => atan2_tiny_phi n d quotient
    | HalfPiMinus | HalfPiPlus => atan2_half_pi_f64
    | PiMinus => atan2_pi
    end
  else
    let '(y, phi) := atan2_fast n d f in
    match atan2_decide y with
    | Some r => r
    | None => Q256.to_f64 (atan2_accurate_value n d f phi)
    end.

(** The public [atan2]. *)
Definition atan2_entry (y x : f64) : f64 :=
  if orb (asin_is_nan y) (asin_is_nan x) then asin_nan
  else
    let a := aw (Z.land (bits_of_b64 y) (asin_sign_bit - 1)) in
    let b := aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)) in
    let negative := negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0) in
    let eq0 v := atan2_cmp_is v asin_zero Eq in
    let eqinf v := atan2_cmp_is v atan2_infinity Eq in
    let magnitude :=
      if eq0 a then (if negative then atan2_pi else asin_zero)
      else if eq0 b then atan2_half_pi_f64
      else if eqinf a then
        (if eqinf b then (if negative then atan2_three_quarter_pi else atan2_quarter_pi)
         else atan2_half_pi_f64)
      else if eqinf b then (if negative then atan2_pi else asin_zero)
      else atan2_angle a b negative in
    asin_with_sign magnitude y.
