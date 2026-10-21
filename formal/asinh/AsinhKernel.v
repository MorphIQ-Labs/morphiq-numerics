(** The transcription of asinh (crates/morphiq-numerics/src/asinh/mod.rs,
    docs/asinh.md): the series, the logarithm of x + sqrt(x^2 + 1), the large
    form, the rounding decision, the accurate path's two Newton steps in Q256
    with its exponential, and the public entry, each operation the proved IEEE
    754 binary64 or Q256 operation the Rust computes, in the Rust's order; ln's
    fast value is its own proved transcription (formal/ln/LnFastValue.v). The
    constants are formal/asinh/AsinhTables.v.

    These are definitions only: formal/extraction/InternalCrosscheck.v extracts
    them and scripts/check_formal.sh runs them against the Rust code's results
    on the internal cross-check corpus, bit for bit. Proofs that they meet
    docs/asinh.md's bounds are not written. *)

From Coq Require Import ZArith List.
From Flocq Require Import Zaux IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt RoundingTest.
From Q Require Import Q256 Q256Real.
Require Import AsinTables AsinKernel AsinhTables LnFastValue.
Import ListNotations.
Open Scope Z_scope.

(** The Rust constants, as binary64 encodings. *)
Definition asinh_is_x := aw 0x3e57137449123ef6.
Definition asinh_two_m7 := aw 0x3f80000000000000.
Definition asinh_two_28 := aw 0x41b0000000000000.
Definition asinh_shifter := aw 0x4338000000000000.
Definition asinh_quarter := aw 0x3fd0000000000000.
Definition asinh_infinity := aw 0x7ff0000000000000.
(** The rounding test's [EPS = 2^-63 (1 + 2^-50)]. *)
Definition asinh_eps := aw 0x3c00000000000004.

Definition asinh_lt (x y : f64) : bool :=
  match asin_cmp x y with Some Lt => true | _ => false end.

(** [series]: [x + x^3 P(x^2)], [x < 2^-7]. *)
Definition asinh_series (x : f64) : f64 * f64 :=
  let q k := aw (nth (Z.to_nat k) asinh_poly0 0) in
  let x2 := fmul x x in
  let p := fadd (q 0) (fmul x2 (fadd (q 1) (fmul x2 (fadd (q 2) (fmul x2 (q 3)))))) in
  add_f64_64 x asin_zero (fmul (fmul x x2) p).

(** [logarithm]: [ln (x + sqrt (x^2 + 1))], [2^-7 <= x < 2^28]. *)
Definition asinh_logarithm (x : f64) : f64 * f64 :=
  let '(sq, sqe) := two_prod64 x x in
  let '(h1, l1) := two_sum64 asin_one sq in
  let '(uh, ul) := add_f64_64 h1 l1 sqe in
  let root := fsqrt uh in
  let '(rs, rse) := two_prod64 root root in
  let residual := fadd (fsub (fsub uh rs) rse) ul in
  let '(sh, sl) := two_sum64 root (fdiv residual (fmul asin_two root)) in
  let '(a, b) := two_sum64 x sh in
  let '(vh, vl) := add_f64_64 a b sl in
  let '(lh, ll) := lf_ln_fast_value vh in
  add_f64_64 lh ll (fdiv vl vh).

(** [large]: [ln x + ln 2 + 1/(4 x^2)], [x >= 2^28]. *)
Definition asinh_large (x : f64) : f64 * f64 :=
  let '(lh, ll) := lf_ln_fast_value x in
  let '(ch, cl) := two_sum64 (aw (fst asinh_ln2)) (aw (snd asinh_ln2)) in
  let '(sh, sl) := add64 lh ll ch cl in
  add_f64_64 sh sl (fdiv (fdiv asinh_quarter x) x).

(** [fast]: the double-word of [asinh x] for [x] in [(ASINH_IS_X, inf)]. *)
Definition asinh_fast (x : f64) : f64 * f64 :=
  if asinh_lt x asinh_two_m7 then asinh_series x
  else if asinh_lt x asinh_two_28 then asinh_logarithm x
  else asinh_large x.

Definition asinh_decide (y : f64 * f64) : option f64 := decide_with (fst y) (snd y) asinh_eps.

(** The integer a binary64 integer holds. *)
Definition asinh_int (f : f64) : Z :=
  match f with
  | B754_finite s m e _ =>
      cond_Zopp s (if (e <? 0)%Z then Z.shiftr (Zpos m) (- e) else Z.shiftl (Zpos m) e)
  | _ => 0
  end.

(** [exp]: [e^y = m 2^k], [m = exp r], [r = y - k ln 2], with the series' steps
    from the last to the first. *)
Definition asinh_exp (y : q256) : q256 * Z :=
  let k := fsub (fadd (fmul (Q256.to_f64 y) (aw asinh_inv_ln2)) asinh_shifter) asinh_shifter in
  let r := Q256.add y (Q256.neg_q (Q256.mul (qf k) (Q256.new false (fst asinh_ln2_q256) (snd asinh_ln2_q256)))) in
  let h := fold_left (fun h '(m, e) => Q256.add q_one (Q256.mul (Q256.mul r (Q256.new false m e)) h))
             (rev asinh_exp_steps) q_one in
  (h, asinh_int k).

(** [recip]: [1/c] with [c] scaled into [[1, 2)] first. *)
Definition asinh_recip (c : q256) : q256 :=
  let top := Q256Real.top c in
  Q256Real.mul_pow2 (q_recip (Q256Real.mul_pow2 c (- top))) (- top).

(** [newton]: [y + (x - sinh y)/cosh y]. *)
Definition asinh_newton (x y : q256) : q256 :=
  let '(m, k) := asinh_exp y in
  let e := Q256Real.mul_pow2 m k in
  let ei := Q256Real.mul_pow2 (asinh_recip m) (- k) in
  let sinh := Q256Real.mul_pow2 (q_sub e ei) (-1) in
  let cosh := Q256Real.mul_pow2 (Q256.add e ei) (-1) in
  Q256.add y (Q256.mul (q_sub x sinh) (asinh_recip cosh)).

(** [accurate_value]: two Newton steps from the fast value, before rounding. *)
Definition asinh_accurate_value (x : f64) (y : f64 * f64) : q256 :=
  let start := Q256.add (qf (fst y)) (qf (snd y)) in
  let xq := qf x in
  asinh_newton xq (asinh_newton xq start).

Definition asinh_accurate (x : f64) (y : f64 * f64) : f64 := Q256.to_f64 (asinh_accurate_value x y).

(** The public [asinh]. *)
Definition asinh_entry (x : f64) : f64 :=
  if asin_is_nan x then x
  else
    let a := aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)) in
    match asin_cmp a asinh_is_x with
    | Some Lt | Some Eq => x
    | _ =>
        match asin_cmp a asinh_infinity with
        | Some Eq => x
        | _ =>
            let y := asinh_fast a in
            asin_with_sign (match asinh_decide y with Some r => r | None => asinh_accurate a y end) x
        end
    end.
