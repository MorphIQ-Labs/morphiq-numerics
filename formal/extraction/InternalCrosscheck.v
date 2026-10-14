(** The proved Q128 and Q256 transcriptions (formal/q), rounding tests
    (formal/binary64/RoundingTest.v), exp's stages (formal/exp/ExpStageReduction.v,
    ExpStageA.v, ExpStageB.v, with formal/binary64/RoundingConstant.v), exp's
    fallback reduction, fast value, accurate path and small-argument path
    (formal/exp/ExpReduction.v, ExpFast.v, ExpAccurate.v, ExpSmall.v), ln's
    reduction and accurate paths (formal/ln/LnReduction.v, LnAccurate.v), and
    ln_1p's screens and stages H and B (formal/ln/Ln1pScreen.v, Ln1pStageH.v,
    Ln1pStageB.v), extracted to OCaml
    so formal/extraction/internaldriver.ml can run them on the internal
    cross-check corpus and compare with the Rust code bit for bit. A value
    travels as its sign, its exponent and its significand's 64-bit limbs, least
    significant first. *)

From Coq Require Import ZArith List Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Q Require Import Limbs Digits64 Q128 Q256 Q256Real.
From Binary64 Require Import IEEE64 RoundingTest.
Require ExpReduction ExpFast ExpAccurate ExpSmall LnReduction LnAccurate Ln1pScreen ExpStageReduction ExpStageA ExpStageB Ln1pStageH Ln1pStageB.
Require Exp2Stages Expm1Stages Exp2FallbackReduction Exp2FallbackAccurate Exp2FallbackFast Exp2.
Require Expm1GeneralReduction Expm1GeneralFast Expm1GeneralAccurate Expm1SmallFast Expm1SmallAccurate Expm1.
Require LnFastValue Ln1pFast LnFastDecision LnEntry.
Require ErfcxReciprocal ErfcxSquare ErfcxMiddlePolynomial ErfcxProduct ErfcxMiddleValue ErfcxQuotient ErfcxQuotientScale ErfcxTailCorrection ErfcxTailValue ErfcxTableSplit ErfcxTableProducts ErfcxTableData ErfcxTableReduction ErfcxTableEntry.
Require ErfcxReflectionExp ErfcxReflectionSubtract ErfcxReflectionFast.
Require ErfcxMiddleFast ErfcxTailFast ErfcxAccurateProduct ErfcxAccurateExponential.
Require NormalGaussianKernel NormalDensityFast NormalDensityDecision NormalFastDecision NormalAccurateGaussian NormalAccurateDensity
  NormalAccurateCenter NormalAccurateCentralCdf NormalErfcxAsymptotic
  NormalScaledArgument NormalAccurateTail NormalTableLookup NormalExtendedTable
  NormalExtendedErfcx NormalAccurateTailFull NormalLogSeries NormalComplementSeries
  NormalAccurateOuter NormalAccurateLogPositive NormalAccurateLogCentral NormalAccurateLogNegative.
Require NormalCenterSmall NormalCenterSmallDecision.
Require NormalCenterFastSquare.
Require NormalCenterFastPolynomial.
Require NormalCenterFastValue NormalCenterFastDecision.
Require NormalCenterCentral NormalCdfCentralFast.
Require NormalLogDw NormalLogCentralFast NormalLogDecision.
Require NormalFastScaledArgument NormalErfcxFastScaled.
Require NormalTailFast NormalTailDecision.
Require NormalOuterSigned.
Require NormalLogNegativeFast.
Import ListNotations.

Definition limbs (k : nat) (x : Z) : list Z := map (fun i => dig x (Z.of_nat i)) (seq 0 k).

Definition q128_in (n : bool) (e : Z) (l : list Z) : q128 := Q128.Q n (Limbs.v l) e.
Definition q128_out (x : q128) : bool * Z * list Z := (Q128.neg x, Q128.e x, limbs 2 (Q128.m x)).
Definition q256_in (n : bool) (e : Z) (l : list Z) : q256 := Q256.Q n l e.
Definition q256_out (x : q256) : bool * Z * list Z := (Q256.neg x, Q256.e x, Q256.m x).

Require Import NormalLogPositiveFast.
Definition x_normal_accurate_gaussian x := q256_out (NormalAccurateGaussian.normal_q_gaussian_regular (b64_of_bits x)).
Definition x_normal_accurate_density x := q256_out (NormalAccurateDensity.normal_q_density_regular (b64_of_bits x)).
Definition x_normal_accurate_center x := q256_out (NormalAccurateCenter.normal_q_center (b64_of_bits x)).
Definition x_normal_accurate_central_cdf x := q256_out (NormalAccurateCentralCdf.normal_q_central_cdf (b64_of_bits x)).
Definition x_normal_gaussian x :=
  let '(h,l,k) := NormalGaussianKernel.normal_gaussian64 (b64_of_bits x) in
  (k,map bits_of_b64 [h;l]).
Definition x_normal_density_fast x :=
  let '(h,l,k) := NormalDensityFast.normal_density_fast64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 h in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalFastDecision.normal_interval_decide64 h l e)).
Definition x_normal_center_small x :=
  let '(h,l) := NormalCenterSmall.normal_center_small64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalCenterSmallDecision.normal_center_small_decide64 (b64_of_bits x))).
Definition x_normal_center_tail x :=
  let '(h,l,t) := NormalCenterFastSquare.normal_center_square_tail64 (b64_of_bits x) in
  map bits_of_b64 [h;l;t].
Definition x_normal_center_shape x :=
  let '(h,l) := NormalCenterFastPolynomial.normal_center_shape64 (b64_of_bits x) in
  map bits_of_b64 [h;l].
Definition x_normal_center_fast x :=
  let '(h,l) := NormalCenterFastValue.normal_center_regular64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalCenterFastDecision.normal_center_regular_decide64 (b64_of_bits x))).
Definition x_normal_center_central x :=
  let '(h,l) := NormalCenterCentral.normal_center_central64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalCenterCentral.normal_center_central_decide64 (b64_of_bits x))).
Definition x_normal_cdf_central x :=
  let '(h,l) := NormalCdfCentralFast.normal_cdf_central_fast64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalCdfCentralFast.normal_cdf_central_decide64 (b64_of_bits x))).
Definition x_normal_log_central x :=
  let '(h,l) := NormalLogCentralFast.normal_log_central_fast64 (b64_of_bits x) in
  let e:=NormalLogDecision.normal_log_guard64 h in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalLogDecision.normal_log_central_decide64 (b64_of_bits x))).
Definition x_normal_fast_scaled_argument x :=
  let '(h,l) := NormalFastScaledArgument.normal_fast_scaled_argument64 (b64_of_bits x) in
  map bits_of_b64 [h;l].
Definition x_normal_erfcx_fast_scaled x :=
  let '(h,l) := NormalErfcxFastScaled.normal_erfcx_fast_scaled64 (b64_of_bits x) in
  map bits_of_b64 [h;l].
Definition x_normal_tail_fast x :=
  let '(h,l,k) := NormalTailFast.normal_tail_fast64 (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalTailDecision.normal_tail_decide64 (b64_of_bits x))).
Definition x_normal_outer_complement negative c x :=
  let '(h,l) := NormalOuterSigned.normal_outer_signed_fast64 negative c (b64_of_bits x) in
  let e:=NormalDensityDecision.normal_density_guard64 (b64_abs h) in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalOuterSigned.normal_outer_signed_decide64 negative c (b64_of_bits x))).
Definition x_normal_outer_cdf x := x_normal_outer_complement false (ErfcxDecision.erfcx_pow2 0) x.
Definition x_normal_outer_center_positive x := x_normal_outer_complement false (ErfcxDecision.erfcx_pow2 (-1)) x.
Definition x_normal_outer_center_negative x := x_normal_outer_complement true (ErfcxDecision.erfcx_pow2 (-1)) x.
Definition x_normal_log_negative x :=
  let '(h,l) := NormalLogNegativeFast.normal_log_negative_fast64 (b64_of_bits x) in
  let e:=NormalLogDecision.normal_log_guard64 h in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalLogNegativeFast.normal_log_negative_decide64 (b64_of_bits x))).
Definition x_normal_log_positive x :=
  let '(h,l,_) := NormalLogPositiveFast.normal_log_positive_fast64 (b64_of_bits x) in
  let e:=NormalLogDecision.normal_log_guard64 h in
  (map bits_of_b64 [h;l;e],option_map bits_of_b64 (NormalLogPositiveFast.normal_log_positive_decide64 (b64_of_bits x))).
Definition x_normal_erfcx_asym n e l := q256_out (NormalErfcxAsymptotic.normal_q_erfcx_asymptotic (q256_in n e l)).
Definition x_normal_scaled_argument x := q256_out (NormalScaledArgument.normal_q_scaled_argument (b64_of_bits x)).
Definition x_normal_accurate_tail_asym x := q256_out (NormalAccurateTail.normal_q_tail_asym (b64_of_bits x)).
Definition x_normal_erfcx_small_table n e l := q256_out (NormalTableLookup.normal_q_erfcx_small_table (q256_in n e l)).
Definition x_normal_erfcx_extended_table n e l := q256_out (NormalExtendedTable.normal_q_erfcx_extended_table (q256_in n e l)).
Definition x_normal_erfcx_positive n e l := q256_out (NormalExtendedErfcx.normal_q_erfcx_positive (q256_in n e l)).
Definition x_normal_accurate_tail x := q256_out (NormalAccurateTailFull.normal_q_tail (b64_of_bits x)).
Definition x_normal_logarithm n e l := q256_out (NormalLogSeries.normal_q_logarithm (q256_in n e l)).
Definition x_normal_log_complement n e l := q256_out (NormalComplementSeries.normal_q_log_complement (q256_in n e l)).
Definition x_normal_accurate_outer_cdf x := q256_out (NormalAccurateOuter.normal_q_outer_complement ErfcxAccurateTerms.q_one (b64_of_bits x)).
Definition x_normal_accurate_outer_center x := q256_out (NormalAccurateOuter.normal_q_outer_complement ErfcxAccurateSquare.q_half (b64_of_bits x)).
Definition x_normal_accurate_log_positive x := q256_out (NormalAccurateLogPositive.normal_q_log_cdf_positive (b64_of_bits x)).
Definition x_normal_accurate_log_central x := q256_out (NormalAccurateLogCentral.normal_q_log_cdf_central (b64_of_bits x)).
Definition x_normal_accurate_log_negative x := q256_out (NormalAccurateLogNegative.normal_q_log_cdf_negative (b64_of_bits x)).

Definition x_q128_mul n1 e1 l1 n2 e2 l2 := q128_out (Q128.mul (q128_in n1 e1 l1) (q128_in n2 e2 l2)).
Definition x_q128_add n1 e1 l1 n2 e2 l2 := q128_out (Q128.add (q128_in n1 e1 l1) (q128_in n2 e2 l2)).
Definition x_q128_to_f64 n e l := bits_of_b64 (Q128.to_f64 (q128_in n e l)).
Definition x_q128_from_f64 bits := q128_out (Q128.from_f64 bits).
Definition x_q256_mul n1 e1 l1 n2 e2 l2 := q256_out (Q256.mul (q256_in n1 e1 l1) (q256_in n2 e2 l2)).
Definition x_q256_add n1 e1 l1 n2 e2 l2 := q256_out (Q256.add (q256_in n1 e1 l1) (q256_in n2 e2 l2)).
Definition x_q256_to_f64 n e l := bits_of_b64 (Q256.to_f64 (q256_in n e l)).
Definition x_q256_from_f64 bits := q256_out (Q256.from_f64 bits).
Definition x_q256_from_limbs n e l := q256_out (Q256.from_limbs n l e).
Definition x_q256_top n e l := Q256Real.top (q256_in n e l).
Definition x_q256_mul_pow2 n e l power := q256_out (Q256Real.mul_pow2 (q256_in n e l) power).

(** The rounding tests (RoundingTest.v), on binary64 encodings. *)
Definition opt_bits (o : option f64) : option Z := match o with Some v => Some (bits_of_b64 v) | None => None end.
Definition x_decide_with hi lo eps := opt_bits (decide_with (b64_of_bits hi) (b64_of_bits lo) (b64_of_bits eps)).
Definition x_decide_scaled hi lo eps k := opt_bits (decide_scaled (b64_of_bits hi) (b64_of_bits lo) (b64_of_bits eps) k).

(** exp's stages: [Stages::of]'s [n], [r1], [j] and [k]; stage A's and stage
    B's values and their tests' outcomes. *)
Definition x_stage x :=
  let xb := b64_of_bits x in
  let '(n, j, k, r1) := ExpStageReduction.stage_of xb in
  let '(ya, la) := ExpStageA.stage_a_value n r1 (Z.to_nat j) in
  let '(yb, lb) := ExpStageB.stage_b_value n r1 (Z.to_nat j) in
  (map bits_of_b64 [n; r1], j, k, map bits_of_b64 [ya; la], opt_bits (ExpStageA.stage_a xb),
   map bits_of_b64 [yb; lb], opt_bits (ExpStageB.stage_b xb)).

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

(** ln's reduction (LnReduction.v): [E], [i], [y], [R[i]], the double-word [z]
    and [z] in Q128. *)
Definition x_ln_reduce x :=
  let '(e, i, y, r) := LnReduction.reduce (b64_of_bits x) in
  let '(zh, zl) := LnReduction.reduce_z y r in
  (e, Z.of_nat i, map bits_of_b64 [y; r; zh; zl], q128_out (LnReduction.z_exact y r)).

(** ln's and ln_1p's accurate values (LnAccurate.v): the 128-bit values their
    accurate paths round. *)
Definition x_ln_accurate x := q128_out (LnAccurate.ln_acc (b64_of_bits x)).
Definition x_ln_1p_accurate x := q128_out (LnAccurate.ln_1p_acc (b64_of_bits x)).

(** ln_1p's stages (Ln1pStageH.v, Ln1pStageB.v): [s], [lo], [eps] and the
    test's result. *)
Definition x_ln1p_h x :=
  let '(s, lo, eps) := Ln1pStageH.stage_h_parts (b64_of_bits x) in
  (map bits_of_b64 [s; lo; eps], opt_bits (Ln1pStageH.stage_h (b64_of_bits x))).
Definition x_ln1p_b x :=
  let '(s, lo, eps) := Ln1pStageB.stage_b_parts (b64_of_bits x) in
  (map bits_of_b64 [s; lo; eps], opt_bits (Ln1pStageB.stage_b (b64_of_bits x))).

(** ln_1p's screens (Ln1pScreen.v): stage H's, then stage B's. *)
Definition x_ln1p_screens x := (Ln1pScreen.h_screen (b64_of_bits x), Ln1pScreen.b_screen (b64_of_bits x)).

(** The full screens, stages, rounding decisions and scaling of exp2/expm1. *)
Definition x_exp2_stages x := opt_bits (Exp2Stages.exp2_stages (b64_of_bits x)).
Definition x_expm1_stages x := opt_bits (Expm1Stages.expm1_stages (b64_of_bits x)).

(** The fallback's own table index/scale and exact residual, followed by
    the Q128 value: no reduction metadata is supplied by the Rust oracle. *)
Definition x_exp2_fallback x :=
 let xb := b64_of_bits x in
 let '(_,j,k,d) := Exp2FallbackReduction.exp2_fallback_reduce xb in
 (j, k, bits_of_b64 d, q128_out (Exp2FallbackAccurate.exp2_fallback_accurate xb)).

Definition x_exp2_fast x :=
 let xb := b64_of_bits x in
 let '(_,j,k,d) := Exp2FallbackReduction.exp2_fallback_reduce xb in
 let '(yh,yl) := Exp2FallbackFast.exp2_fast_value d (Z.to_nat j) in
 (map bits_of_b64 [yh; yl], opt_bits (Exp2FallbackFast.exp2_fallback_fast xb)).
Definition x_exp2_entry x := bits_of_b64 (Exp2.exp2_entry (b64_of_bits x)).

Definition x_expm1_general x :=
 let xb := b64_of_bits x in
 let '(j,k,_,_,_,_,_,_) := Expm1GeneralReduction.em_reduce xb in
 let '(h,l) := Expm1GeneralFast.em_general_fast_value xb in
 let q := Expm1GeneralAccurate.em_general_accurate xb in
 (j, k, map bits_of_b64 [h;l], opt_bits (Expm1GeneralFast.em_general_fast xb),
  q128_out q, bits_of_b64 (Q128.to_f64 q)).

Definition x_expm1_small x :=
 let xb := b64_of_bits x in
 let '(h,l) := Expm1SmallFast.em_small_fast_value xb in
 let q := Expm1SmallAccurate.em_small_accurate xb in
 (map bits_of_b64 [h;l], opt_bits (Expm1SmallFast.em_small_fast xb),
  q128_out q, bits_of_b64 (Q128.to_f64 q)).

Definition x_expm1_entry x := bits_of_b64 (Expm1.expm1_entry (b64_of_bits x)).

Definition x_ln_fast x :=
 let xb := b64_of_bits x in
 let '(h,l) := LnFastValue.lf_ln_fast_value xb in
 (map bits_of_b64 [h;l], opt_bits (LnFastDecision.lf_ln_fast xb)).
Definition x_ln1p_fast x :=
 let xb := b64_of_bits x in
 let '(h,l) := Ln1pFast.lf_ln1p_fast_value xb in
 (map bits_of_b64 [h;l], opt_bits (LnFastDecision.lf_ln1p_fast xb)).
Definition x_ln_entry x := bits_of_b64 (LnEntry.ln_entry (b64_of_bits x)).
Definition x_ln1p_entry x := bits_of_b64 (LnEntry.ln1p_entry (b64_of_bits x)).

Definition x_erfcx_reciprocal x :=
 let '(h,l) := ErfcxReciprocal.reciprocal64 (b64_of_bits x) in
 map bits_of_b64 [h;l].

Definition x_erfcx_reciprocal_square x :=
 let '(h,l) := ErfcxSquare.reciprocal_square64 (b64_of_bits x) in
 map bits_of_b64 [h;l].

Definition x_erfcx_reciprocal_correction x :=
 let '(h,l) := ErfcxMiddlePolynomial.reciprocal_correction64 (b64_of_bits x) in
 map bits_of_b64 [h;l].

Definition x_erfcx_product ah al bh bl :=
 let '(h,l) := ErfcxProduct.product64 (b64_of_bits ah) (b64_of_bits al) (b64_of_bits bh) (b64_of_bits bl) in
 map bits_of_b64 [h;l].

Definition x_erfcx_middle x :=
 let '(h,l) := ErfcxMiddleValue.middle64 (b64_of_bits x) in
 map bits_of_b64 [h;l].

Definition x_erfcx_quotient x :=
 let '(h,l) := ErfcxQuotient.quotient64 (b64_of_bits x) in map bits_of_b64 [h;l].
Definition x_erfcx_scaled_quotient x :=
 let '(h,l) := ErfcxQuotientScale.scaled_quotient64 (b64_of_bits x) in map bits_of_b64 [h;l].

Definition x_erfcx_tail_correction x :=
 [bits_of_b64 (ErfcxTailCorrection.tail_correction64 (b64_of_bits x))].
Definition x_erfcx_tail x :=
 let '(h,l) := ErfcxTailValue.tail64 (b64_of_bits x) in map bits_of_b64 [h;l].

Definition x_erfcx_table_split x e :=
 let '(h,l) := ErfcxTableSplit.table_split64 (b64_of_bits x) e in
 map bits_of_b64 [h;l;IEEE64.fmul h h].

Definition x_erfcx_table_value x :=
 let '(h,l) := ErfcxTableEntry.table_eval64 (b64_of_bits x) in map bits_of_b64 [h;l].

Definition x_erfcx_table_reduce x :=
 let '(i,c,h,e) := ErfcxTableReduction.table_reduce64 (b64_of_bits x) in
 (i,e,map bits_of_b64 [c;h]).

Definition x_erfcx_table_leading i x :=
 let '(a1,b1,a2h,b2,p1,sq,p2) := ErfcxTableProducts.table_leading64 (Z.to_nat i) (b64_of_bits x) in
 map bits_of_b64 [a1;b1;a2h;b2;p1;sq;p2].

Definition x_erfcx_reflection_square x :=
 let '(s,se) := IEEE64Mul.two_prod64 (b64_of_bits x) (b64_of_bits x) in
 map bits_of_b64 [s;se].

Definition x_erfcx_reflection_exp s se :=
 let '(h,l,k) := ErfcxReflectionExp.reflection_exp64 (b64_of_bits s) (b64_of_bits se) in
 (k,map bits_of_b64 [h;l]).

Definition x_erfcx_reflection_value x :=
 let '(h,l,k) := ErfcxReflectionSubtract.reflection_value64 (b64_of_bits x) in
 (k,map bits_of_b64 [h;l]).

Definition x_erfcx_reflection_fast x :=
 match ErfcxReflectionFast.reflection_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.

Require ErfcxTableFast ErfcxAccurateTaylorEntry ErfcxAccurateReflectionEntry ErfcxPublicModel.
Definition x_erfcx_entry x := bits_of_b64 (ErfcxPublicModel.erfcx_entry64 (b64_of_bits x)).
Definition x_erfcx_accurate_negative x := q256_out (ErfcxAccurateReflectionEntry.q_negative (b64_of_bits x)).
Definition x_erfcx_accurate_taylor x := q256_out (ErfcxAccurateTaylorEntry.q_taylor (b64_of_bits x)).

Definition x_erfcx_accurate_exp s se := q256_out (ErfcxAccurateExponential.q_reflection_exponential (b64_of_bits s) (b64_of_bits se)).

Definition x_erfcx_accurate_tail x := q256_out (ErfcxAccurateProduct.q_asym (b64_of_bits x)).

Definition x_erfcx_table_fast x :=
 match ErfcxTableFast.table_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.
Require ErfcxScaledFast.
Definition x_erfcx_tail_scaled_fast x :=
 match ErfcxScaledFast.tail_scaled_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.
Require ErfcxSubnormalFast.
Definition x_erfcx_tail_subnormal_fast x :=
 match ErfcxSubnormalFast.tail_subnormal_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.
Definition x_erfcx_middle_fast x :=
 match ErfcxMiddleFast.middle_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.
Definition x_erfcx_tail_unscaled_fast x :=
 match ErfcxTailFast.tail_unscaled_fast64 (b64_of_bits x) with
 | Some y => Some (bits_of_b64 y) | None => None
 end.

Extraction "internalcrosscheck.ml" x_normal_log_positive x_normal_log_negative x_normal_outer_cdf x_normal_outer_center_positive x_normal_outer_center_negative x_normal_tail_fast x_normal_fast_scaled_argument x_normal_erfcx_fast_scaled x_normal_log_central x_normal_center_central x_normal_cdf_central x_normal_center_fast x_normal_center_shape x_normal_center_tail x_normal_center_small x_normal_density_fast x_normal_accurate_outer_cdf x_normal_accurate_outer_center x_normal_accurate_log_positive x_normal_accurate_log_central x_normal_accurate_log_negative x_normal_log_complement x_normal_logarithm x_normal_erfcx_positive x_normal_accurate_tail x_normal_erfcx_extended_table x_normal_erfcx_small_table x_normal_scaled_argument x_normal_accurate_tail_asym x_normal_erfcx_asym x_normal_accurate_gaussian x_normal_accurate_density x_normal_accurate_center x_normal_accurate_central_cdf x_normal_gaussian x_erfcx_entry x_erfcx_accurate_negative x_erfcx_accurate_taylor x_erfcx_accurate_exp x_erfcx_accurate_tail x_erfcx_table_fast x_erfcx_tail_scaled_fast x_erfcx_tail_subnormal_fast x_erfcx_middle_fast x_erfcx_tail_unscaled_fast x_erfcx_reflection_fast x_erfcx_reflection_value x_erfcx_reflection_square x_erfcx_reflection_exp x_erfcx_table_value x_erfcx_table_reduce x_erfcx_table_leading x_erfcx_table_split x_erfcx_tail x_erfcx_tail_correction x_erfcx_quotient x_erfcx_scaled_quotient x_erfcx_middle x_erfcx_product x_erfcx_reciprocal_correction x_erfcx_reciprocal_square x_erfcx_reciprocal x_ln_fast x_ln1p_fast x_ln_entry x_ln1p_entry x_expm1_entry x_expm1_small x_expm1_general x_exp2_fast x_exp2_entry x_exp2_fallback x_exp2_stages x_expm1_stages x_ln1p_screens x_ln1p_h x_ln1p_b x_ln_accurate x_ln_1p_accurate x_stage x_ln_reduce x_small x_accurate x_fast x_reduce x_decide_with x_decide_scaled x_q128_mul x_q128_add x_q128_to_f64 x_q128_from_f64
  x_q256_mul x_q256_add x_q256_to_f64 x_q256_from_f64 x_q256_from_limbs x_q256_top x_q256_mul_pow2.
