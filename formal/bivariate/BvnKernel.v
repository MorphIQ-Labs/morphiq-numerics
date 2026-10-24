(** The transcription of the bivariate normal's scalar kernel
    (crates/morphiq-numerics/src/bivariate_normal/mod.rs, docs/bivariate_normal.md):
    the regime, the low-correlation table build, the closed forms, the low
    quadrature's double-word sum, and the high-correlation branch with its
    reflection, graded panels, double-word sum and closed form. Each operation
    is the proved IEEE 754 binary64 operation the Rust computes ([fadd],
    [fsub], [fmul], [fdiv], [fsqrt] at round to nearest even, [two_sum64] and
    [two_prod64] of formal/binary64), in the Rust's order and association, with
    the Rust's constants (the tables are formal/bivariate/BvnTables.v).

    The library functions the kernel calls ([exp], [sin], [asin], [norm_cdf])
    are verified elsewhere (docs/exp.md, docs/sin_cos.md, docs/asin.md,
    docs/normal.md) and enter as the fields of [lib], so a theorem about this
    kernel holds for any functions meeting those documents' contracts.
    [sqrt] is the IEEE operation. The kernel is a definition of the Rust
    function's operation sequence: formal/extraction/BvnCrosscheck.v extracts it and
    scripts/check_formal.sh runs it, with the library functions given by the
    results the Rust recorded for each call it made, against the Rust's results on
    the internal cross-check corpus, bit for bit. formal/bivariate/BvnRefineLow.v
    and BvnRefineHigh.v prove its pieces equal the real-valued functions the error
    proofs are written over (docs/bivariate_normal.md section 6.5). *)

From Coq Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt.
Require Import BvnTables.
Import ListNotations.
Open Scope Z_scope.

Definition aw (z : Z) : f64 := b64_of_bits z.

Infix "+f" := fadd (at level 50, left associativity).
Infix "-f" := fsub (at level 50, left associativity).
Infix "*f" := fmul (at level 40, left associativity).
Infix "/f" := fdiv (at level 40, left associativity).

(** The Rust constants, as binary64 encodings. *)
Definition k0 := aw 0x0000000000000000.
Definition k1 := aw 0x3ff0000000000000.
Definition kneg1 := aw 0xbff0000000000000.
Definition k2 := aw 0x4000000000000000.
Definition k3 := aw 0x4008000000000000.
Definition k4 := aw 0x4010000000000000.
Definition k5 := aw 0x4014000000000000.
Definition k8 := aw 0x4020000000000000.
Definition k12 := aw 0x4028000000000000.
Definition k16 := aw 0x4030000000000000.
Definition k20 := aw 0x4034000000000000.
Definition k100 := aw 0x4059000000000000.
Definition kquarter := aw 0x3fd0000000000000.
(** [f64::NAN]. *)
Definition knan := aw 0x7ff8000000000000.
(** [f64::EPSILON]. *)
Definition keps := aw 0x3cb0000000000000.
(** [TAU] and [SQRT_TAU]. *)
Definition ktau := aw 0x401921fb54442d18.
Definition ksqrt_tau := aw 0x40040d931ff62706.
(** [SATURATED_THRESHOLD = 39]. *)
Definition ksaturated := aw 0x4043800000000000.
(** [PRODUCT_EXACT_FLOOR = 1e-270]. *)
Definition kproduct_floor := aw 0x07e0e7c9eebc444a.
(** [GENZ_CORRELATION_SPLIT = 0.925]. *)
Definition ksplit := aw 0x3fed99999999999a.
(** [PANEL_FLOOR = 0.003] and the 16-node threshold [0.095]. *)
Definition kpanel_floor := aw 0x3f689374bc6a7efa.
Definition kpanel_wide := aw 0x3fb851eb851eb852.
(** The unit square of the 15-node rule's centre node, [(3/4)^2]. *)
Definition kcentre_square := aw 0x3fe2000000000000.
(** [HK_CUTOFF = 100]. *)
Definition khk_cutoff := aw 0x4059000000000000.

(** [LOW_RULE_LIMITS]. *)
Definition low_rule_limits : list Z :=
  [0x3fc999999999999a; 0x3fd28f5c28f5c28f; 0x3fe51eb851eb851f; 0x3fe8000000000000;
   0x3fec7ae147ae147b].

(** The comparisons of Rust's [f64] operators: false for a NaN operand. *)
Definition fcmp (x y : f64) : option comparison := Bcompare 53 1024 x y.
Definition flt (x y : f64) : bool := match fcmp x y with Some Lt => true | _ => false end.
Definition fgt (x y : f64) : bool := flt y x.
Definition fle (x y : f64) : bool := match fcmp x y with Some Lt => true | Some Eq => true | _ => false end.
Definition fge (x y : f64) : bool := fle y x.
Definition feq (x y : f64) : bool := match fcmp x y with Some Eq => true | _ => false end.
Definition fisnan (x : f64) : bool := match x with B754_nan _ _ _ => true | _ => false end.
Definition fabs (x : f64) : f64 := b64_abs x.

(** [f64::max] where neither operand is NaN. Rust does not fix the sign of a
    zero result ([max(-0.0, 0.0)]); the one caller whose result a zero reaches
    passes it to [norm_cdf], whose value at [-0] and [+0] is the same
    (docs/normal.md), so the sign cannot change the kernel's result. *)
Definition fmax (x y : f64) : f64 := if flt x y then y else x.

(** [x.max(0.0)]: [0.0] for a NaN or negative [x]. *)
Definition fmax0 (x : f64) : f64 := if fgt x k0 then x else k0.

(** The library functions the kernel calls. *)
Record lib := mk_lib {
  lib_exp : f64 -> f64;
  lib_sin : f64 -> f64;
  lib_asin : f64 -> f64;
  lib_norm_cdf : f64 -> f64
}.

(** Which closed form or quadrature a correlation selects. *)
Inductive regime := Independent | Comonotone | Countermonotone | Low | High.

(** [Regime::of]: [None] for NaN or [|rho| > 1]. *)
Definition regime_of (rho : f64) : option regime :=
  if orb (fisnan rho) (fgt (fabs rho) k1) then None
  else if flt (fabs rho) keps then Some Independent
  else if feq rho k1 then Some Comonotone
  else if feq rho kneg1 then Some Countermonotone
  else if flt (fabs rho) ksplit then Some Low
  else Some High.

(** [probability]'s clamp: [value.clamp(0.0, 1.0)] for a number, NaN as it is. *)
Definition clamp_to_probability (v : f64) : f64 :=
  if fisnan v then v else if flt v k0 then k0 else if fgt v k1 then k1 else v.

(** The rules, in the order of [low_correlation_rule]. *)
Definition low_rules : list (list Z * list Z) :=
  [(gl6_x, gl6_w); (gl8_x, gl8_w); (gl12_x, gl12_w); (gl14_x, gl14_w); (gl20_x, gl20_w);
   (gl24_x, gl24_w)].

(** The index of the first limit [|rho|] is below, or the last rule's. *)
Fixpoint low_rule_index (m : f64) (limits : list Z) : nat :=
  match limits with
  | [] => 0
  | l :: rest => if flt m (aw l) then 0%nat else S (low_rule_index m rest)
  end.

Definition low_correlation_rule (rho : f64) : list Z * list Z :=
  nth (low_rule_index (fabs rho) low_rule_limits) low_rules ([], []).

(** The angle of a node: [asr * (sign * x + 1) / 2]. *)
Definition node_angle (asr sign x : f64) : f64 := asr *f (sign *f x +f k1) /f k2.

(** One node of the table: [(kw, p, q)] of the node's angle's sine [s]. *)
Definition node_entry (L : lib) (asr k w x sign : f64) : f64 * f64 * f64 :=
  let s := lib_sin L (node_angle asr sign x) in
  (w *f k, kquarter /f (k1 -f s), kquarter /f (k1 +f s)).

(** The table's [(kw, p, q)] of each node, in node order: for each stored
    abscissa and weight its positive node then its mirror. *)
Definition low_pairs (L : lib) (asr k : f64) (xw : list (Z * Z)) : list (f64 * f64 * f64) :=
  flat_map (fun p => let x := aw (fst p) in let w := aw (snd p) in
    [node_entry L asr k w x k1; node_entry L asr k w x kneg1]) xw.

Definition low_nodes (L : lib) (asr k : f64) (xs ws : list Z) : list (f64 * f64 * f64) :=
  low_pairs L asr k (combine xs ws).

Record table := mk_table {
  t_rho : f64;
  t_regime : regime;
  (** [asin(rho)], the quadrature's angular range. *)
  t_asr : f64;
  t_nodes : list (f64 * f64 * f64)
}.

(** [BivariateNormal::new]. *)
Definition build_table (L : lib) (rho : f64) : option table :=
  match regime_of rho with
  | None => None
  | Some Low =>
      let asr := lib_asin L rho in
      let '(xs, ws) := low_correlation_rule rho in
      let k := asr /f (k2 *f ktau) in
      Some (mk_table rho Low asr (low_nodes L asr k xs ws))
  | Some r => Some (mk_table rho r k0 [])
  end.

(** [degenerate_limit] for ordered [x <= y]. *)
Definition degenerate_limit (L : lib) (x y : f64) : option f64 :=
  if orb (fisnan x) (fisnan y) then Some knan
  else if fle x (fneg ksaturated) then Some k0
  else if fge y ksaturated then Some (lib_norm_cdf L x)
  else None.

(** One node's term: [kw * exp(-(d p + m q))], [d = (x - y)^2], [m = (x + y)^2]. *)
Definition low_term (L : lib) (d m kw p q : f64) : f64 :=
  kw *f lib_exp L (fneg (d *f p +f m *f q)).

(** The low quadrature's accumulation of the terms, as a double-word: [two_sum]
    per term, the low parts added in order. *)
Fixpoint low_sum (L : lib) (d m : f64) (nodes : list (f64 * f64 * f64)) (high low : f64) : f64 * f64 :=
  match nodes with
  | [] => (high, low)
  | (kw, p, q) :: rest =>
      let '(s, e) := two_sum64 high (low_term L d m kw p q) in
      low_sum L d m rest s (low +f e)
  end.

(** [d = (x - y)^2] and [m = (x + y)^2]. *)
Definition sq_diff (x y : f64) : f64 := let e := x -f y in e *f e.
Definition sq_sum (x y : f64) : f64 := let e := x +f y in e *f e.

(** The low branch's last stage: the product of the two distribution functions
    kept as a double-word (its error word dropped below [PRODUCT_EXACT_FLOOR]),
    its sum with the quadrature's high word, one rounding and the clamp. *)
Definition low_finish (px py high low : f64) : f64 :=
  let '(hi, lo) := two_prod64 px py in
  let lo := if fge hi kproduct_floor then lo else k0 in
  let '(sum, err) := two_sum64 hi high in
  clamp_to_probability (sum +f (err +f (low +f lo))).

(** [BivariateNormal::low] for ordered [x <= y]. *)
Definition kernel_low (L : lib) (t : table) (x y : f64) : f64 :=
  let d := sq_diff x y in
  let m := sq_sum x y in
  let '(high, low) := low_sum L d m (t_nodes t) k0 k0 in
  low_finish (lib_norm_cdf L x) (lib_norm_cdf L y) high low.

(** [PanelRule]: the weights, the unit squares of the abscissas [t] as
    [((3 + t)/4)^2] and [((3 - t)/4)^2], and the centre node's weight. *)
Definition panel_rule_of (wide : bool) : list Z * list Z * list Z * option Z :=
  if wide then (gl16_w, gl16_xp, gl16_xm, None)
  else (gl15_w, gl15_xp, gl15_xm, Some gl15_w0).

(** The rule of the panel of scale [s]: 16 nodes above [0.095], 15 below. *)
Definition panel_rule (s : f64) : list Z * list Z * list Z * option Z :=
  panel_rule_of (fgt s kpanel_wide).

(** [integrand_term]. *)
Definition integrand_term (L : lib) (xs w bs hk : f64) : f64 :=
  let rs := fsqrt (k1 -f xs) in
  let phi := bs /f (k2 *f xs) +f hk /f (k1 +f rs) in
  if flt phi k100 then w *f (lib_exp L (fneg phi) /f rs) else k0.

(** The panel nodes of a scale in order, each as its unit square and weight:
    the pair of each abscissa, then the centre. *)
Definition panel_nodes (rule : list Z * list Z * list Z * option Z) : list (f64 * f64) :=
  let '(w, plus, minus, centre) := rule in
  flat_map (fun pmw => let '(p, m, wi) := pmw in [(aw p, aw wi); (aw m, aw wi)])
    (combine (combine plus minus) w)
  ++ match centre with Some w0 => [(kcentre_square, aw w0)] | None => [] end.

(** One node's term of a panel of half-width [s / 4]: [half_width * integrand_term]
    at the node's unit square [xu] (the panel's [s^2 * xu] is [xs]) and weight [w]. *)
Definition node_value (L : lib) (half_width s2 xu w bs hk : f64) : f64 :=
  half_width *f integrand_term L (s2 *f xu) w bs hk.

(** One node of a panel into the double-word [(high, low)]: [two_sum] of the term
    into the high word, its error added to the low word. *)
Definition panel_step (L : lib) (half_width s2 bs hk : f64) (st : f64 * f64) (xw : f64 * f64) : f64 * f64 :=
  let '(sum, err) := two_sum64 (fst st) (node_value L half_width s2 (fst xw) (snd xw) bs hk) in
  (sum, snd st +f err).

(** The panels: the scale halves while it exceeds [PANEL_FLOOR]; [fuel] bounds the
    loop (the scale starts at most [0.38] and the floor is [0.003], so eight halvings
    end it). The result is the double-word and the last scale. *)
Fixpoint panel_sum (L : lib) (fuel : nat) (s bs hk high low : f64) : f64 * f64 * f64 :=
  match fuel with
  | O => (high, low, s)
  | S fuel' =>
      if fgt s kpanel_floor then
        let half_width := s /f k4 in
        let s2 := s *f s in
        let '(high, low) := fold_left (panel_step L half_width s2 bs hk) (panel_nodes (panel_rule s)) (high, low) in
        panel_sum L fuel' (s /f k2) bs hk high low
      else (high, low, s)
  end.

(** The pieces of Genz's closed form: [c = (4 - hk) / 8], [d = (12 - hk) / 16],
    [w = 1 - d bs / 5], [x = c (bs - ass) w / 3], [1 - x + c d ass^2 / 5] and
    [1 - c bs w / 3]. *)
Definition gen_c (hk : f64) : f64 := (k4 -f hk) /f k8.
Definition gen_d (hk : f64) : f64 := (k12 -f hk) /f k16.
Definition gen_w (d bs : f64) : f64 := k1 -f d *f bs /f k5.
Definition gen_x (c bs ass w : f64) : f64 := c *f (bs -f ass) *f w /f k3.
Definition gen_p1 (c d ass x : f64) : f64 := k1 -f x +f c *f d *f ass *f ass /f k5.
Definition gen_p2 (c bs w : f64) : f64 := k1 -f c *f bs *f w /f k3.

(** Genz's closed form for the integral on the last scale [s <= 0.003], zero
    where [b >= 20 s]. *)
Definition closed_form (L : lib) (s bs hk : f64) : f64 :=
  let b := fsqrt bs in
  if flt b (k20 *f s) then
    let ass := s *f s in
    let c := gen_c hk in
    let d := gen_d hk in
    let w := gen_w d bs in
    let p1 := gen_p1 c d ass (gen_x c bs ass w) in
    let p2 := gen_p2 c bs w in
    let a1 := s *f lib_exp L (fneg (bs /f ass +f hk) /f k2) *f p1 in
    let a2 := lib_exp L (fneg hk /f k2) *f ksqrt_tau *f lib_norm_cdf L (fneg b /f s) *f b *f p2 in
    a1 -f a2
  else k0.

(** The integral [-J] accumulates, before its scaling: [bvn] of [high_correlation]
    after the panels and the closed form. *)
Definition high_integral (L : lib) (hk bs rho : f64) : f64 :=
  if flt hk khk_cutoff then
    let ass := (k1 -f fabs rho) *f (k1 +f fabs rho) in
    let a := fsqrt ass in
    let '(high, low, s) := panel_sum L 64%nat a bs hk k0 k0 in
    let panels := high +f low in
    closed_form L s bs hk +f panels
  else k0.

(** The high branch's last stage: the integral's scaling [-bvn / TAU], the
    normal-distribution terms of the reflection, and the clamp. *)
Definition high_finish (L : lib) (dh dk rho bvn : f64) : f64 :=
  let bvn := fneg bvn /f ktau in
  let result :=
    if fgt rho k0 then bvn +f lib_norm_cdf L (fneg (fmax dh dk))
    else if fgt (fneg dh) dk then
      let g := fneg bvn in
      let '(hi, lo) := two_sum64 (lib_norm_cdf L (fneg dh)) (fneg (lib_norm_cdf L dk)) in
      hi +f (lo +f g)
    else fneg bvn in
  clamp_to_probability result.

(** [high_correlation]: [dh] and [dk] are the negated thresholds. *)
Definition high_correlation (L : lib) (dh dk rho : f64) : f64 :=
  let '(k, hk) := if flt rho k0 then (fneg dk, fneg (dh *f dk)) else (dk, dh *f dk) in
  let bs := (dh -f k) *f (dh -f k) in
  high_finish L dh dk rho (high_integral L hk bs rho).

(** [BivariateNormal::cdf]. *)
Definition cdf (L : lib) (t : table) (x y : f64) : f64 :=
  let '(x, y) := if fle x y then (x, y) else (y, x) in
  match degenerate_limit L x y with
  | Some limit => limit
  | None =>
      match t_regime t with
      | Independent => lib_norm_cdf L x *f lib_norm_cdf L y
      | Comonotone => lib_norm_cdf L x
      | Countermonotone => fmax0 (lib_norm_cdf L x -f lib_norm_cdf L (fneg y))
      | Low => kernel_low L t x y
      | High => high_correlation L (fneg x) (fneg y) (t_rho t)
      end
  end.

(** [bivariate_norm_cdf]. *)
Definition bivariate_norm_cdf (L : lib) (x y rho : f64) : f64 :=
  match build_table L rho with
  | Some t => cdf L t x y
  | None => knan
  end.
