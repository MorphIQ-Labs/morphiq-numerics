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
    the internal cross-check corpus, bit for bit. *)

From Coq Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt.
Require Import BvnTables.
Import ListNotations.
Open Scope Z_scope.

Definition aw (z : Z) : f64 := b64_of_bits z.

Infix "+." := fadd (at level 50, left associativity).
Infix "-." := fsub (at level 50, left associativity).
Infix "*." := fmul (at level 40, left associativity).
Infix "/." := fdiv (at level 40, left associativity).

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
  [0x3fac28f5c28f5c29; 0x3fc999999999999a; 0x3fd851eb851eb852; 0x3fe147ae147ae148;
   0x3fe51eb851eb851f; 0x3fe8000000000000; 0x3fe9eb851eb851ec; 0x3fec7ae147ae147b].

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
  [(gl4_x, gl4_w); (gl6_x, gl6_w); (gl8_x, gl8_w); (gl10_x, gl10_w); (gl12_x, gl12_w);
   (gl14_x, gl14_w); (gl16_x, gl16_w); (gl20_x, gl20_w); (gl24_x, gl24_w)].

(** The index of the first limit [|rho|] is at or below, or the last rule's. *)
Fixpoint low_rule_index (m : f64) (limits : list Z) : nat :=
  match limits with
  | [] => 0
  | l :: rest => if fle m (aw l) then 0%nat else S (low_rule_index m rest)
  end.

Definition low_correlation_rule (rho : f64) : list Z * list Z :=
  nth (low_rule_index (fabs rho) low_rule_limits) low_rules ([], []).

(** One node of the table: [(kw, p, q)] of the node's angle's sine [s]. *)
Definition node_entry (L : lib) (asr k w x sign : f64) : f64 * f64 * f64 :=
  let s := lib_sin L (asr *. (sign *. x +. k1) /. k2) in
  (w *. k, kquarter /. (k1 -. s), kquarter /. (k1 +. s)).

(** The table's [(kw, p, q)] of each node, in node order: for each abscissa its
    positive node then its mirror. *)
Definition low_nodes (L : lib) (asr k : f64) (xs ws : list Z) : list (f64 * f64 * f64) :=
  flat_map (fun xw => let x := aw (fst xw) in let w := aw (snd xw) in
    [node_entry L asr k w x k1; node_entry L asr k w x kneg1]) (combine xs ws).

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
      let k := asr /. (k2 *. ktau) in
      Some (mk_table rho Low asr (low_nodes L asr k xs ws))
  | Some r => Some (mk_table rho r k0 [])
  end.

(** [degenerate_limit] for ordered [x <= y]. *)
Definition degenerate_limit (L : lib) (x y : f64) : option f64 :=
  if orb (fisnan x) (fisnan y) then Some knan
  else if fle x (fneg ksaturated) then Some k0
  else if fge y ksaturated then Some (lib_norm_cdf L x)
  else None.

(** The low quadrature's accumulation of the terms, as a double-word: [two_sum]
    per term, the low parts added in order. *)
Fixpoint low_sum (L : lib) (d m : f64) (nodes : list (f64 * f64 * f64)) (high low : f64) : f64 * f64 :=
  match nodes with
  | [] => (high, low)
  | (kw, p, q) :: rest =>
      let term := kw *. lib_exp L (fneg (d *. p +. m *. q)) in
      let '(s, e) := two_sum64 high term in
      low_sum L d m rest s (low +. e)
  end.

(** [BivariateNormal::low] for ordered [x <= y]. *)
Definition low_branch (L : lib) (t : table) (x y : f64) : f64 :=
  let e1 := x -. y in
  let d := e1 *. e1 in
  let e2 := x +. y in
  let m := e2 *. e2 in
  let '(high, low) := low_sum L d m (t_nodes t) k0 k0 in
  let '(hi, lo) := two_prod64 (lib_norm_cdf L x) (lib_norm_cdf L y) in
  let lo := if fge hi kproduct_floor then lo else k0 in
  let '(sum, err) := two_sum64 hi high in
  clamp_to_probability (sum +. (err +. (low +. lo))).

(** [PanelRule]: the weights, the unit squares of the abscissas [t] as
    [((3 + t)/4)^2] and [((3 - t)/4)^2], and the centre node's weight. *)
Definition panel_rule (s : f64) : list Z * list Z * list Z * option Z :=
  if fgt s kpanel_wide then (gl16_w, gl16_xp, gl16_xm, None)
  else (gl15_w, gl15_xp, gl15_xm, Some gl15_w0).

(** [integrand_term]. *)
Definition integrand_term (L : lib) (xs w bs hk : f64) : f64 :=
  let rs := fsqrt (k1 -. xs) in
  let phi := bs /. (k2 *. xs) +. hk /. (k1 +. rs) in
  if flt phi k100 then w *. (lib_exp L (fneg phi) /. rs) else k0.

(** The panel nodes of a scale in order, each as its unit square and weight:
    the pair of each abscissa, then the centre. *)
Definition panel_nodes (rule : list Z * list Z * list Z * option Z) : list (f64 * f64) :=
  let '(w, plus, minus, centre) := rule in
  flat_map (fun pmw => let '(p, m, wi) := pmw in [(aw p, aw wi); (aw m, aw wi)])
    (combine (combine plus minus) w)
  ++ match centre with Some w0 => [(kcentre_square, aw w0)] | None => [] end.

(** The panels: [two_sum] per term into the double-word [(high, low)], the scale
    halving while it exceeds [PANEL_FLOOR]; [fuel] bounds the loop (the scale
    starts at most [0.38] and the floor is [0.003], so eight halvings end it).
    The result is the double-word and the last scale. *)
Fixpoint panel_sum (L : lib) (fuel : nat) (s bs hk high low : f64) : f64 * f64 * f64 :=
  match fuel with
  | O => (high, low, s)
  | S fuel' =>
      if fgt s kpanel_floor then
        let half_width := s /. k4 in
        let s2 := s *. s in
        let '(high, low) :=
          fold_left (fun st xw =>
              let term := half_width *. integrand_term L (s2 *. fst xw) (snd xw) bs hk in
              let '(sum, err) := two_sum64 (fst st) term in
              (sum, snd st +. err))
            (panel_nodes (panel_rule s)) (high, low) in
        panel_sum L fuel' (s /. k2) bs hk high low
      else (high, low, s)
  end.

(** Genz's closed form for the integral on the last scale [s <= 0.003], zero
    where [b >= 20 s]. *)
Definition closed_form (L : lib) (s bs hk c d : f64) : f64 :=
  let b := fsqrt bs in
  if flt b (k20 *. s) then
    let ass := s *. s in
    let asr := fneg (bs /. ass +. hk) /. k2 in
    let bvn := s *. lib_exp L asr
               *. (k1 -. c *. (bs -. ass) *. (k1 -. d *. bs /. k5) /. k3 +. c *. d *. ass *. ass /. k5) in
    bvn -. lib_exp L (fneg hk /. k2) *. ksqrt_tau *. lib_norm_cdf L (fneg b /. s) *. b
           *. (k1 -. c *. bs *. (k1 -. d *. bs /. k5) /. k3)
  else k0.

(** The integral [-J] accumulates, before its scaling: [bvn] of [high_correlation]
    after the panels and the closed form. *)
Definition high_integral (L : lib) (dh k hk bs rho : f64) : f64 :=
  if flt hk khk_cutoff then
    let ass := (k1 -. fabs rho) *. (k1 +. fabs rho) in
    let a := fsqrt ass in
    let c := (k4 -. hk) /. k8 in
    let d := (k12 -. hk) /. k16 in
    let '(high, low, s) := panel_sum L 64%nat a bs hk k0 k0 in
    let panels := high +. low in
    closed_form L s bs hk c d +. panels
  else k0.

(** [high_correlation]: [dh] and [dk] are the negated thresholds. *)
Definition high_correlation (L : lib) (dh dk rho : f64) : f64 :=
  let '(k, hk) := if flt rho k0 then (fneg dk, fneg (dh *. dk)) else (dk, dh *. dk) in
  let bs := (dh -. k) *. (dh -. k) in
  let bvn := high_integral L dh k hk bs rho in
  let bvn := fneg bvn /. ktau in
  let result :=
    if fgt rho k0 then bvn +. lib_norm_cdf L (fneg (fmax dh dk))
    else if fgt (fneg dh) dk then
      let g := fneg bvn in
      let '(hi, lo) := two_sum64 (lib_norm_cdf L (fneg dh)) (fneg (lib_norm_cdf L dk)) in
      hi +. (lo +. g)
    else fneg bvn in
  clamp_to_probability result.

(** [BivariateNormal::cdf]. *)
Definition cdf (L : lib) (t : table) (x y : f64) : f64 :=
  let '(x, y) := if fle x y then (x, y) else (y, x) in
  match degenerate_limit L x y with
  | Some limit => limit
  | None =>
      match t_regime t with
      | Independent => lib_norm_cdf L x *. lib_norm_cdf L y
      | Comonotone => lib_norm_cdf L x
      | Countermonotone => fmax0 (lib_norm_cdf L x -. lib_norm_cdf L (fneg y))
      | Low => low_branch L t x y
      | High => high_correlation L (fneg x) (fneg y) (t_rho t)
      end
  end.

(** [bivariate_norm_cdf]. *)
Definition bivariate_norm_cdf (L : lib) (x y rho : f64) : f64 :=
  match build_table L rho with
  | Some t => cdf L t x y
  | None => knan
  end.
