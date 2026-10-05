(** The vendored multiplicative theorems at binary64's precision (53), round to
    nearest, ties to even, with every premise discharged. Each still describes
    the unbounded-exponent model (FLX); the binary64 domain is in
    docs/double-word.md. Discharging the premises here shows the theorems are
    not vacuous: they apply to every double-word input. *)

From Coq Require Import Reals ZArith Lia.
From Flocq Require Import Core Mult_error.
From Double Require Import DWPlus DWTimesFP DWTimesDW DWDivFP DWDivDW.
From Binary64 Require Import Binary64Add.

Open Scope R_scope.

Notation u := (bpow radix2 (- prec)).

(** An exact product: on binary64 operands, Fast2Mult's two roundings sum to
    the product, since a product's rounding error is representable. *)
Lemma fast2mult_exact a b : fmtX a -> fmtX b ->
  a * b = fst (Fast2Mult prec ne a b) + snd (Fast2Mult prec ne a b).
Proof.
  intros Fa Fb. unfold Fast2Mult; simpl.
  set (r := round radix2 (FLX_exp prec) (Znearest ne) (a * b)).
  assert (Fe : fmtX (a * b - r)).
  { replace (a * b - r) with (- (r - a * b)) by ring.
    apply generic_format_opp, mult_error_FLX; auto with typeclass_instances. }
  rewrite round_generic; auto with typeclass_instances. ring.
Qed.

Lemma ne_sym x : ne x = negb (ne (- (x + 1))).
Proof.
  unfold ne. rewrite Bool.negb_involutive, Z.even_opp, Z.add_1_r, Z.even_succ.
  now rewrite <- Z.negb_even.
Qed.

Theorem mul_f64_bound xh xl y : double_word prec ne xh xl -> fmtX y ->
  let (zh, zl) := DWTimesFP prec ne xh xl y in
  let xy := (xh + xl) * y in
  Rabs ((zh + zl - xy) / xy) <= 3 / 2 * u ^ 2 + 4 * u ^ 3.
Proof.
  intros DWx Fy.
  exact (proj1 (@DWTimesFP_correct prec ne eq_refl (ltac:(unfold prec; lia))
                  fast2mult_exact (TwoProd_Fast2Mult prec ne) xh xl y DWx Fy)).
Qed.

Theorem mul_bound xh xl yh yl :
  double_word prec ne xh xl -> double_word prec ne yh yl ->
  let (zh, zl) := DWTimesDW1 prec ne xh xl yh yl in
  let xy := (xh + xl) * (yh + yl) in
  Rabs ((zh + zl - xy) / xy) < 5 * (u * u).
Proof.
  intros DWx DWy.
  exact (@DWTimesDW1_correct_even prec (ltac:(unfold prec; lia)) ne ne_sym
           (ltac:(unfold prec; lia)) (TwoProd_Fast2Mult prec ne) xh xl yh yl DWx DWy eq_refl).
Qed.

Theorem div_f64_bound xh xl y : double_word prec ne xh xl -> fmtX y -> y <> 0 ->
  let (zh, zl) := DWDivFP3 prec ne xh xl y in
  let xy := (xh + xl) / y in
  Rabs ((zh + zl - xy) / xy) <= 3 * (u * u).
Proof.
  intros DWx Fy Hy.
  exact (@DWDFP3_correct prec (ltac:(unfold prec; lia)) ne eq_refl fast2mult_exact
           (TwoProd_Fast2Mult prec ne) xh xl y DWx Fy (ltac:(unfold prec; lia)) Hy).
Qed.

Theorem div_bound xh xl yh yl :
  double_word prec ne xh xl -> double_word prec ne yh yl -> yh <> 0 ->
  let (zh, zl) := DWDivDW2 prec ne xh xl yh yl in
  let xy := (xh + xl) / (yh + yl) in
  Rabs ((zh + zl - xy) / xy) <= 15 * u ^ 2 + 56 * u ^ 3.
Proof.
  intros DWx DWy Hy.
  exact (@DWDDW_correct prec (ltac:(unfold prec; lia)) ne eq_refl fast2mult_exact
           (TwoProd_Fast2Mult prec ne) xh xl yh yl DWx DWy (ltac:(unfold prec; lia)) Hy).
Qed.
