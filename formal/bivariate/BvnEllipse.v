(** Quadrature truncation of the bivariate normal's low-correlation rule
    (docs/bivariate_normal_truncation.md).  Every statement below is about
    real numbers; the passage from them to the Gauss-Legendre remainder is the
    list of cited theorems in the document, none of which is assumed here. *)
From Coq Require Import Reals Lra Psatz.
From Interval Require Import Tactic.
Open Scope R_scope.

(** The exponent of the integrand is [r * g(s)] with [s = sin t],
    [g(s) = (1 - k s) / (2 (1 - s^2))], [r = x^2 + y^2], [k = 2xy/r], [|k| <= 1],
    since [cos^2 t = 1 - sin^2 t].  For [s = X + iY], [1 - s^2 = D = (1 - X^2 + Y^2) - i 2XY]
    and [1 - k s = (1 - k X) - i k Y]; [Re g] is [(Nr Dr + Ni Di) / (2 |D|^2)]. *)
Definition num_re_g (k X Y : R) : R :=
  (1 - k * X) * (1 - X * X + Y * Y) + (- k * Y) * (-2 * X * Y).

Definition den_re_g (X Y : R) : R :=
  (1 - X * X + Y * Y) * (1 - X * X + Y * Y) + (2 * X * Y) * (2 * X * Y).

(** The numerator factors as [(1 - kX)(1 - X^2) + Y^2 (1 + kX)]. *)
Lemma num_re_g_factor k X Y :
  num_re_g k X Y = (1 - k * X) * (1 - X * X) + Y * Y * (1 + k * X).
Proof. unfold num_re_g; ring. Qed.

(** If [|X| <= 1] and [|k| <= 1] the real part of the exponent is nonnegative:
    [|f| = exp(-Re Q) <= 1]. *)
Lemma re_g_nonneg k X Y :
  -1 <= k <= 1 -> -1 <= X <= 1 -> 0 <= num_re_g k X Y.
Proof.
  intros [Hk1 Hk2] [HX1 HX2]. rewrite num_re_g_factor.
  assert (H1 : 0 <= 1 - k * X) by nra.
  assert (H2 : 0 <= 1 - X * X) by nra.
  assert (H3 : 0 <= 1 + k * X) by nra.
  assert (0 <= Y * Y) by nra.
  assert (0 <= (1 - k * X) * (1 - X * X)) by (apply Rmult_le_pos; assumption).
  assert (0 <= Y * Y * (1 + k * X)) by (apply Rmult_le_pos; assumption).
  lra.
Qed.

(** The denominator is positive unless [s = +-1]; it is an exact square sum. *)
Lemma den_re_g_pos X Y :
  -1 < X < 1 -> 0 < den_re_g X Y.
Proof.
  intros [H1 H2]. unfold den_re_g.
  assert (0 < 1 - X * X) by nra.
  assert (0 < (1 - X * X + Y * Y) * (1 - X * X + Y * Y)) by nra.
  nra.
Qed.

(** Bernstein ellipse of the interval [0, A] with parameter [rho]: the point at
    angle [th] is [A * (1/2 + (rho e^{i th} + e^{-i th}/rho)/4)] and has
    [Re = u], [Im = v]. *)
Definition ell_u (A rho th : R) : R := A / 2 + A * (rho + / rho) / 4 * cos th.
Definition ell_v (A rho th : R) : R := A * (rho - / rho) / 4 * sin th.
Definition cosh' (v : R) : R := (exp v + exp (- v)) / 2.

(** [Re sin(u + iv) = sin u cosh v]. *)
Definition re_sin (u v : R) : R := sin u * cosh' v.

Definition ellipse_ok (A rho : R) : Prop :=
  forall th, 0 <= th <= PI -> -1 <= re_sin (ell_u A rho th) (ell_v A rho th) <= 1.

(** The real extent of the ellipse stays inside [(-pi/2, pi/2)]: the filled
    ellipse contains no zero of [cos t]. *)
Definition ellipse_inside (A rho : R) : Prop :=
  A * (rho + 1) * (rho + 1) / (4 * rho) < 15707 / 10000 /\
  A * (rho - 1) * (rho - 1) / (4 * rho) < 15707 / 10000.

(** Gauss-Legendre bound of the unit interval, [64 M / (15 (1 - rho^-2) rho^(2N))]
    with [M = 1], scaled by the half-length [A/2]. *)
Definition trunc_bound (A rho : R) (N : nat) : R :=
  A / 2 * (64 / (15 * ((1 - / (rho * rho)) * rho ^ (2 * N)))).

(** Budget of the truncation term in the integral: [2 pi * 2e-17], from below. *)
Definition budget : R := 12566 / 10 ^ 20.

Lemma budget_le : budget <= 2 * PI * (2 / 10 ^ 17).
Proof. unfold budget. interval. Qed.
