(** The arithmetic of the graded-panel certificate (docs/bivariate_normal_high.md
    section 3.4): panels [[s/2, s]] with [s <= 0.381], each carrying a Gauss-Legendre
    rule whose Bernstein ellipse (parameter [7/2]) stays in the sector
    [|Im z| <= (21/25) Re z], where [|exp(-bs / (2 z^2))| <= 1].  Every statement is
    about real numbers; the complex-analytic steps (the Gauss-Legendre remainder bound
    for analytic integrands, the maximum modulus and Schwarz lemmas, the analyticity
    of the integrand on the filled ellipse) are the cited theorems of the document
    and are not assumed here. *)
From Coq Require Import Reals Lra Psatz.
From Interval Require Import Tactic.
Open Scope R_scope.

(** The Bernstein ellipse of the unit panel [[1/2, 1]] with parameter [7/2]:
    centre [3/4], half-length [1/4], so [u = 3/4 + (53/112) cos th] and
    [v = (45/112) sin th]. *)
Definition pu (th : R) : R := 3 / 4 + 53 / 112 * cos th.
Definition pv (th : R) : R := 45 / 112 * sin th.

(** The whole ellipse lies right of the origin and inside the sector of slope
    [21/25] (about 40 degrees): there [Re z^-2 > 0], so [exp(-bs/(2 z^2))] is
    bounded by one on it, whatever [bs >= 0]. *)
Lemma panel_sector th :
  0 <= th <= PI -> 0 < pu th /\ Rabs (pv th) <= 21 / 25 * pu th.
Proof.
  intros Hth. unfold pu, pv.
  assert (Hs : 0 <= sin th) by (apply sin_ge_0; lra).
  split.
  - interval with (i_bisect th, i_depth 10).
  - rewrite Rabs_right by lra.
    assert (0 <= 21 / 25 * (3 / 4 + 53 / 112 * cos th) - 45 / 112 * sin th) by (interval with (i_bisect th, i_depth 16)).
    lra.
Qed.

(** Its largest modulus is at the real end, [137/112 < 123/100]. *)
Lemma panel_modulus th :
  0 <= th <= PI -> pu th * pu th + pv th * pv th <= (123 / 100) * (123 / 100).
Proof.
  intros Hth. unfold pu, pv.
  assert (0 <= (123 / 100) * (123 / 100) - ((3 / 4 + 53 / 112 * cos th) * (3 / 4 + 53 / 112 * cos th) + 45 / 112 * sin th * (45 / 112 * sin th))) by (interval with (i_bisect th, i_depth 16)).
  lra.
Qed.

(** In the sector, [Re z^-2 = (x^2 - y^2) / (x^2 + y^2)^2] is at least [1/2]
    once [|z|^2 <= 22/100], which holds on every panel ellipse
    ([(381/1000)(123/100) = 0.4686], squared [0.2196]). *)
Lemma sector_decay x y :
  0 < x -> Rabs y <= 21 / 25 * x -> x * x + y * y <= 22 / 100 ->
  (x * x - y * y) / ((x * x + y * y) * (x * x + y * y)) >= 1 / 2.
Proof.
  intros Hx Hy Hz.
  assert (Hy2 : y * y <= (21 / 25) * (21 / 25) * (x * x)).
  { pose proof (Rabs_pos y). pose proof (Rabs_def2 y) as _. 
    assert (Rabs y * Rabs y <= (21 / 25 * x) * (21 / 25 * x)) by (apply Rmult_le_compat; lra).
    rewrite <- (Rabs_mult y y) in H0. rewrite Rabs_right in H0 by (apply Rle_ge; nra). nra. }
  assert (HS : 0 < x * x + y * y) by nra.
  assert (H1 : (x * x - y * y) >= 1726 / 10000 * (x * x + y * y)) by nra.
  assert (HS2 : (x * x + y * y) * (x * x + y * y) <> 0) by nra.
  assert (E : (x * x - y * y) / ((x * x + y * y) * (x * x + y * y)) - 1 / 2
    = (2 * (x * x - y * y) - (x * x + y * y) * (x * x + y * y)) / (2 * ((x * x + y * y) * (x * x + y * y)))).
  { assert (HS1 : x * x + y * y <> 0) by lra. field. exact HS1. }
  assert (0 <= (2 * (x * x - y * y) - (x * x + y * y) * (x * x + y * y)) / (2 * ((x * x + y * y) * (x * x + y * y)))).
  { unfold Rdiv. apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; nra]. }
  lra.
Qed.

(** The exponent's growth is cancelled: with [bs >= 4 t] ([t = |hk|] when
    [hk < 0]) and [Re z^-2 >= 1/2], [exp(-(bs/2) Re z^-2) exp(t) <= 1]. *)
Lemma decay_cancel bs t q :
  0 <= t -> 4 * t <= bs -> 1 / 2 <= q -> exp (- (bs / 2) * q) * exp t <= 1.
Proof.
  intros Ht Hbs Hq. rewrite <- exp_plus.
  assert (H : - (bs / 2) * q + t <= 0) by nra.
  destruct (Rle_lt_or_eq_dec _ _ H) as [Hl|He].
  - left. rewrite <- exp_0. apply exp_increasing. exact Hl.
  - rewrite He. rewrite exp_0. lra.
Qed.

(** The constants of the Schwarz-lemma bound [|exp(-bs/(2 z^2)) V(z)| <= kappa |z|^6]
    (document section 3.4): on [|u| = 9/10], [|1/rs| <= 1 / sqrt(1/10) <= 317/100],
    and, with [t = |hk| <= 1521], [f(t) = exp(-t/2) (1 + (4+t)/8 (9/10) (1 + (12+t)/16
    (9/10)))] is at most [18/10]. *)
Lemma inv_sqrt_tenth : 1 / sqrt (1 / 10) <= 317 / 100.
Proof. interval. Qed.

Definition fpoly (t : R) : R :=
  exp (- t / 2) * (1 + (4 + t) / 8 * (9 / 10) * (1 + (12 + t) / 16 * (9 / 10))).

Lemma fpoly_bound t : 0 <= t <= 1521 -> fpoly t <= 18 / 10.
Proof.
  intros Ht. unfold fpoly. interval with (i_bisect t, i_depth 16).
Qed.

Lemma kappa_arith : (317 / 100 + 18 / 10) / ((9 / 10) * (9 / 10) * (9 / 10)) <= 72 / 10.
Proof. interval. Qed.

(** The panel constants.  The Gauss-Legendre remainder of a panel of half-length [l = s/4]
    with [N] nodes and an integrand bounded by [M] on the ellipse of parameter [rho = 7/2] is
    [l 64 M / (15 (1 - rho^-2) rho^(2 N))]; [M = 1/sqrt(1 - 22/100) <= 1.134] bounds
    [|1 / rs|] there.  With [N >= 15] the remainder is at most [63e-18 s]. *)
Lemma modulus_constant : 1 / sqrt (1 - 22 / 100) <= 1134 / 1000.
Proof. interval. Qed.

Lemma panel_constant_15 :
  1 / 4 * (64 / (15 * ((1 - / ((7 / 2) * (7 / 2))) * (7 / 2) ^ (2 * 15)))) * (1134 / 1000) <= 63 / 10 ^ 18.
Proof. interval with (i_prec 80). Qed.

Lemma panel_constant_16 :
  1 / 4 * (64 / (15 * ((1 - / ((7 / 2) * (7 / 2))) * (7 / 2) ^ (2 * 16)))) * (1134 / 1000) <= 63 / 10 ^ 18.
Proof. interval with (i_prec 80). Qed.

(** The tail below the last scale: [kappa s^7 / 7] with [kappa = 7.2], [s <= 0.003]. *)
Lemma tail_constant : 72 / 10 * (3 / 1000) ^ 7 / 7 <= 23 / 10 ^ 19.
Proof. interval. Qed.

Lemma tail_monotone s : 0 <= s -> s <= 3 / 1000 -> 72 / 10 * s ^ 7 / 7 <= 72 / 10 * (3 / 1000) ^ 7 / 7.
Proof.
  intros H0 H1. assert (s ^ 7 <= (3 / 1000) ^ 7) by (apply pow_incr; lra).
  unfold Rdiv. assert (0 <= / 7) by (left; apply Rinv_0_lt_compat; lra). nra.
Qed.

(** The certificate: the sector and modulus facts for the ellipse, the decay and
    constants, and the panel constants. *)
Definition panel_design_certified : Prop :=
  (forall th, 0 <= th <= PI -> 0 < pu th /\ Rabs (pv th) <= 21 / 25 * pu th) /\
  (forall th, 0 <= th <= PI -> pu th * pu th + pv th * pv th <= (123 / 100) * (123 / 100)) /\
  (forall x y, 0 < x -> Rabs y <= 21 / 25 * x -> x * x + y * y <= 22 / 100 ->
     (x * x - y * y) / ((x * x + y * y) * (x * x + y * y)) >= 1 / 2) /\
  (forall bs t q, 0 <= t -> 4 * t <= bs -> 1 / 2 <= q -> exp (- (bs / 2) * q) * exp t <= 1) /\
  (forall t, 0 <= t <= 1521 -> fpoly t <= 18 / 10) /\
  (1 / sqrt (1 / 10) <= 317 / 100) /\
  ((317 / 100 + 18 / 10) / ((9 / 10) * (9 / 10) * (9 / 10)) <= 72 / 10) /\
  (381 / 1000 * (123 / 100) * (381 / 1000 * (123 / 100)) <= 22 / 100) /\
  (1 / sqrt (1 - 22 / 100) <= 1134 / 1000) /\
  (1 / 4 * (64 / (15 * ((1 - / ((7 / 2) * (7 / 2))) * (7 / 2) ^ (2 * 15)))) * (1134 / 1000) <= 63 / 10 ^ 18) /\
  (1 / 4 * (64 / (15 * ((1 - / ((7 / 2) * (7 / 2))) * (7 / 2) ^ (2 * 16)))) * (1134 / 1000) <= 63 / 10 ^ 18) /\
  (72 / 10 * (3 / 1000) ^ 7 / 7 <= 23 / 10 ^ 19).

Theorem panel_design : panel_design_certified.
Proof.
  refine (conj panel_sector _). refine (conj panel_modulus _). refine (conj sector_decay _).
  refine (conj decay_cancel _). refine (conj fpoly_bound _). refine (conj inv_sqrt_tenth _).
  refine (conj kappa_arith _). refine (conj _ _); [interval|].
  refine (conj modulus_constant _). refine (conj panel_constant_15 _).
  refine (conj panel_constant_16 _). exact tail_constant.
Qed.
