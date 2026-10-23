(** The exact decomposition evaluated by the high-correlation branch
    (docs/bivariate_normal_high.md section 1), as algebra over the reals.

    Every statement is a field identity.  The calculus it rests on -- Plackett's
    identity, the change of variable [x^2 = 1 - r^2], and the three moment
    integrals [int_0^a e^(-b^2/(2x^2)) x^m dx] -- is the paper step of the
    document; the moments enter here only as the recurrences integration by
    parts gives, stated as hypotheses of [moment_closed_form]. *)
From Coq Require Import Reals Lra Field.
Open Scope R_scope.

(** The exponent split.  With [x^2 = 1 - s^2] (so [s] is the correlation of the
    substituted variable), the exponent of Plackett's integrand splits into the
    part that narrows the integrand and the part that is smooth:
    [(h^2 + k^2 - 2 h k s) / (2 (1 - s^2)) = (h - k)^2 / (2 x^2) + h k / (1 + s)]. *)
Lemma plackett_exponent h k s x :
  1 + s <> 0 -> x * x = 1 - s * s -> x <> 0 ->
  (h * h + k * k - 2 * h * k * s) / (2 * (1 - s * s))
  = (h - k) * (h - k) / (2 * (x * x)) + h * k / (1 + s).
Proof.
  intros Hs Hx Hx0. rewrite <- Hx.
  assert (Hxx : x * x <> 0) by (apply Rmult_integral_contrapositive_currified; assumption).
  rewrite Hx in Hxx |- *.
  assert (H1s : 1 - s <> 0).
  { intro H. apply Hxx. nra. }
  field. split; assumption.
Qed.

(** The closed form: the analytic part.  [E0, E2, E4] stand for the moments
    [int_0^a e^(-bs/(2 x^2)) x^m dx], [m = 0, 2, 4], with [bs = b^2];
    [R = sqrt(2 pi) Phi(-b / a)] and [ea = e^(-bs/(2 a^2))].  The base moment is
    [E0 = a ea - b R]; integration by parts gives
    [3 E2 = a^3 ea - bs E0] and [5 E4 = a^5 ea - bs E2].  The code's two
    closed-form terms, [a ea (1 - c (bs - a^2) (1 - d bs / 5) / 3 + c d a^4 / 5)]
    and [b R (1 - c bs (1 - d bs / 5) / 3)], are [E0 + c E2 + c d E4]. *)
Theorem moment_closed_form a b ea R c d E0 E2 E4 :
  E0 = a * ea - b * R ->
  3 * E2 = a ^ 3 * ea - (b * b) * E0 ->
  5 * E4 = a ^ 5 * ea - (b * b) * E2 ->
  E0 + c * E2 + c * d * E4
  = a * ea * (1 - c * ((b * b) - a * a) * (1 - d * (b * b) / 5) / 3 + c * d * (a * a) * (a * a) / 5)
    - b * R * (1 - c * (b * b) * (1 - d * (b * b) / 5) / 3).
Proof.
  intros H0 H2 H4.
  assert (HE2 : E2 = (a ^ 3 * ea - (b * b) * E0) / 3) by lra.
  assert (HE4 : E4 = (a ^ 5 * ea - (b * b) * E2) / 5) by lra.
  rewrite HE4, HE2, H0. field.
Qed.

(** The reflection used for negative correlation.  With
    [P+ = Phi(-max(h, k')) - J'/(2 pi)] for the reflected pair,
    [P(h, k; -r) = Phi(-h) - P+(h, -k; r)]: the three Phi terms combine as
    [Phi(-h) - Phi(-max(h, -k)) = max(0, Phi(-h) - Phi(k))] when
    [Phi(-max(h, -k)) = min(Phi(-h), Phi(k))]. *)
Lemma reflection_phi_terms ph pk :
  ph - Rmin ph pk = Rmax 0 (ph - pk).
Proof.
  unfold Rmin, Rmax. destruct (Rle_dec ph pk), (Rle_dec 0 (ph - pk)); lra.
Qed.
