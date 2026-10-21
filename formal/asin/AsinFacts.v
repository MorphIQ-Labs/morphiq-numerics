(** The analytic facts asin's accurate-path certificates assume
    (docs/asin.md, section 5): the Taylor remainders of sin and cos at the
    Newton step's start, the argument ranges, and sin t / t. *)
From Coq Require Import Reals Lra Psatz Rtrigo_calc.
From Interval Require Import Tactic.
Open Scope R_scope.

Lemma abs_le_inv a b : Rabs a <= b -> -b <= a <= b.
Proof. intros H. unfold Rabs in H. destruct (Rcase_abs a); lra. Qed.

Lemma one_le_half_pi : 1 <= PI / 2.
Proof. interval with (i_prec 60). Qed.

Lemma half_pi_le : PI / 2 <= 1.5708.
Proof. interval with (i_prec 60). Qed.

(** [1 - d^2/2 <= cos d <= 1] for [|d| <= 1]. *)
Lemma cos_taylor d : Rabs d <= 1 -> 1 - d * d / 2 <= cos d <= 1.
Proof.
  intros H. apply abs_le_inv in H.
  pose proof one_le_half_pi as P.
  pose proof (cos_bound d 1 ltac:(lra) ltac:(lra)) as [L _].
  unfold cos_approx, cos_term in L. simpl in L.
  split.
  - assert (Q0 : 0 <= d*d) by nra.
    assert (Q1 : d*d <= 1) by nra.
    assert (0 <= (d*d)*(d*d)*(30 - d*d)) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
    nra.
  - apply COS_bound.
Qed.

(** [d - |d|^3/6 <= sin d <= d] for [0 <= d <= 1]. *)
Lemma sin_taylor_pos d : 0 <= d <= 1 -> d - d * d * d / 6 <= sin d <= d.
Proof.
  intros H.
  pose proof one_le_half_pi as P. pose proof PI_4 as P4.
  pose proof (sin_bound d 0 ltac:(lra) ltac:(lra)) as [L U].
  unfold sin_approx, sin_term in L, U. simpl in L, U.
  assert (Q0 : 0 <= d*d) by nra.
  assert (Q1 : d*d <= 1) by nra.
  assert (0 <= d * (d*d) * (20 - d*d)) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
  split; nra.
Qed.

(** [|sin d - d| <= |d|^3/6] for [|d| <= 1]. *)
Lemma sin_taylor d : Rabs d <= 1 -> Rabs (sin d - d) <= d * d * Rabs d / 6.
Proof.
  intros H. destruct (Rle_lt_dec 0 d) as [Pd | Nd].
  - rewrite (Rabs_pos_eq d Pd) in *.
    pose proof (sin_taylor_pos d ltac:(lra)) as [L U].
    rewrite Rabs_left1 by lra. lra.
  - rewrite (Rabs_left d Nd) in *.
    pose proof (sin_taylor_pos (-d) ltac:(lra)) as [L U].
    rewrite sin_neg in L, U.
    rewrite Rabs_pos_eq by nra. nra.
Qed.

Lemma eps_lower : / 2^61 / 6 <= / 2^60.
Proof. interval with (i_prec 60). Qed.

Lemma eps_upper : 1 / 2 + / 2^61 / 6 <= 0.5000001.
Proof. interval with (i_prec 60). Qed.

Lemma eps_pos : 0 < / 2^61.
Proof. interval with (i_prec 60). Qed.

(** [sin y0] and [cos y0] on [[0, pi/4]], and the bounds shared by both remainders. *)
Lemma step_ranges y0 : 0 <= y0 <= PI / 4 -> 0 <= sin y0 <= 1 /\ 0 <= cos y0 <= 1.
Proof.
  intros Y.
  pose proof (SIN_bound y0) as [_ S1]. pose proof (COS_bound y0) as [_ C1].
  pose proof PI_RGT_0 as P.
  pose proof (sin_ge_0 y0 ltac:(lra) ltac:(lra)) as S0.
  pose proof (cos_ge_0 y0 ltac:(lra) ltac:(lra)) as C0.
  tauto.
Qed.

(** The remainders: with [d] nonzero and [|d| <= 2^-61],
    [rr = (s (1 - cos d) + c (d - sin d))/d^2] lies in [[-2^-60, 0.5000001]]
    for [0 <= s <= 1] and [-1 <= c <= 1]. *)
Lemma remainder_range d s c : 0 <= s <= 1 -> -1 <= c <= 1 -> d <> 0 -> Rabs d <= / 2^61 ->
  let rr := (s * (1 - cos d) + c * (d - sin d)) / (d * d) in
  -/2^60 <= rr <= 0.5000001 /\ rr * (d * d) = s * (1 - cos d) + c * (d - sin d).
Proof.
  intros Hs Hc NZ D rr.
  assert (Ds : Rabs d <= 1) by (apply Rle_trans with (/2^61); [exact D | interval with (i_prec 60)]).
  pose proof (cos_taylor d Ds) as [C1 C2].
  pose proof (sin_taylor d Ds) as S. apply abs_le_inv in S.
  pose proof (Rlt_0_sqr d NZ) as D2. unfold Rsqr in D2.
  pose proof eps_lower. pose proof eps_upper. pose proof eps_pos.
  set (A := d * d) in *. set (a := Rabs d) in *.
  assert (Ha : 0 <= a) by apply Rabs_pos.
  assert (Aa : 0 <= A * a) by nra.
  assert (E : rr * A = s * (1 - cos d) + c * (d - sin d)) by (unfold rr; field; intro Hz; lra).
  assert (Lo : s * (1 - cos d) + c * (d - sin d) >= - (A * a / 6)).
  { assert (0 <= s * (1 - cos d)) by nra.
    assert (0 <= (1 + c) * (A * a / 6 + (d - sin d))) by (apply Rmult_le_pos; lra).
    assert (0 <= (1 - c) * (A * a / 6 - (d - sin d))) by (apply Rmult_le_pos; lra).
    assert (c * (d - sin d) >= - (A * a / 6)) by nra.
    lra. }
  assert (Up : s * (1 - cos d) + c * (d - sin d) <= A * (1 / 2) + A * a / 6).
  { assert (s * (1 - cos d) <= A / 2) by nra.
    assert (0 <= (1 + c) * (A * a / 6 - (d - sin d))) by (apply Rmult_le_pos; lra).
    assert (0 <= (1 - c) * (A * a / 6 + (d - sin d))) by (apply Rmult_le_pos; lra).
    assert (c * (d - sin d) <= A * a / 6) by nra.
    lra. }
  split; [split | exact E].
  - assert (-(a / 6) <= rr) by nra. lra.
  - assert (rr <= 1 / 2 + a / 6) by nra. lra.
Qed.

(** The Taylor remainder of sine at the Newton step's start: with [y0] in
    [[0, pi/4]] and a start error [|d| <= 2^-61],
    [sin (y0 + d) = sin y0 + cos y0 d - rr d^2] with [rr] in the certificate's
    range [[-2^-60, 0.5000001]]. *)
Lemma taylor_sin y0 d : 0 <= y0 <= PI / 4 -> Rabs d <= / 2^61 ->
  exists rr, -/2^60 <= rr <= 0.5000001 /\ sin (y0 + d) = sin y0 + cos y0 * d - rr * (d * d).
Proof.
  intros Y D. destruct (step_ranges y0 Y) as [Hs Hc].
  destruct (Req_dec d 0) as [Z | NZ].
  - exists 0. split; [pose proof eps_pos; interval with (i_prec 60) | ]. subst d. rewrite Rplus_0_r. ring.
  - destruct (remainder_range d (sin y0) (cos y0) Hs ltac:(lra) NZ D) as [R E]. cbv zeta in R, E.
    exists ((sin y0 * (1 - cos d) + cos y0 * (d - sin d)) / (d * d)). split; [exact R | ].
    rewrite sin_plus, E. ring.
Qed.

(** Likewise for cosine: [cos (d0 + d) = cos d0 - sin d0 d - rr d^2]. *)
Lemma taylor_cos d0 d : 0 <= d0 <= PI / 4 -> Rabs d <= / 2^61 ->
  exists rr, -/2^60 <= rr <= 0.5000001 /\ cos (d0 + d) = cos d0 - sin d0 * d - rr * (d * d).
Proof.
  intros Y D. destruct (step_ranges d0 Y) as [Hs Hc].
  destruct (Req_dec d 0) as [Z | NZ].
  - exists 0. split; [pose proof eps_pos; interval with (i_prec 60) | ]. subst d. rewrite Rplus_0_r. ring.
  - destruct (remainder_range d (cos d0) (- sin d0) Hc ltac:(lra) NZ D) as [R E]. cbv zeta in R, E.
    exists ((cos d0 * (1 - cos d) + - sin d0 * (d - sin d)) / (d * d)). split; [exact R | ].
    rewrite cos_plus, E. ring.
Qed.

(** The binary64 numbers either side of [sqrt (1/2)]:
    [SPLIT = 0x1.6a09e667f3bccp-1] and its successor. *)
Definition SPLIT := 6369051672525772 / 9007199254740992.
Definition SPLIT_UP := 6369051672525773 / 9007199254740992.

Lemma quarter_pi_le : PI / 4 <= 0.7854.
Proof. interval with (i_prec 60). Qed.

(** [asin x <= pi/4 - 8e-17] for [x <= SPLIT]: the Newton step's start stays in
    the series' domain [[0, pi/4]]. *)
Lemma sin_split_range Y : 0 <= Y <= PI / 2 -> sin Y <= SPLIT -> Y <= PI / 4 - 8 / 10^17.
Proof.
  intros [Y0 Y1] H.
  destruct (Rle_lt_dec Y (PI / 4 - 8 / 10^17)) as [Le | Gt]; [exact Le | exfalso].
  pose proof PI_RGT_0 as P. pose proof quarter_pi_le as Q.
  assert (Lt : sin (PI / 4 - 8 / 10^17) < sin Y).
  { apply sin_increasing_1; try lra. interval with (i_prec 60). }
  assert (B : SPLIT < sin (PI / 4 - 8 / 10^17)) by (unfold SPLIT; interval with (i_prec 100)).
  lra.
Qed.

(** [acos x <= pi/4 - 6e-17] for [x >= SPLIT_UP], the complement's [delta]. *)
Lemma cos_split_range D : 0 <= D <= PI / 2 -> SPLIT_UP <= cos D -> D <= PI / 4 - 6 / 10^17.
Proof.
  intros [D0 D1] H.
  destruct (Rle_lt_dec D (PI / 4 - 6 / 10^17)) as [Le | Gt]; [exact Le | exfalso].
  pose proof PI_RGT_0 as P. pose proof quarter_pi_le as Q.
  assert (Lt : cos D < cos (PI / 4 - 6 / 10^17)).
  { apply cos_decreasing_1; try lra. interval with (i_prec 60). }
  assert (B : cos (PI / 4 - 6 / 10^17) < SPLIT_UP) by (unfold SPLIT_UP; interval with (i_prec 100)).
  lra.
Qed.

(** [asin x >= 2^-26] once [x >= 2^-26]: [sin Y <= Y]. *)
Lemma y_lower Y : 0 <= Y <= PI / 4 -> / 2^26 <= sin Y -> / 2^26 <= Y.
Proof.
  intros [Y0 Y1] H. pose proof quarter_pi_le as Q.
  pose proof (sin_taylor_pos Y ltac:(lra)) as [_ U]. lra.
Qed.

(** [acos x >= 2^-27] once [x <= 1 - 2^-53]: [1 - D^2/2 <= cos D]. *)
Lemma d_lower D : 0 <= D <= PI / 4 -> cos D <= 1 - / 2^53 -> / 2^27 <= D.
Proof.
  intros [D0 D1] H. pose proof quarter_pi_le as Q.
  assert (Ds : Rabs D <= 1) by (rewrite Rabs_pos_eq by lra; lra).
  pose proof (cos_taylor D Ds) as [L _].
  assert (T : / 2^52 <= D * D) by (assert (/ 2^53 = / 2^52 / 2) by (field); lra).
  destruct (Rle_lt_dec (/ 2^27) D) as [Ok | Bad]; [exact Ok | exfalso].
  assert (D * D < / 2^27 * / 2^27) by nra.
  assert (/ 2^27 * / 2^27 < / 2^52) by (interval with (i_prec 60)).
  lra.
Qed.

(** [sin t / t >= 0.89] on [(0, pi/4]]: [sin t >= t - t^3/6]. *)
Lemma sin_ratio t : 0 < t <= PI / 4 -> 0.89 * t <= sin t.
Proof.
  intros [T0 T1]. pose proof quarter_pi_le as Q.
  pose proof (sin_taylor_pos t ltac:(lra)) as [L _].
  assert (t * t <= 0.62) by nra.
  nra.
Qed.

(** [0.7071 <= cos y0] and [sin y0 <= 0.70711] on [[0, pi/4]]. *)
Lemma quarter_pi_ranges y0 : 0 <= y0 <= PI / 4 -> 0.7071 <= cos y0 /\ sin y0 <= 0.70711.
Proof.
  intros [Y0 Y1]. pose proof PI_RGT_0 as P.
  assert (Cq : 0.7071 <= cos (PI / 4)) by (rewrite cos_PI4; interval with (i_prec 60)).
  assert (Sq : sin (PI / 4) <= 0.70711) by (rewrite sin_PI4; interval with (i_prec 60)).
  destruct (Rle_lt_dec (PI / 4) y0) as [Eq | Lt].
  - assert (y0 = PI / 4) by lra. subst y0. split; assumption.
  - split.
    + pose proof (cos_decreasing_1 y0 (PI / 4) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) Lt). lra.
    + pose proof (sin_increasing_1 y0 (PI / 4) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) Lt). lra.
Qed.
