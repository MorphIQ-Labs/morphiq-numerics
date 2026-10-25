(** The high branch for [hk >= 100]: the closed form and the integral on the last scale are both
    tiny there (every exponential is under [e^-50 < 2e-22]), so the kernel's evaluation of the
    closed form is within [161e-18] of the integral over [[0, s]] without Claim K, which is
    the small-[hk] argument of [BvnHighEnd.closed_total]. The classical facts used are the
    positivity and size of the three moments and of the integral, named as hypotheses. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighAlgebra BvnHighCF.
Open Scope R_scope.

(** The exact closed form is [exp(-hk/2) (E0 + c E2 + c d E4)]; with the moments in
    [[0, s^(m+1)/(m+1)]] it is under [1e-24] for [100 <= hk <= 1400]. *)
Lemma closed_x_small (Phi : R -> R) s bs hk E0 E2 E4 :
  1 / 10 ^ 8 <= s <= 3 / 1000 -> 0 <= bs -> 100 <= hk -> hk <= 1400 ->
  E0 = s * exp (- (bs / (s * s)) / 2) - sqrt bs * (sqrt (2 * PI) * Phi (- (sqrt bs / s))) ->
  3 * E2 = s ^ 3 * exp (- (bs / (s * s)) / 2) - (sqrt bs * sqrt bs) * E0 ->
  5 * E4 = s ^ 5 * exp (- (bs / (s * s)) / 2) - (sqrt bs * sqrt bs) * E2 ->
  0 <= E0 <= s -> 0 <= E2 <= s ^ 3 / 3 -> 0 <= E4 <= s ^ 5 / 5 ->
  Rabs (closed_x Phi s bs hk) <= 1 / 10 ^ 24.
Proof.
  intros [Hs0 Hs1] Hbs Hh0 Hh1 H0 H2 H4 [HE00 HE01] [HE20 HE21] [HE40 HE41].
  assert (Hspos : 0 < s) by (assert (0 < 1 / 10 ^ 8) by interval; lra).
  pose proof (moment_closed_form s (sqrt bs) (exp (- (bs / (s * s)) / 2)) (sqrt (2 * PI) * Phi (- (sqrt bs / s)))
    ((4 - hk) / 8) ((12 - hk) / 16) E0 E2 E4 H0 H2 H4) as Hm.
  assert (Hbb : sqrt bs * sqrt bs = bs) by (apply sqrt_sqrt; exact Hbs).
  rewrite Hbb in Hm.
  assert (Hss : s * s <> 0) by (apply Rgt_not_eq; nra).
  assert (Hexpo : exp (- ((bs / (s * s) + hk) / 2)) = exp (- (bs / (s * s)) / 2) * exp (- (hk / 2))).
  { replace (- ((bs / (s * s) + hk) / 2)) with (- (bs / (s * s)) / 2 + - (hk / 2)) by lra. apply exp_plus. }
  assert (Hcx : closed_x Phi s bs hk = exp (- (hk / 2)) * (E0 + (4 - hk) / 8 * E2 + (4 - hk) / 8 * ((12 - hk) / 16) * E4)).
  { unfold closed_x. rewrite Hexpo. rewrite Hm. ring. }
  set (c := (4 - hk) / 8). set (d := (12 - hk) / 16).
  rewrite Hcx.
  assert (HEh : exp (- (hk / 2)) <= 2 / 10 ^ 22).
  { assert (Hx : exp (- (hk / 2)) <= exp (- 50)).
    { destruct (Rle_lt_or_eq_dec 50 (hk / 2) ltac:(lra)) as [Hl|Heq]; [left; apply exp_increasing; lra | right; f_equal; lra]. }
    assert (exp (- 50) <= 2 / 10 ^ 22) by interval. lra. }
  pose proof (exp_pos (- (hk / 2))) as Hpos.
  assert (Hc1 : Rabs c <= 176) by (unfold c; apply Rabs_le; lra).
  assert (Hd1 : Rabs d <= 89) by (unfold d; apply Rabs_le; lra).
  assert (Hs3 : s ^ 3 <= 27 / 10 ^ 9) by (assert (s ^ 3 <= (3 / 1000) ^ 3) by (apply pow_incr; lra); assert ((3 / 1000) ^ 3 = 27 / 10 ^ 9) by field; lra).
  assert (Hs5 : s ^ 5 <= 243 / 10 ^ 15) by (assert (s ^ 5 <= (3 / 1000) ^ 5) by (apply pow_incr; lra); assert ((3 / 1000) ^ 5 = 243 / 10 ^ 15) by field; lra).
  assert (HX : Rabs (E0 + c * E2 + c * d * E4) <= 31 / 10000).
  { assert (Hcm : Rabs (c * E2) <= 176 * (27 / 10 ^ 9 / 3)).
    { rewrite Rabs_mult. rewrite (Rabs_right E2) by lra. apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hc1 | lra]. }
    assert (Hcd : Rabs (c * d * E4) <= 176 * 89 * (243 / 10 ^ 15 / 5)).
    { rewrite !Rabs_mult. rewrite (Rabs_right E4) by lra.
      apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | lra | | lra].
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hc1 | exact Hd1]. }
    assert (Hn1 : Rabs (E0 + c * E2 + c * d * E4) <= Rabs E0 + Rabs (c * E2) + Rabs (c * d * E4)).
    { pose proof (Rabs_triang (E0 + c * E2) (c * d * E4)). pose proof (Rabs_triang E0 (c * E2)). lra. }
    rewrite (Rabs_right E0) in Hn1 by lra.
    assert (176 * (27 / 10 ^ 9 / 3) + 176 * 89 * (243 / 10 ^ 15 / 5) + 3 / 1000 <= 31 / 10000 + 0) by interval.
    lra. }
  rewrite Rabs_mult, (Rabs_right (exp (- (hk / 2)))) by lra.
  assert (Hm2 : exp (- (hk / 2)) * Rabs (E0 + c * E2 + c * d * E4) <= 2 / 10 ^ 22 * (31 / 10000)).
  { apply Rmult_le_compat; [lra | apply Rabs_pos | exact HEh | exact HX]. }
  assert (2 / 10 ^ 22 * (31 / 10000) <= 1 / 10 ^ 24) by interval.
  exact (Rle_trans _ _ _ Hm2 H).
Qed.

(** The kernel's closed form against the integral over [[0, s]], for [100 <= hk < 1400]. *)
Lemma closed_total_big ck Cx I0 :
  Rabs (ck - Cx) <= 1 / 10 ^ 32 -> Rabs Cx <= 1 / 10 ^ 24 -> 0 <= I0 <= 1 / 10 ^ 24 ->
  Rabs (ck - I0) <= 161 / 10 ^ 18.
Proof.
  intros H1 H2 [H3 H4].
  pose proof (Rabs_triang (ck - Cx) Cx) as T. replace (ck - Cx + Cx) with ck in T by ring.
  pose proof (Rabs_triang ck (- I0)) as T2. rewrite Rabs_Ropp in T2.
  replace (ck + - I0) with (ck - I0) in T2 by ring.
  rewrite (Rabs_right I0) in T2 by lra.
  assert (1 / 10 ^ 32 + 1 / 10 ^ 24 + 1 / 10 ^ 24 <= 161 / 10 ^ 18) by interval. lra.
Qed.

(** The same with the remainder correction added. *)
Lemma closed_total_big_rem ck Cx I0 r :
  Rabs (ck - Cx) <= 1 / 10 ^ 32 -> Rabs Cx <= 1 / 10 ^ 24 -> 0 <= I0 <= 1 / 10 ^ 24 ->
  Rabs r <= 2 / 10 ^ 20 ->
  Rabs (rnd (ck + r) - I0) <= 161 / 10 ^ 18.
Proof.
  intros H1 H2 [H3 H4] Hr.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof Hr as Hr'.
  pose proof (Rabs_triang (ck - Cx) Cx) as T1. replace (ck - Cx + Cx) with ck in T1 by ring.
  assert (Hck : Rabs ck <= 2 / 10 ^ 24 + 1 / 10 ^ 32) by (assert (1 / 10 ^ 32 + 1 / 10 ^ 24 = 1 / 10 ^ 32 + 1 / 10 ^ 24) by reflexivity; lra).
  assert (Hck' : Rabs ck <= 1 / 10 ^ 23) by (assert (2 / 10 ^ 24 + 1 / 10 ^ 32 <= 1 / 10 ^ 23) by interval; lra).
  pose proof (Rabs_triang ck r) as T7.
  assert (Hck2 : Rabs (ck + r) <= 3 / 10 ^ 20) by (assert (1 / 10 ^ 23 + 2 / 10 ^ 20 <= 3 / 10 ^ 20) by interval; lra).
  pose proof (rnd_abs (ck + r)) as Hra.
  assert (Hu5 : u * Rabs (ck + r) <= u * (3 / 10 ^ 20)) by (apply Rmult_le_compat_l; lra).
  assert (Hu6 : u * (3 / 10 ^ 20) <= 1 / 10 ^ 30) by (assert (12 / 10 ^ 17 * (3 / 10 ^ 20) <= 1 / 10 ^ 30) by interval; nra).
  assert (Hη2 : eta <= 1 / 10 ^ 290) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 290) by interval; lra).
  pose proof (Rabs_triang (rnd (ck + r) - (ck + r)) (ck + r - I0)) as T4.
  replace (rnd (ck + r) - (ck + r) + (ck + r - I0)) with (rnd (ck + r) - I0) in T4 by ring.
  pose proof (Rabs_triang (ck + r) (- I0)) as T6. rewrite Rabs_Ropp in T6.
  replace (ck + r + - I0) with (ck + r - I0) in T6 by ring.
  rewrite (Rabs_right I0) in T6 by lra.
  assert (Hfin : 3 / 10 ^ 20 + 1 / 10 ^ 24 + 1 / 10 ^ 30 + 1 / 10 ^ 290 <= 161 / 10 ^ 18) by interval.
  lra.
Qed.
