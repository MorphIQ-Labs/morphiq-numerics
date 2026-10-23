(** The constants [TAU] and [SQRT_TAU] of the source and the division of the computed
    integral by [TAU] (docs/bivariate_normal_high.md section 5). *)
From Coq Require Import Reals Lra Psatz ZArith List.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly.
Open Scope R_scope.

(** The two constants of the source, as the rationals their bits denote. *)
Definition TAU : R := 884279719003555 / 140737488355328.
Definition SQRT_TAU : R := 2822212540896131 / 1125899906842624.

Lemma tau_error : Rabs (TAU - 2 * PI) <= 4 / 10 ^ 17 * (2 * PI).
Proof. unfold TAU. interval with (i_prec 90). Qed.

Lemma sqrt_tau_error : Rabs (SQRT_TAU - sqrt (2 * PI)) <= 74 / 10 ^ 18 * sqrt (2 * PI).
Proof. unfold SQRT_TAU. interval with (i_prec 90). Qed.

Lemma tau_bounds : 628 / 100 <= TAU <= 629 / 100.
Proof. unfold TAU. split; interval. Qed.

Lemma c54_value : c54 = 1 / 18014398509481984.
Proof.
  unfold c54.
  assert (H : bpow radix2 54 * bpow radix2 (-54) = 1).
  { rewrite <- bpow_plus. replace (54 + -54)%Z with 0%Z by lia. reflexivity. }
  assert (H2 : bpow radix2 54 = 18014398509481984).
  { cbv [bpow]. cbn. unfold IZR. cbn. lra. }
  rewrite H2 in H. lra.
Qed.

(** Division by [TAU] and its rounding.  [J] is the integral, [Jt] its computed
    value within [dJ]; the result is [g = rnd (-Jt / TAU)] against [-J / (2 pi)]. *)
Theorem division_step Jt J dJ :
  0 <= J <= 21 / 50 -> Rabs (Jt - J) <= dJ -> dJ <= 1 / 1000 ->
  Rabs (rnd (- Jt / TAU) - (- (J / (2 * PI)))) <= 1593 / 10000 * dJ + 1 / 10 ^ 17.
Proof.
  intros HJ Hd HdJ.
  pose proof tau_bounds as [Tl Tu]. pose proof tau_error as Te. pose proof PI_RGT_0 as Hpi.
  pose proof (Rabs_pos (Jt - J)) as Hd0.
  pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  assert (HT : 0 < TAU) by lra.
  set (iT := / TAU).
  assert (HiT : TAU * iT = 1) by (unfold iT; field; lra).
  assert (HiT0 : 0 < iT) by (unfold iT; apply Rinv_0_lt_compat; lra).
  assert (HiT1 : iT <= 1593 / 10000) by nra.
  set (i2 := / (2 * PI)).
  assert (Hi2 : (2 * PI) * i2 = 1) by (unfold i2; field; lra).
  assert (Hi20 : 0 < i2) by (unfold i2; apply Rinv_0_lt_compat; lra).
  assert (Hx : Rabs (- Jt / TAU) < / 8).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_lt. split; nra. }
  pose proof (rnd_err_eighth _ Hx) as Hr.
  assert (Hc : c54 / 8 <= 7 / 10 ^ 18).
  { rewrite c54_value. lra. }
  assert (Hdiv : Rabs (- Jt / TAU - (- (J / (2 * PI)))) <= 1593 / 10000 * dJ + 3 / 10 ^ 18).
  { replace (- Jt / TAU - (- (J / (2 * PI)))) with (- (Jt - J) * iT + J * (TAU - 2 * PI) * (iT * i2)).
    2: { unfold iT, i2. field. split; lra. }
    pose proof (Rabs_triang (- (Jt - J) * iT) (J * (TAU - 2 * PI) * (iT * i2))) as Ht.
    assert (H1 : Rabs (- (Jt - J) * iT) <= 1593 / 10000 * dJ).
    { rewrite Rabs_mult, Rabs_Ropp, (Rabs_right iT) by lra. nra. }
    assert (H2 : Rabs (J * (TAU - 2 * PI) * (iT * i2)) <= 3 / 10 ^ 18).
    { rewrite !Rabs_mult. rewrite (Rabs_right J) by lra. rewrite (Rabs_right iT) by lra. rewrite (Rabs_right i2) by lra.
      assert (Hq : Rabs (TAU - 2 * PI) * i2 <= 4 / 10 ^ 17) by nra.
      assert (Hq0 : 0 <= Rabs (TAU - 2 * PI) * i2) by (apply Rmult_le_pos; [apply Rabs_pos | lra]).
      replace (J * Rabs (TAU - 2 * PI) * (iT * i2)) with (J * iT * (Rabs (TAU - 2 * PI) * i2)) by ring.
      assert (HJiT : J * iT <= 21 / 50 * (1593 / 10000)) by nra.
      assert (0 <= J * iT) by nra.
      nra. }
    lra. }
  pose proof (Rabs_triang (rnd (- Jt / TAU) - (- Jt / TAU)) (- Jt / TAU - (- (J / (2 * PI))))) as Hf.
  replace (rnd (- Jt / TAU) - (- Jt / TAU) + (- Jt / TAU - (- (J / (2 * PI)))))
    with (rnd (- Jt / TAU) - (- (J / (2 * PI)))) in Hf by ring.
  lra.
Qed.

Lemma g_small Jt J dJ :
  0 <= J <= 21 / 50 -> Rabs (Jt - J) <= dJ -> dJ <= 1 / 1000 ->
  Rabs (rnd (- Jt / TAU)) <= 1 / 10.
Proof.
  intros HJ Hd HdJ.
  pose proof tau_bounds as [Tl Tu]. pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  set (iT := / TAU).
  assert (HiT : TAU * iT = 1) by (unfold iT; field; lra).
  assert (HiT0 : 0 < iT) by (unfold iT; apply Rinv_0_lt_compat; lra).
  assert (HiT1 : iT <= 1593 / 10000) by nra.
  assert (Hx : Rabs (- Jt / TAU) < / 8).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_lt. split; nra. }
  pose proof (rnd_err_eighth _ Hx) as Hr.
  assert (Hc : c54 / 8 <= 7 / 10 ^ 18) by (rewrite c54_value; lra).
  assert (Hx2 : Rabs (- Jt / TAU) <= 7 / 100).
  { assert (E : - Jt / TAU = - Jt * iT) by (unfold Rdiv, iT; reflexivity).
    rewrite E. apply Rabs_le. split; nra. }
  pose proof (Rabs_triang (rnd (- Jt / TAU) - (- Jt / TAU)) (- Jt / TAU)) as Ht.
  replace (rnd (- Jt / TAU) - (- Jt / TAU) + (- Jt / TAU)) with (rnd (- Jt / TAU)) in Ht by ring.
  lra.
Qed.
