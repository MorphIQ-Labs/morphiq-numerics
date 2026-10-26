From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps.
Open Scope R_scope.

(** [x'] approximates [x]: [|x| <= m] and [|x' - x| <= e]. *)
Definition ab (x x' m e : R) : Prop := Rabs x <= m /\ Rabs (x' - x) <= e.

Lemma ab_mono x x' m e m' e' : ab x x' m e -> m <= m' -> e <= e' -> ab x x' m' e'.
Proof. unfold ab. intros [H1 H2] Hm He. split; lra. Qed.

Lemma ab_exact x : ab x x (Rabs x) 0.
Proof. unfold ab. split; [lra|]. replace (x - x) with 0 by ring. rewrite Rabs_R0. lra. Qed.

Lemma ab_add x x' y y' m1 e1 m2 e2 : ab x x' m1 e1 -> ab y y' m2 e2 ->
  ab (x + y) (rnd (x' + y')) (m1 + m2) (e1 + e2 + u * (m1 + e1 + (m2 + e2)) + eta).
Proof.
  unfold ab. intros [Hx1 Hx2] [Hy1 Hy2]. pose proof (rnd_abs (x' + y')) as Hr. pose proof u_pos as Hu.
  assert (Hx' : Rabs x' <= m1 + e1).
  { pose proof (Rabs_triang (x' - x) x). replace (x' - x + x) with x' in H by ring. lra. }
  assert (Hy' : Rabs y' <= m2 + e2).
  { pose proof (Rabs_triang (y' - y) y). replace (y' - y + y) with y' in H by ring. lra. }
  pose proof (Rabs_triang x' y') as Hs. pose proof (Rabs_triang x y) as Hs2.
  pose proof (Rabs_triang (x' - x) (y' - y)) as Hs3.
  pose proof (Rabs_triang (rnd (x' + y') - (x' + y')) (x' + y' - (x + y))) as Ht.
  replace (rnd (x' + y') - (x' + y') + (x' + y' - (x + y))) with (rnd (x' + y') - (x + y)) in Ht by ring.
  replace (x' + y' - (x + y)) with ((x' - x) + (y' - y)) in Ht by ring.
  assert (u * Rabs (x' + y') <= u * (m1 + e1 + (m2 + e2))) by (apply Rmult_le_compat_l; [lra | lra]).
  split; lra.
Qed.

Lemma abs_sub_le a b : Rabs (a - b) <= Rabs a + Rabs b.
Proof. pose proof (Rabs_triang a (- b)) as H. rewrite Rabs_Ropp in H. unfold Rminus. exact H. Qed.

Lemma ab_sub x x' y y' m1 e1 m2 e2 : ab x x' m1 e1 -> ab y y' m2 e2 ->
  ab (x - y) (rnd (x' - y')) (m1 + m2) (e1 + e2 + u * (m1 + e1 + (m2 + e2)) + eta).
Proof.
  unfold ab. intros [Hx1 Hx2] [Hy1 Hy2]. pose proof (rnd_abs (x' - y')) as Hr. pose proof u_pos as Hu.
  assert (Hx' : Rabs x' <= m1 + e1).
  { pose proof (Rabs_triang (x' - x) x). replace (x' - x + x) with x' in H by ring. lra. }
  assert (Hy' : Rabs y' <= m2 + e2).
  { pose proof (Rabs_triang (y' - y) y). replace (y' - y + y) with y' in H by ring. lra. }
  pose proof (abs_sub_le x' y') as Hs. pose proof (abs_sub_le x y) as Hs2.
  assert (Hs3 : Rabs (x' - y' - (x - y)) <= e1 + e2).
  { replace (x' - y' - (x - y)) with ((x' - x) - (y' - y)) by ring.
    pose proof (abs_sub_le (x' - x) (y' - y)). lra. }
  pose proof (Rabs_triang (rnd (x' - y') - (x' - y')) (x' - y' - (x - y))) as Ht.
  replace (rnd (x' - y') - (x' - y') + (x' - y' - (x - y))) with (rnd (x' - y') - (x - y)) in Ht by ring.
  assert (u * Rabs (x' - y') <= u * (m1 + e1 + (m2 + e2))) by (apply Rmult_le_compat_l; [lra | lra]).
  split; [lra|]. lra.
Qed.

Lemma ab_mul x x' y y' m1 e1 m2 e2 : ab x x' m1 e1 -> ab y y' m2 e2 ->
  ab (x * y) (rnd (x' * y')) (m1 * m2) (m1 * e2 + m2 * e1 + e1 * e2 + u * ((m1 + e1) * (m2 + e2)) + eta).
Proof.
  unfold ab. intros [Hx1 Hx2] [Hy1 Hy2]. pose proof (rnd_abs (x' * y')) as Hr. pose proof u_pos as Hu.
  pose proof (Rabs_pos x). pose proof (Rabs_pos y). pose proof (Rabs_pos (x' - x)). pose proof (Rabs_pos (y' - y)).
  assert (Hx' : Rabs x' <= m1 + e1).
  { pose proof (Rabs_triang (x' - x) x). replace (x' - x + x) with x' in H3 by ring. lra. }
  assert (Hy' : Rabs y' <= m2 + e2).
  { pose proof (Rabs_triang (y' - y) y). replace (y' - y + y) with y' in H3 by ring. lra. }
  assert (Hxy : Rabs (x * y) <= m1 * m2) by (rewrite Rabs_mult; apply Rmult_le_compat; lra).
  assert (Hd : Rabs (x' * y' - x * y) <= m1 * e2 + m2 * e1 + e1 * e2).
  { replace (x' * y' - x * y) with (x * (y' - y) + y * (x' - x) + (x' - x) * (y' - y)) by ring.
    pose proof (Rabs_triang (x * (y' - y) + y * (x' - x)) ((x' - x) * (y' - y))) as T1.
    pose proof (Rabs_triang (x * (y' - y)) (y * (x' - x))) as T2.
    rewrite (Rabs_mult (x' - x) (y' - y)) in T1.
    rewrite (Rabs_mult x (y' - y)), (Rabs_mult y (x' - x)) in T2.
    assert (Rabs x * Rabs (y' - y) <= m1 * e2) by (apply Rmult_le_compat; lra).
    assert (Rabs y * Rabs (x' - x) <= m2 * e1) by (apply Rmult_le_compat; lra).
    assert (Rabs (x' - x) * Rabs (y' - y) <= e1 * e2) by (apply Rmult_le_compat; lra).
    lra. }
  pose proof (Rabs_pos x') as Hx'0. pose proof (Rabs_pos y') as Hy'0.
  assert (Hp : Rabs (x' * y') <= (m1 + e1) * (m2 + e2)) by (rewrite Rabs_mult; apply Rmult_le_compat; lra).
  pose proof (Rabs_triang (rnd (x' * y') - x' * y') (x' * y' - x * y)) as Ht.
  replace (rnd (x' * y') - x' * y' + (x' * y' - x * y)) with (rnd (x' * y') - x * y) in Ht by ring.
  assert (u * Rabs (x' * y') <= u * ((m1 + e1) * (m2 + e2))) by (apply Rmult_le_compat_l; lra).
  split; lra.
Qed.

Lemma ab_divc x x' c m e : 0 < c -> ab x x' m e ->
  ab (x / c) (rnd (x' / c)) (m / c) (e / c + u * ((m + e) / c) + eta).
Proof.
  unfold ab. intros Hc [H1 H2]. pose proof (rnd_abs (x' / c)) as Hr. pose proof u_pos as Hu.
  assert (Hi : 0 < / c) by (apply Rinv_0_lt_compat; lra).
  assert (Hx' : Rabs x' <= m + e).
  { pose proof (Rabs_triang (x' - x) x). replace (x' - x + x) with x' in H by ring. lra. }
  assert (A : Rabs (x / c) <= m / c).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_right c) by lra. apply Rmult_le_compat_r; lra. }
  assert (B : Rabs (x' / c - x / c) <= e / c).
  { replace (x' / c - x / c) with ((x' - x) / c) by (field; lra).
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_right c) by lra. apply Rmult_le_compat_r; lra. }
  assert (C : Rabs (x' / c) <= (m + e) / c).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_right c) by lra. apply Rmult_le_compat_r; lra. }
  pose proof (Rabs_triang (rnd (x' / c) - x' / c) (x' / c - x / c)) as Ht.
  replace (rnd (x' / c) - x' / c + (x' / c - x / c)) with (rnd (x' / c) - x / c) in Ht by ring.
  assert (u * Rabs (x' / c) <= u * ((m + e) / c)) by (apply Rmult_le_compat_l; lra).
  split; lra.
Qed.
