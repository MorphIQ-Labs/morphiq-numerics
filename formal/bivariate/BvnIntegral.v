(** The Plackett integral of the low-correlation branch,
    [Iint r p a = int_0^a exp(-Q(sin t)) dt], and its Lipschitz bound: the
    integrand lies in [(0, 1]] on [|t| <= 3/2]. *)
From Coq Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnArg BvnNode BvnTrig.
Open Scope R_scope.

Definition fint (r p : R) (t : R) : R := exp (- Qf r p (sin t)).

Definition Iint (r p a : R) : R := RInt (fint r p) 0 a.

Lemma fint_le_1 r p t : 0 <= r -> Rabs p <= r / 2 -> Rabs t <= 3 / 2 -> 0 < fint r p t <= 1.
Proof.
  intros Hr Hp Ht. unfold fint. split; [apply exp_pos |].
  pose proof (Qf_nonneg r p (sin t) Hr Hp (sin_abs_lt_1 t Ht)) as HQ.
  rewrite <- exp_0. apply exp_mono. lra.
Qed.

Lemma fint_cont r p t : Rabs (sin t) < 1 -> continuous (fint r p) t.
Proof.
  intros Hs.
  assert (Hd : 1 - sin t * sin t <> 0).
  { apply Rabs_lt_between in Hs. destruct Hs as [H1 H2]. nra. }
  apply (ex_derive_continuous (fint r p) t). unfold fint, Qf.
  auto_derive.
  exact Hd.
Qed.

Lemma fint_ex_RInt r p a b : Rabs a <= 3 / 2 -> Rabs b <= 3 / 2 -> ex_RInt (fint r p) a b.
Proof.
  intros Ha Hb. apply (ex_RInt_continuous (V := R_CompleteNormedModule)). intros z Hz.
  apply fint_cont. apply sin_abs_lt_1.
  apply Rabs_le_between in Ha. apply Rabs_le_between in Hb.
  destruct Hz as [Hz1 Hz2].
  assert (Hmin : Rmin a b <= a) by apply Rmin_l.
  assert (Hmax : b <= Rmax a b) by apply Rmax_r.
  assert (Hmin' : Rmin a b >= - (3 / 2)).
  { unfold Rmin. destruct (Rle_dec a b); lra. }
  assert (Hmax' : Rmax a b <= 3 / 2).
  { unfold Rmax. destruct (Rle_dec a b); lra. }
  apply Rabs_le_between. lra.
Qed.

Lemma RInt_ordered r p u v : 0 <= r -> Rabs p <= r / 2 -> Rabs u <= 3 / 2 -> Rabs v <= 3 / 2 -> u <= v ->
  Rabs (RInt (fint r p) u v) <= v - u.
Proof.
  intros Hr Hp Hu Hv Huv.
  pose proof (RInt_correct (V := R_CompleteNormedModule) (fint r p) u v (fint_ex_RInt r p u v Hu Hv)) as Hc.
  pose proof (norm_RInt_le_const (fint r p) u v _ 1 Huv ltac:(
    intros t [Ht1 Ht2]; change (norm (fint r p t)) with (Rabs (fint r p t));
    assert (Rabs t <= 3 / 2) by (apply Rabs_le_between in Hu; apply Rabs_le_between in Hv; apply Rabs_le_between; lra);
    destruct (fint_le_1 r p t Hr Hp H) as [H1 H2]; rewrite Rabs_pos_eq by lra; lra) Hc) as Hn.
  change (norm (RInt (fint r p) u v)) with (Rabs (RInt (fint r p) u v)) in Hn. lra.
Qed.

Lemma Iint_lip r p a b : 0 <= r -> Rabs p <= r / 2 -> Rabs a <= 3 / 2 -> Rabs b <= 3 / 2 ->
  Rabs (Iint r p a - Iint r p b) <= Rabs (a - b).
Proof.
  intros Hr Hp Ha Hb. unfold Iint.
  assert (H0a : Rabs 0 <= 3 / 2) by (rewrite Rabs_R0; lra).
  assert (E : RInt (fint r p) 0 a - RInt (fint r p) 0 b = RInt (fint r p) b a).
  { assert (Hc : RInt (fint r p) 0 b + RInt (fint r p) b a = RInt (fint r p) 0 a).
    { exact (RInt_Chasles (V := R_CompleteNormedModule) (fint r p) 0 b a (fint_ex_RInt r p 0 b H0a Hb) (fint_ex_RInt r p b a Hb Ha)). }
    lra. }
  rewrite E.
  destruct (Rle_dec b a) as [Hba | Hba].
  - pose proof (RInt_ordered r p b a Hr Hp Hb Ha Hba) as H.
    rewrite Rabs_pos_eq with (x := a - b) by lra. exact H.
  - assert (Hab : a <= b) by lra.
    pose proof (RInt_ordered r p a b Hr Hp Ha Hb Hab) as H.
    assert (Hs : RInt (fint r p) b a = - RInt (fint r p) a b).
    { assert (Hc : RInt (fint r p) a b + RInt (fint r p) b a = RInt (fint r p) a a).
      { exact (RInt_Chasles (V := R_CompleteNormedModule) (fint r p) a b a (fint_ex_RInt r p a b Ha Hb) (fint_ex_RInt r p b a Hb Ha)). }
      assert (Hp0 : RInt (fint r p) a a = 0) by (apply (RInt_point (V := R_CompleteNormedModule))).
      lra. }
    rewrite Hs, Rabs_Ropp. rewrite Rabs_minus_sym. rewrite Rabs_pos_eq with (x := b - a) by lra. exact H.
Qed.
