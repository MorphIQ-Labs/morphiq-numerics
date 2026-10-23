(** From the terms to the corrected sum: [rndF (rndF (H + L) * Kh)] against
    [Kex * V], where [V] is the exact sum of the weighted integrand values the
    terms approximate. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound BvnSum.
Open Scope R_scope.

Definition psi (etaK : R) : R := (1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) - 1.

Lemma chain ts V B1 Kex Kh etaK :
  (forall t, In t ts -> fmtF t /\ 0 <= t) -> (length ts <= 24)%nat ->
  0 <= V -> 0 <= B1 -> Rabs (sumR ts - V) <= B1 + 72 * z ->
  0 <= Kex -> Kex <= 1 -> Rabs (Kh - Kex) <= etaK * Kex -> 0 <= etaK -> etaK <= / 1000 ->
  Rabs (rndF (rndF (fst (acc ts (0, 0)) + snd (acc ts (0, 0))) * Kh) - Kex * V)
    <= Kex * (psi etaK * V + (1 + psi etaK) * B1) + 1000 * z.
Proof.
  intros Hts Hn HV HB1 HT HKex HK1 HKh Heta Heta1.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz0.
  destruct (acc_final ts Hts Hn) as [FH [FL Hacc]].
  set (T := sumR ts) in *.
  set (H := fst (acc ts (0, 0))) in *. set (L := snd (acc ts (0, 0))) in *.
  assert (HT0 : 0 <= T) by (apply sumR_nonneg; intros t Ht; apply (Hts t Ht)).
  assert (HTabs : Rabs (T - V) <= B1 + 72 * z) by exact HT.
  apply Rabs_le_inv in HT. destruct HT as [HTl HTu].
  assert (Hu2 : 2000 * u * u <= / 1000000) by (rewrite Huv; lra).
  assert (HHL : Rabs (H + L) <= T * (1 + 2000 * u * u) + 30 * z).
  { assert (E : H + L = T + (H + L - T)) by ring. rewrite E.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_pos_eq T HT0). nra. }
  pose proof (rnd_rel_z (H + L)) as Hr1. set (hh := rndF (H + L)) in *.
  assert (Hhh : Rabs hh <= (T * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z).
  { assert (Hs : Rabs hh <= Rabs (H + L) + Rabs (hh - (H + L))).
    { assert (E : hh = (H + L) + (hh - (H + L))) by ring. rewrite E at 1. apply Rabs_triang. }
    nra. }
  (* distance of hh to V *)
  assert (HhV : Rabs (hh - V) <= (u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) + B1 + 400 * z).
  { assert (E : hh - V = (hh - (H + L)) + ((H + L) - T) + (T - V)) by ring. rewrite E.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
    assert (HTV : T <= V + B1 + 72 * z) by lra.
    assert (Hq : u * Rabs (H + L) <= u * (T * (1 + 2000 * u * u) + 30 * z)) by (apply Rmult_le_compat_l; lra).
    assert (Hc : 0 <= u * (1 + 2000 * u * u)) by nra.
    assert (Hq2 : u * (1 + 2000 * u * u) * T <= u * (1 + 2000 * u * u) * (V + B1 + 72 * z))
      by (apply Rmult_le_compat_l; lra).
    assert (HT2 : 2000 * u * u * T <= 2000 * u * u * (V + B1 + 72 * z))
      by (apply Rmult_le_compat_l; [nra | lra]).
    assert (Hzs : 72 * (u * (1 + 2000 * u * u)) * z + 30 * u * z + 2000 * u * u * 72 * z + z + 30 * z + 72 * z <= 400 * z)
      by (assert (u <= / 1000000) by (rewrite Huv; lra); nra).
    assert (Eq1 : u * (T * (1 + 2000 * u * u) + 30 * z) = u * (1 + 2000 * u * u) * T + 30 * u * z) by ring.
    assert (Eq2 : u * (1 + 2000 * u * u) * (V + B1 + 72 * z) = u * (1 + 2000 * u * u) * (V + B1) + 72 * (u * (1 + 2000 * u * u)) * z) by ring.
    assert (Eq3 : 2000 * u * u * (V + B1 + 72 * z) = 2000 * u * u * (V + B1) + 2000 * u * u * 72 * z) by ring.
    assert (Eq4 : (u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) = u * (1 + 2000 * u * u) * (V + B1) + 2000 * u * u * (V + B1)) by ring.
    lra. }
  set (m := hh * Kh).
  assert (HKhb : Kh <= Kex * (1 + etaK) /\ 0 <= Kh).
  { assert (HKc : Rabs (Kh - Kex) <= etaK * Kex) by exact HKh.
    apply Rabs_le_inv in HKc. destruct HKc as [A1 A2]. split; nra. }
  destruct HKhb as [HKh1 HKh2].
  pose proof (rnd_rel_z m) as Hr2.
  assert (Hm : Rabs m <= Kex * (1 + etaK) * ((T * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z)).
  { unfold m. rewrite Rabs_mult, (Rabs_pos_eq Kh HKh2).
    assert (Hp : 0 <= (T * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z) by nra.
    pose proof (Rabs_pos hh). nra. }
  assert (HmV : Rabs (m - Kex * V) <= Kex * (1 + etaK) * Rabs (hh - V) + V * (etaK * Kex)).
  { assert (E : m - Kex * V = (hh - V) * Kh + V * (Kh - Kex)) by (unfold m; ring).
    rewrite E. eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
    rewrite (Rabs_pos_eq Kh HKh2), (Rabs_pos_eq V HV).
    assert (Hx : Rabs (hh - V) * Kh <= Rabs (hh - V) * (Kex * (1 + etaK)))
      by (apply Rmult_le_compat_l; [apply Rabs_pos | exact HKh1]).
    assert (Hy : V * Rabs (Kh - Kex) <= V * (etaK * Kex)) by (apply Rmult_le_compat_l; lra).
    nra. }
  assert (E : rndF m - Kex * V = (rndF m - m) + (m - Kex * V)) by ring.
  rewrite E. eapply Rle_trans; [apply Rabs_triang |].
  assert (Hu1 : u * Rabs m <= u * (Kex * (1 + etaK) * ((T * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z)))
    by (apply Rmult_le_compat_l; lra).
  (* combine; T <= V + B1 + 72 z *)
  assert (HTV : T <= V + B1 + 72 * z) by lra.
  set (P := (1 + etaK) * (1 + 2000 * u * u) * (1 + u) * (1 + u)).
  unfold psi.
  assert (Hk1 : Kex * (1 + etaK) * ((u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) + B1) + V * (etaK * Kex)
                + u * (Kex * (1 + etaK) * (((V + B1) * (1 + 2000 * u * u)) * (1 + u)))
                = Kex * ((P - 1) * V + P * B1)).
  { unfold P. ring. }
  assert (Hz1 : Kex * (1 + etaK) * 400 * z + u * (Kex * (1 + etaK) * ((72 * z * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z)) + z <= 1000 * z).
  { assert (Kex * (1 + etaK) <= 2) by nra. nra. }
  assert (Hke : 0 <= Kex * (1 + etaK)) by nra.
  assert (F1 : Kex * (1 + etaK) * Rabs (hh - V)
               <= Kex * (1 + etaK) * ((u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) + B1 + 400 * z))
    by (apply Rmult_le_compat_l; [exact Hke | exact HhV]).
  assert (F2 : u * (Kex * (1 + etaK) * ((T * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z))
               <= u * (Kex * (1 + etaK) * (((V + B1 + 72 * z) * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z))).
  { apply Rmult_le_compat_l; [lra |]. apply Rmult_le_compat_l; [exact Hke |].
    assert (0 < 1 + u) by lra. assert (0 <= 1 + 2000 * u * u) by nra.
    assert (T * (1 + 2000 * u * u) <= (V + B1 + 72 * z) * (1 + 2000 * u * u)) by (apply Rmult_le_compat_r; lra).
    nra. }
  assert (Eq1 : u * (Kex * (1 + etaK) * (((V + B1 + 72 * z) * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z))
                = u * (Kex * (1 + etaK) * (((V + B1) * (1 + 2000 * u * u)) * (1 + u)))
                  + u * (Kex * (1 + etaK) * ((72 * z * (1 + 2000 * u * u) + 30 * z) * (1 + u) + z))) by ring.
  assert (Eq2 : Kex * (1 + etaK) * ((u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) + B1 + 400 * z)
                = Kex * (1 + etaK) * ((u * (1 + 2000 * u * u) + 2000 * u * u) * (V + B1) + B1) + Kex * (1 + etaK) * 400 * z) by ring.
  lra.
Qed.
