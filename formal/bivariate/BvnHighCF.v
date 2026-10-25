(** Genz's closed form on the last scale: the kernel's evaluation of
    [A1 - A2] against the exact expression, within 1.5e-16 (J units), from the
    leaf contracts of [BvnHighClosed], [BvnHighClosed2] and [BvnHighPol]. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighErr BvnHighErrTree
  BvnHighClosed BvnHighClosed2 BvnHighPol BvnHighPolB.
Open Scope R_scope.

(** The exact closed form: [s e P1 - exp(-hk/2) sqrt(2 pi) Phi(-b/s) b P2] with
    [e = exp(-(bs/s^2 + hk)/2)]. *)
Definition closed_x (Phi : R -> R) (s bs hk : R) : R :=
  let c := (4 - hk) / 8 in
  let d := (12 - hk) / 16 in
  let w := 1 - d * bs / 5 in
  s * exp (- ((bs / (s * s) + hk) / 2))
    * (1 - c * (bs - s * s) * w / 3 + c * d * (s * s) * (s * s) / 5)
  - exp (- (hk / 2)) * sqrt (2 * PI) * Phi (- (sqrt bs / s)) * sqrt bs * (1 - c * bs * w / 3).

(** The kernel's evaluation, operation by operation (each [rnd] is one IEEE
    operation): the code of [high_correlation] after the panels. *)
Definition closed_k (expT sqrtT nc : R -> R) (s bsT hkT : R) : R :=
  let ass := rnd (s * s) in
  let sg := rnd (rnd (bsT / ass) + hkT) in
  let b := sqrtT bsT in
  let c := rnd (rnd (4 - hkT) / 8) in
  let d := rnd (rnd (12 - hkT) / 16) in
  let w := rnd (1 - rnd (rnd (d * bsT) / 5)) in
  let x := rnd (rnd (rnd (c * rnd (bsT - ass)) * w) / 3) in
  let p1 := rnd (rnd (1 - x) + rnd (rnd (rnd (rnd (c * d) * ass) * ass) / 5)) in
  let p2 := rnd (1 - rnd (rnd (rnd (c * bsT) * w) / 3)) in
  let a1 := rnd (rnd (s * expT (- (sg / 2))) * p1) in
  let a2 := rnd (rnd (rnd (rnd (expT (- (hkT / 2)) * SQRT_TAU) * nc (rnd (- b / s))) * b) * p2) in
  rnd (a1 - a2).

Definition xe_leaf (hk bs s E eh S P b : R) (i : nat) : R :=
  match i with
  | 0 => hk | 1 => bs | 2 => s * s | 3 => 1 | 4 => 4 | 5 => 12 | 6 => s
  | 7 => E | 8 => eh | 9 => S | 10 => P | 11 => b | _ => 0 end.

Definition ce_leaf (hk bs ass s E eh S P b : R) (i : nat) : R :=
  match i with
  | 0 => hk | 1 => bs | 2 => ass | 3 => 1 | 4 => 4 | 5 => 12 | 6 => s
  | 7 => E | 8 => eh | 9 => S | 10 => P | 11 => b | _ => 0 end.

Lemma sem_closed Phi s bs hk :
  sem (XE6 (xe_leaf hk bs s (exp (- ((bs / (s * s) + hk) / 2))) (exp (- (hk / 2))) (sqrt (2 * PI))
                    (Phi (- (sqrt bs / s))) (sqrt bs))) A_t = closed_x Phi s bs hk.
Proof.
  unfold closed_x.
  cbv [XE6 XE5 XE4 XE3 XE2 XE1 ext xe_leaf sem A_t A1_t A2_t P1_t P2_t X_t w_t c_t d_t Nat.eqb].
  field.
Qed.

Lemma csem_closed expT sqrtT nc s bsT hkT :
  csem (CE6 (fun _ => 0) (ce_leaf hkT bsT (rnd (s * s)) s (expT (- (rnd (rnd (bsT / rnd (s * s)) + hkT) / 2)))
          (expT (- (hkT / 2))) SQRT_TAU (nc (rnd (- sqrtT bsT / s))) (sqrtT bsT))) A_t
  = closed_k expT sqrtT nc s bsT hkT.
Proof.
  unfold closed_k.
  cbv [CE6 CE5 CE4 CE3 CE2 CE1 ext ce_leaf csem A_t A1_t A2_t P1_t P2_t X_t w_t c_t d_t Nat.eqb].
  reflexivity.
Qed.

Lemma le_div_r a b c : 0 < c -> a * c <= b -> a <= b / c.
Proof. intros Hc H. apply Rmult_le_reg_r with c; [exact Hc|]. replace (b / c * c) with b by (field; lra). exact H. Qed.

Lemma div_le_l a b c : 0 < c -> a <= b * c -> a / c <= b.
Proof. intros Hc H. apply Rmult_le_reg_r with c; [exact Hc|]. replace (a / c * c) with a by (field; lra). exact H. Qed.

Lemma b111 : bpow radix2 (-111) <= u / 10 ^ 17.
Proof.
  unfold u. replace (-111)%Z with (-53 + -58)%Z by lia. rewrite bpow_plus.
  assert (H : bpow radix2 (-58) <= / 10 ^ 17).
  { cbv [bpow]. cbn. interval. }
  assert (0 < bpow radix2 (-53)) by apply bpow_gt_0.
  assert (E : bpow radix2 (-53) / 10 ^ 17 = bpow radix2 (-53) * / 10 ^ 17) by (unfold Rdiv; ring).
  rewrite E. apply Rmult_le_compat_l; lra.
Qed.

Section CF.
Variables expT sqrtT nc Phi : R -> R.
Hypothesis Hex7 : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.
Hypothesis Hexu : forall x, -1000 <= x -> x < -700 -> 0 <= expT x <= 1 / 10 ^ 300.
Hypothesis Hsq0 : forall x, 0 <= x -> rel (sqrt x) (sqrtT x) u.
Hypothesis Hnc : forall x, x <= 0 -> Rabs (nc x - Phi x) <= (u + bpow radix2 (-111)) * Phi x + eta.
Hypothesis PhiA : forall x, x <= 0 -> 0 <= Phi x <= 1 / 2.
Hypothesis PhiL : forall x1 x2, x1 <= 0 -> x2 <= 0 ->
  Rabs (Phi x1 - Phi x2) <= Rabs (x1 - x2) * exp (- (Rmin (- x1) (- x2) * Rmin (- x1) (- x2) / 2)) / (25066 / 10000).

Variables s bs hk bsT hkT e0 : R.
Hypothesis Hs : 1 / 10 ^ 8 <= s <= 3 / 1000.
Hypothesis Hbs : 0 <= bs.
Hypothesis Hbsq : bs <= 4001 / 10 * (s * s).
Hypothesis Hc : - (4 * hk) <= bs.
Hypothesis He0 : 0 <= e0 <= / 10 ^ 200.
Hypothesis Hbs2 : rela bs bsT (31 / 10 * u) e0.
Hypothesis Hhk2 : rela hk hkT u e0.
(** The kernel's guard: the closed form is evaluated only below [b = 20 s]. *)
Hypothesis Hguard : sqrtT bsT < 20 * s.

Hypothesis HbsT0 : 0 <= bsT.

Lemma b_err : Rabs (sqrtT bsT - sqrt bs) <= 43 / 10 * u * sqrt bs + 3 / 10 ^ 100.
Proof.
  pose proof (hk_lo s bs hk Hs Hbsq Hc) as Hl.
  unfold rela in Hbs2. rewrite (Rabs_right bs) in Hbs2 by lra.
  exact (b_rel sqrtT Hsq0 bs bsT e0 Hbs HbsT0 He0 Hbs2).
Qed.

Lemma b_facts : 0 <= sqrtT bsT /\ sqrt bs <= 600001 / 10 ^ 7 /\ sqrt bs / s <= 2001 / 100.
Proof.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  pose proof b_err as He. pose proof (sqrt_pos bs) as Hb0.
  destruct Hs as [Hs1 Hs2].
  apply Rabs_le_inv in He. destruct He as [He1 He2].
  assert (HT : sqrtT bsT >= 0).
  { pose proof (Hsq0 bsT HbsT0) as Hr. unfold rel in Hr. pose proof (Rabs_le_inv _ _ Hr) as [A B].
    rewrite (Rabs_right (sqrt bsT)) in * by (apply Rle_ge; apply sqrt_pos).
    pose proof (sqrt_pos bsT). nra. }
  assert (Hb : sqrt bs * (1 - 43 / 10 * u) <= 20 * s + 3 / 10 ^ 100) by nra.
  assert (Hs3 : 0 < 1 - 43 / 10 * u) by lra.
  repeat split; [lra | | ].
  - assert (HH : sqrt bs <= (20 * s + 3 / 10 ^ 100) / (1 - 43 / 10 * u)).
    { apply le_div_r; [exact Hs3 | lra]. }
    assert ((20 * s + 3 / 10 ^ 100) / (1 - 43 / 10 * u) <= 600001 / 10 ^ 7).
    { apply div_le_l; [exact Hs3|].
      assert (u <= 1112 / 10 ^ 19) by (apply Rlt_le; apply u_small).
      assert (600001 / 10 ^ 7 * (1 - 43 / 10 * (1112 / 10 ^ 19)) >= 600000001 / 10 ^ 10) by interval.
      assert (600001 / 10 ^ 7 * (1 - 43 / 10 * u) >= 600001 / 10 ^ 7 * (1 - 43 / 10 * (1112 / 10 ^ 19))) by (apply Rle_ge; apply Rmult_le_compat_l; [interval | lra]).
      assert (20 * s + 3 / 10 ^ 100 <= 6 / 100 + 3 / 10 ^ 100) by lra.
      assert (6 / 100 + 3 / 10 ^ 100 <= 600000001 / 10 ^ 10) by interval. lra. }
    lra.
  - assert (HH : sqrt bs / s <= ((20 * s + 3 / 10 ^ 100) / (1 - 43 / 10 * u)) / s).
    { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
      apply le_div_r; [exact Hs3 | lra]. }
    assert (E : ((20 * s + 3 / 10 ^ 100) / (1 - 43 / 10 * u)) / s = (20 + 3 / 10 ^ 100 / s) / (1 - 43 / 10 * u)) by (field; split; lra).
    assert (H3 : 3 / 10 ^ 100 / s <= 3 / 10 ^ 92).
    { unfold Rdiv. assert (/ s <= 10 ^ 8).
      { assert (H8 : 1 <= 10 ^ 8 * s) by (assert (10 ^ 8 * (1 / 10 ^ 8) = 1) by field; nra).
        apply Rmult_le_reg_r with s; [lra|]. rewrite Rinv_l by lra. lra. }
      assert (0 <= 3 / 10 ^ 100) by interval.
      assert (3 / 10 ^ 100 * 10 ^ 8 = 3 / 10 ^ 92) by field. nra. }
    assert ((20 + 3 / 10 ^ 92) / (1 - 43 / 10 * u) <= 2001 / 100).
    { apply div_le_l; [exact Hs3|].
      assert (u <= 1112 / 10 ^ 19) by (apply Rlt_le; apply u_small).
      assert (2001 / 100 * (1 - 43 / 10 * (1112 / 10 ^ 19)) >= 2000 / 100 + 3 / 10 ^ 92) by interval.
      assert (2001 / 100 * (1 - 43 / 10 * u) >= 2001 / 100 * (1 - 43 / 10 * (1112 / 10 ^ 19))) by (apply Rle_ge; apply Rmult_le_compat_l; [interval | lra]). lra. }
    assert (Hd : (20 + 3 / 10 ^ 100 / s) / (1 - 43 / 10 * u) <= (20 + 3 / 10 ^ 92) / (1 - 43 / 10 * u)).
    { unfold Rdiv at 1 3. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | lra]. }
    lra.
Qed.

Lemma Phi_leaf : ab (Phi (- (sqrt bs / s))) (nc (rnd (- sqrtT bsT / s))) (1 / 2) (183 / 100 * u).
Proof.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof b_err as He. pose proof b_facts as [HT0 [Hb1 Hq1]].
  pose proof (sqrt_pos bs) as Hb0.
  destruct Hs as [Hs1 Hs2]. assert (Hs0 : 0 < s) by (assert (0 < 1 / 10 ^ 8) by interval; lra).
  set (q := sqrt bs / s) in *.
  assert (Hq0 : 0 <= q) by (unfold q; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  set (y := - sqrtT bsT / s).
  assert (Hy0 : y <= 0).
  { unfold y. replace (- sqrtT bsT / s) with (- (sqrtT bsT / s)) by (field; lra).
    assert (0 <= sqrtT bsT / s) by (apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]). lra. }
  assert (HxT : rnd y <= 0) by (rewrite <- rnd_0; apply rnd_le; exact Hy0).
  assert (Hyq : Rabs (y - - q) <= 43 / 10 * u * q + 3 / 10 ^ 92).
  { unfold y, q. replace (- sqrtT bsT / s - - (sqrt bs / s)) with (- ((sqrtT bsT - sqrt bs) / s)) by (field; lra).
    rewrite Rabs_Ropp. unfold Rdiv at 1. rewrite Rabs_mult, (Rabs_right (/ s)) by (left; apply Rinv_0_lt_compat; lra).
    assert (H1 : Rabs (sqrtT bsT - sqrt bs) * / s <= (43 / 10 * u * sqrt bs + 3 / 10 ^ 100) * / s)
      by (apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact He]).
    assert (H2 : 3 / 10 ^ 100 * / s <= 3 / 10 ^ 92).
    { assert (H8 : 1 <= 10 ^ 8 * s) by (assert (10 ^ 8 * (1 / 10 ^ 8) = 1) by field; nra).
      assert (/ s <= 10 ^ 8) by (apply Rmult_le_reg_r with s; [lra|]; rewrite Rinv_l by lra; lra).
      assert (0 <= 3 / 10 ^ 100) by interval.
      assert (3 / 10 ^ 100 * 10 ^ 8 = 3 / 10 ^ 92) by field. nra. }
    assert (E : (43 / 10 * u * sqrt bs + 3 / 10 ^ 100) * / s = 43 / 10 * u * (sqrt bs / s) + 3 / 10 ^ 100 * / s) by (field; lra).
    lra. }
  assert (Hyabs : Rabs y <= q * (1 + 43 / 10 * u) + 3 / 10 ^ 92).
  { pose proof (Rabs_triang (y - - q) (- q)) as Ht. replace (y - - q + - q) with y in Ht by ring.
    rewrite Rabs_Ropp in Ht. rewrite (Rabs_right q) in Ht by lra. lra. }
  pose proof (rnd_abs y) as Hr.
  assert (Hxq : Rabs (rnd y - - q) <= 54 / 10 * u * q + 4 / 10 ^ 92).
  { pose proof (Rabs_triang (rnd y - y) (y - - q)) as Ht. replace (rnd y - y + (y - - q)) with (rnd y - - q) in Ht by ring.
    assert (Hu1 : u * Rabs y <= u * (q * (1 + 43 / 10 * u) + 3 / 10 ^ 92)) by (apply Rmult_le_compat_l; lra).
    assert (E : u * (q * (1 + 43 / 10 * u) + 3 / 10 ^ 92) = u * q + 43 / 10 * u * (u * q) + u * (3 / 10 ^ 92)) by ring.
    assert (Hq2 : u * (u * q) <= 1 / 100 * (u * q)) by (assert (0 <= u * q) by nra; nra).
    assert (Hq3 : u * (3 / 10 ^ 92) <= 1 / 10 ^ 100) by (assert (u <= 12 / 10 ^ 17) by lra; assert (0 <= 3 / 10 ^ 92) by interval; assert (12 / 10 ^ 17 * (3 / 10 ^ 92) <= 1 / 10 ^ 100) by interval; nra).
    assert (Hη2 : eta <= 1 / 10 ^ 100) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 100) by interval; lra).
    assert (E2 : 54 / 10 * u * q = 54 / 10 * (u * q)) by ring.
    assert (E3 : 43 / 10 * u * q = 43 / 10 * (u * q)) by ring.
    assert (Huq : 0 <= u * q) by nra.
    assert (Hc3 : 3 / 10 ^ 92 + 1 / 10 ^ 100 + 1 / 10 ^ 100 <= 4 / 10 ^ 92) by interval.
    assert (Hc4 : 3 / 10 ^ 92 = 3 * (1 / 10 ^ 92)) by field.
    assert (Hc5 : 4 / 10 ^ 92 = 4 * (1 / 10 ^ 92)) by field.
    lra. }
  pose proof (Phi_diff Phi PhiL q (rnd y) Hq0 Hq1 HxT Hxq) as Hd.
  pose proof (Hnc (rnd y) HxT) as Hn. pose proof (PhiA (rnd y) HxT) as [Ha0 Ha1].
  pose proof (PhiA (- q) ltac:(lra)) as [Hb0' Hb1'].
  unfold ab. split.
  - rewrite Rabs_right by lra. lra.
  - pose proof (Rabs_triang (nc (rnd y) - Phi (rnd y)) (Phi (rnd y) - Phi (- q))) as Ht.
    replace (nc (rnd y) - Phi (rnd y) + (Phi (rnd y) - Phi (- q))) with (nc (rnd y) - Phi (- q)) in Ht by ring.
    pose proof b111 as H111. pose proof (bpow_gt_0 radix2 (-111)) as Hp111.
    assert (H1 : (u + bpow radix2 (-111)) * Phi (rnd y) <= (u + u / 10 ^ 17) * (1 / 2)).
    { apply Rmult_le_compat; [lra | lra | lra | lra]. }
    assert (Hη2 : eta <= u / 10 ^ 30) by (rewrite u_value; assert (/ 10 ^ 300 <= 1 / 9007199254740992 / 10 ^ 30) by interval; lra).
    assert (E4 : (u + u / 10 ^ 17) * (1 / 2) = u / 2 * (1 + 1 / 10 ^ 17)) by field.
    assert (Hz : u / 2 * (1 + 1 / 10 ^ 17) + u / 10 ^ 30 <= 51 / 100 * u) by (assert (0 <= u) by lra; nra).
    lra.
Qed.

Theorem closed_error :
  hk < 100 ->
  Rabs (closed_k expT sqrtT nc s bsT hkT - closed_x Phi s bs hk) <= 15 / 10 ^ 17.
Proof.
  intros Hhk.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof b_facts as [HT0 [Hb1 Hq1]].
  pose proof (hk_lo s bs hk Hs Hbsq Hc) as Hl.
  pose proof (ss_bounds s Hs) as [Hss1 Hss2].
  destruct He0 as [He0a He0b]. assert (He0' : 0 <= e0 <= / 10 ^ 200) by (split; assumption).
  assert (Hhk100 : Rabs hk <= 100) by (apply Rabs_le; lra).
  set (sigT := rnd (rnd (bsT / rnd (s * s)) + hkT)).
  set (Eex := exp (- ((bs / (s * s) + hk) / 2))).
  set (eh := exp (- (hk / 2))).
  set (S := sqrt (2 * PI)).
  set (P := Phi (- (sqrt bs / s))).
  set (b := sqrt bs).
  set (xe0 := xe_leaf hk bs s Eex eh S P b).
  set (ce0 := ce_leaf hkT bsT (rnd (s * s)) s (expT (- (sigT / 2))) (expT (- (hkT / 2))) SQRT_TAU
                (nc (rnd (- sqrtT bsT / s))) (sqrtT bsT)).
  assert (L0 : ab hk hkT 100 (100 * u + 1 / 10 ^ 190)).
  { unfold ab. split; [exact Hhk100|]. unfold rela in Hhk2.
    assert (u * Rabs hk <= u * 100) by (apply Rmult_le_compat_l; lra).
    assert (e0 <= 1 / 10 ^ 190) by (assert (/ 10 ^ 200 <= 1 / 10 ^ 190) by interval; lra). lra. }
  assert (L1 : ab bs bsT (36009 / 10 ^ 7) (32 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 ^ 190)).
  { assert (Hm : bs <= 36009 / 10 ^ 7).
    { assert (4001 / 10 * (s * s) <= 4001 / 10 * (9 / 10 ^ 6)) by (apply Rmult_le_compat_l; [lra | lra]).
      assert (4001 / 10 * (9 / 10 ^ 6) = 36009 / 10 ^ 7) by field. lra. }
    unfold ab. split; [rewrite Rabs_right by lra; exact Hm|]. unfold rela in Hbs2. rewrite (Rabs_right bs) in Hbs2 by lra.
    assert (31 / 10 * u * bs <= 31 / 10 * u * (36009 / 10 ^ 7)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (e0 <= 1 / 10 ^ 190) by (assert (/ 10 ^ 200 <= 1 / 10 ^ 190) by interval; lra).
    assert (E : 32 / 10 * u * (36009 / 10 ^ 7) = 31 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 * u * (36009 / 10 ^ 7)) by field.
    assert (0 <= 1 / 10 * u * (36009 / 10 ^ 7)) by (assert (0 <= u * (36009 / 10 ^ 7)) by (apply Rmult_le_pos; [lra | interval]); lra).
    lra. }
  assert (L2 : ab (s * s) (rnd (s * s)) (9 / 10 ^ 6) (u * (9 / 10 ^ 6) + eta)).
  { unfold ab. split; [rewrite Rabs_right by lra; exact Hss2|].
    pose proof (rnd_abs (s * s)) as Hr. rewrite (Rabs_right (s * s)) in Hr by lra.
    assert (u * (s * s) <= u * (9 / 10 ^ 6)) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Lc : forall x, ab x x (Rabs x) 0) by (intro x; apply ab_exact).
  assert (L3 : ab 1 1 1 0) by (pose proof (Lc 1) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L4 : ab 4 4 4 0) by (pose proof (Lc 4) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L5 : ab 12 12 12 0) by (pose proof (Lc 12) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L6 : ab s s (3 / 1000) 0) by (pose proof (Lc s) as H; rewrite Rabs_right in H by (destruct Hs; lra); destruct Hs; eapply ab_mono; [exact H | lra | lra]).
  assert (Hsig : Rabs (sigT - (bs / (s * s) + hk)) <= 64 / 10 * u * (bs / (s * s) + Rabs hk) + 1 / 10 ^ 170)
    by (exact (sig_err s bs hk bsT hkT e0 Hs Hbs Hbsq He0' Hbs2 Hhk2)).
  assert (L7 : ab Eex (expT (- (sigT / 2))) 1 (35 / 10 * u)).
  { pose proof (Q_bounds s bs Hs Hbs Hbsq) as [Hq0 Hq1']. 
    assert (Hw : 0 <= bs / (s * s) + hk).
    { assert (bs <= bs / (s * s)).
      { assert (1 <= / (s * s)).
        { assert (0 < s * s) by lra. rewrite <- Rinv_1. apply Rinv_le_contravar; [exact H | lra]. }
        replace (bs / (s * s)) with (bs * / (s * s)) by (unfold Rdiv; ring). nra. }
      lra. }
    exact (E_core expT Hex7 Hexu (bs / (s * s)) hk sigT Hq0 Hq1' Hl ltac:(lra) Hw Hsig). }
  assert (L8 : ab eh (expT (- (hkT / 2))) (10005 / 10000) (15 / 10 * u)).
  { exact (eh_leaf expT Hex7 Hexu hk hkT e0 Hl ltac:(lra) He0' Hhk2). }
  assert (L9 : ab S SQRT_TAU (2507 / 1000) (2 / 10 ^ 16)) by exact S_leaf.
  assert (L10 : ab P (nc (rnd (- sqrtT bsT / s))) (1 / 2) (183 / 100 * u)) by exact Phi_leaf.
  assert (L11 : ab b (sqrtT bsT) (601 / 10000) (43 / 10 * u * (601 / 10000) + 3 / 10 ^ 100)).
  { change b with (sqrt bs). pose proof b_err as He. pose proof (sqrt_pos bs) as Hb0. unfold ab. split.
    - rewrite Rabs_right by (apply Rle_ge; exact Hb0). lra.
    - assert (43 / 10 * u * sqrt bs <= 43 / 10 * u * (601 / 10000)) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Henv : forall i, ab (xe0 i) (ce0 i) (me0 i) (ee0 i)).
  { intro i.
    destruct i as [|i]; [exact L0|]. destruct i as [|i]; [exact L1|]. destruct i as [|i]; [exact L2|].
    destruct i as [|i]; [exact L3|]. destruct i as [|i]; [exact L4|]. destruct i as [|i]; [exact L5|].
    destruct i as [|i]; [exact L6|]. destruct i as [|i]; [exact L7|]. destruct i as [|i]; [exact L8|].
    destruct i as [|i]; [exact L9|]. destruct i as [|i]; [exact L10|]. destruct i as [|i]; [exact L11|].
    cbn [xe0 ce0 xe_leaf ce_leaf me0 ee0]. unfold ab. rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. split; lra. }
  pose proof (A_final xe0 ce0 Henv) as HA.
  pose proof (sem_closed Phi s bs hk) as E1.
  pose proof (csem_closed expT sqrtT nc s bsT hkT) as E2.
  assert (E1' : sem (XE6 xe0) A_t = closed_x Phi s bs hk) by exact E1.
  rewrite E1' in HA.
  assert (E3 : csem (CE6 xe0 ce0) A_t = closed_k expT sqrtT nc s bsT hkT).
  { rewrite <- E2. unfold ce0. reflexivity. }
  rewrite E3 in HA. destruct HA as [_ HA]. exact HA.
Qed.

(** [100 <= hk < 1400]: the same, with every exponential factor under [2e-22]. *)
Theorem closed_error_big :
  100 <= hk -> hk < 1400 ->
  Rabs (closed_k expT sqrtT nc s bsT hkT - closed_x Phi s bs hk) <= 1 / 10 ^ 32.
Proof.
  intros Hhk0 Hhk.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof b_facts as [HT0 [Hb1 Hq1]].
  pose proof (hk_lo s bs hk Hs Hbsq Hc) as Hl.
  pose proof (ss_bounds s Hs) as [Hss1 Hss2].
  destruct He0 as [He0a He0b]. assert (He0' : 0 <= e0 <= / 10 ^ 200) by (split; assumption).
  assert (Hhk100 : Rabs hk <= 1400) by (apply Rabs_le; lra).
  set (sigT := rnd (rnd (bsT / rnd (s * s)) + hkT)).
  set (Eex := exp (- ((bs / (s * s) + hk) / 2))).
  set (eh := exp (- (hk / 2))).
  set (S := sqrt (2 * PI)).
  set (P := Phi (- (sqrt bs / s))).
  set (b := sqrt bs).
  set (xe0 := xe_leaf hk bs s Eex eh S P b).
  set (ce0 := ce_leaf hkT bsT (rnd (s * s)) s (expT (- (sigT / 2))) (expT (- (hkT / 2))) SQRT_TAU
                (nc (rnd (- sqrtT bsT / s))) (sqrtT bsT)).
  assert (L0 : ab hk hkT 1400 (1400 * u + 1 / 10 ^ 190)).
  { unfold ab. split; [exact Hhk100|]. unfold rela in Hhk2.
    assert (u * Rabs hk <= u * 1400) by (apply Rmult_le_compat_l; lra).
    assert (e0 <= 1 / 10 ^ 190) by (assert (/ 10 ^ 200 <= 1 / 10 ^ 190) by interval; lra). lra. }
  assert (L1 : ab bs bsT (36009 / 10 ^ 7) (32 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 ^ 190)).
  { assert (Hm : bs <= 36009 / 10 ^ 7).
    { assert (4001 / 10 * (s * s) <= 4001 / 10 * (9 / 10 ^ 6)) by (apply Rmult_le_compat_l; [lra | lra]).
      assert (4001 / 10 * (9 / 10 ^ 6) = 36009 / 10 ^ 7) by field. lra. }
    unfold ab. split; [rewrite Rabs_right by lra; exact Hm|]. unfold rela in Hbs2. rewrite (Rabs_right bs) in Hbs2 by lra.
    assert (31 / 10 * u * bs <= 31 / 10 * u * (36009 / 10 ^ 7)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (e0 <= 1 / 10 ^ 190) by (assert (/ 10 ^ 200 <= 1 / 10 ^ 190) by interval; lra).
    assert (E : 32 / 10 * u * (36009 / 10 ^ 7) = 31 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 * u * (36009 / 10 ^ 7)) by field.
    assert (0 <= 1 / 10 * u * (36009 / 10 ^ 7)) by (assert (0 <= u * (36009 / 10 ^ 7)) by (apply Rmult_le_pos; [lra | interval]); lra).
    lra. }
  assert (L2 : ab (s * s) (rnd (s * s)) (9 / 10 ^ 6) (u * (9 / 10 ^ 6) + eta)).
  { unfold ab. split; [rewrite Rabs_right by lra; exact Hss2|].
    pose proof (rnd_abs (s * s)) as Hr. rewrite (Rabs_right (s * s)) in Hr by lra.
    assert (u * (s * s) <= u * (9 / 10 ^ 6)) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Lc : forall x, ab x x (Rabs x) 0) by (intro x; apply ab_exact).
  assert (L3 : ab 1 1 1 0) by (pose proof (Lc 1) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L4 : ab 4 4 4 0) by (pose proof (Lc 4) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L5 : ab 12 12 12 0) by (pose proof (Lc 12) as H; rewrite Rabs_right in H by lra; exact H).
  assert (L6 : ab s s (3 / 1000) 0) by (pose proof (Lc s) as H; rewrite Rabs_right in H by (destruct Hs; lra); destruct Hs; eapply ab_mono; [exact H | lra | lra]).
  assert (Hsig : Rabs (sigT - (bs / (s * s) + hk)) <= 64 / 10 * u * (bs / (s * s) + Rabs hk) + 1 / 10 ^ 170)
    by (exact (sig_err s bs hk bsT hkT e0 Hs Hbs Hbsq He0' Hbs2 Hhk2)).
  assert (L7 : ab Eex (expT (- (sigT / 2))) (2 / 10 ^ 22) (1 / 10 ^ 32)).
  { pose proof (Q_bounds s bs Hs Hbs Hbsq) as [Hq0 Hq1']. 
    assert (Hw : 0 <= bs / (s * s) + hk).
    { assert (bs <= bs / (s * s)).
      { assert (1 <= / (s * s)).
        { assert (0 < s * s) by lra. rewrite <- Rinv_1. apply Rinv_le_contravar; [exact H | lra]. }
        replace (bs / (s * s)) with (bs * / (s * s)) by (unfold Rdiv; ring). nra. }
      lra. }
    exact (E_core_big expT Hex7 Hexu (bs / (s * s)) hk sigT Hq0 Hq1' Hhk0 ltac:(lra) Hsig). }
  assert (L8 : ab eh (expT (- (hkT / 2))) (2 / 10 ^ 22) (1 / 10 ^ 32)).
  { exact (eh_leaf_big expT Hex7 Hexu hk hkT e0 Hhk0 ltac:(lra) He0' Hhk2). }
  assert (L9 : ab S SQRT_TAU (2507 / 1000) (2 / 10 ^ 16)) by exact S_leaf.
  assert (L10 : ab P (nc (rnd (- sqrtT bsT / s))) (1 / 2) (183 / 100 * u)) by exact Phi_leaf.
  assert (L11 : ab b (sqrtT bsT) (601 / 10000) (43 / 10 * u * (601 / 10000) + 3 / 10 ^ 100)).
  { change b with (sqrt bs). pose proof b_err as He. pose proof (sqrt_pos bs) as Hb0. unfold ab. split.
    - rewrite Rabs_right by (apply Rle_ge; exact Hb0). lra.
    - assert (43 / 10 * u * sqrt bs <= 43 / 10 * u * (601 / 10000)) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Henv : forall i, ab (xe0 i) (ce0 i) (me0b i) (ee0b i)).
  { intro i.
    destruct i as [|i]; [exact L0|]. destruct i as [|i]; [exact L1|]. destruct i as [|i]; [exact L2|].
    destruct i as [|i]; [exact L3|]. destruct i as [|i]; [exact L4|]. destruct i as [|i]; [exact L5|].
    destruct i as [|i]; [exact L6|]. destruct i as [|i]; [exact L7|]. destruct i as [|i]; [exact L8|].
    destruct i as [|i]; [exact L9|]. destruct i as [|i]; [exact L10|]. destruct i as [|i]; [exact L11|].
    cbn [xe0 ce0 xe_leaf ce_leaf me0b ee0b]. unfold ab. rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. split; lra. }
  pose proof (A_final_b xe0 ce0 Henv) as HA.
  pose proof (sem_closed Phi s bs hk) as E1.
  pose proof (csem_closed expT sqrtT nc s bsT hkT) as E2.
  assert (E1' : sem (XE6 xe0) A_t = closed_x Phi s bs hk) by exact E1.
  rewrite E1' in HA.
  assert (E3 : csem (CE6 xe0 ce0) A_t = closed_k expT sqrtT nc s bsT hkT).
  { rewrite <- E2. unfold ce0. reflexivity. }
  rewrite E3 in HA. destruct HA as [_ HA]. exact HA.
Qed.
End CF.

(** The kernel's guard [b < 20 s] bounds [bs] by [400.1 s^2] (so [bs <= 3.6e-3]). *)
Lemma guard_bsq (sqrtT : R -> R) (s bs bsT e0 : R) :
  (forall x, 0 <= x -> rel (sqrt x) (sqrtT x) u) ->
  1 / 10 ^ 8 <= s <= 3 / 1000 -> 0 <= bs -> 0 <= bsT -> 0 <= e0 <= / 10 ^ 200 ->
  rela bs bsT (31 / 10 * u) e0 -> sqrtT bsT < 20 * s -> bs <= 4001 / 10 * (s * s).
Proof.
  intros Hsq0 Hs Hbs HbsT He0 Hbs2 Hg.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  unfold rela in Hbs2. rewrite (Rabs_right bs) in Hbs2 by lra.
  pose proof (b_rel sqrtT Hsq0 bs bsT e0 Hbs HbsT He0 Hbs2) as He.
  pose proof (sqrt_pos bs) as Hb0. pose proof (sqrt_sqrt bs Hbs) as Eb.
  destruct Hs as [Hs1 Hs2]. apply Rabs_le_inv in He. destruct He as [He1 He2].
  assert (Hb : sqrt bs * (1 - 43 / 10 * u) <= 20 * s + 3 / 10 ^ 100) by nra.
  assert (H8 : 1 <= 10 ^ 8 * s) by (assert (10 ^ 8 * (1 / 10 ^ 8) = 1) by field; nra).
  assert (Htiny : 3 / 10 ^ 100 <= 3 / 10 ^ 92 * s).
  { assert (3 / 10 ^ 92 * s >= 3 / 10 ^ 92 * (1 / 10 ^ 8)) by (apply Rle_ge; apply Rmult_le_compat_l; [interval | lra]).
    assert (3 / 10 ^ 92 * (1 / 10 ^ 8) = 3 / 10 ^ 100) by field. lra. }
  assert (Hc : sqrt bs <= 2001 / 100 * s).
  { assert (Hl : 20 * s + 3 / 10 ^ 92 * s <= (2001 / 100) * s * (1 - 43 / 10 * u)).
    { assert (u <= 1112 / 10 ^ 19) by (apply Rlt_le; apply u_small).
      assert (2001 / 100 * (1 - 43 / 10 * u) >= 20 + 3 / 10 ^ 92) by (rewrite u_value; interval).
      nra. }
    assert (Hpos : 0 < 1 - 43 / 10 * u) by lra.
    apply Rmult_le_reg_r with (1 - 43 / 10 * u); [exact Hpos|]. nra. }
  assert (Hq : sqrt bs * sqrt bs <= (2001 / 100 * s) * (2001 / 100 * s)) by (apply Rmult_le_compat; lra).
  nra.
Qed.
