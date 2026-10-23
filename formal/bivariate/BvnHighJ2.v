(** The integral's computed value against the exact integral (docs/bivariate_normal_high.md
    section 4.6): the panel sums, the node roundings, the double-word accumulation, the
    closed form, and the rounding of the scale, composed.  The integral [I x y] of the
    integrand over [[x, y]] is abstract: only additivity and the bound [F <= 1.0818] on
    the integrand are used, both classical. *)
From Coq Require Import Reals Lra Psatz ZArith Lia List.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighSum.
Open Scope R_scope.

Fixpoint sumn (f : nat -> R) (m : nat) : R :=
  match m with O => 0 | S k => sumn f k + f k end.

(** The relative accuracy of one node term: [|t - x| <= delta x], [x >= 0]. *)
Definition delta : R := 117 / 10 * u + 1 / 10 ^ 39.
Definition node_ok (t x : R) : Prop := 0 <= x /\ Rabs (t - x) <= delta * x.

Lemma delta_value : delta <= 130 / 10 ^ 17 * (1 / 1) /\ 0 < delta.
Proof. unfold delta. pose proof u_pos. split; [rewrite u_value; interval | assert (0 < 1 / 10 ^ 39) by interval; lra]. Qed.

Lemma ssum_nodes l e :
  Forall2 node_ok l e ->
  0 <= ssum e /\ Rabs (ssum l - ssum e) <= delta * ssum e /\ sabs l <= (1 + delta) * ssum e.
Proof.
  intros H. induction H as [|t x l e [Hx Ht] Hr IH]; simpl.
  - split; [lra|]. split; [|lra]. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct IH as [I0 [I1 I2]]. destruct delta_value as [_ Hd].
    repeat split.
    + lra.
    + replace (t + ssum l - (x + ssum e)) with ((t - x) + (ssum l - ssum e)) by ring.
      eapply Rle_trans; [apply Rabs_triang|]. nra.
    + pose proof (Rabs_triang (t - x) x) as T. replace (t - x + x) with t in T by ring.
      rewrite (Rabs_right x) in T by lra. nra.
Qed.

Lemma sumn_ge0 f m : (forall j, (j < m)%nat -> 0 <= f j) -> 0 <= sumn f m.
Proof. induction m as [|k IH]; intros H; simpl; [lra|]. pose proof (IH (fun j Hj => H j (Nat.lt_lt_succ_r _ _ Hj))). pose proof (H k (Nat.lt_succ_diag_r k)). lra. Qed.

Section Compose.
Variable I : R -> R -> R.
Hypothesis Iadd : forall x y z, 0 <= x -> x <= y -> y <= z -> z <= 381 / 1000 -> I x z = I x y + I y z.
Hypothesis Ibd : forall x y, 0 <= x -> x <= y -> y <= 381 / 1000 -> 0 <= I x y <= 10818 / 10000 * (y - x).

Variable at_ : R.
Hypothesis Hat : 0 < at_ <= 381 / 1000.
Definition sc (j : nat) : R := at_ / 2 ^ j.

Lemma sc_pos j : 0 < sc j.
Proof. unfold sc. apply Rdiv_lt_0_compat; [lra | apply pow_lt; lra]. Qed.

Lemma sc_succ j : sc (S j) = sc j / 2.
Proof. unfold sc. simpl. field. apply pow_nonzero; lra. Qed.

Lemma sc_le j : sc j <= at_.
Proof.
  induction j as [|k IH]; [unfold sc; simpl; right; field|].
  rewrite sc_succ. pose proof (sc_pos k). lra.
Qed.

Lemma sc_mono j k : (j <= k)%nat -> sc k <= sc j.
Proof.
  intros H. induction H as [|k Hk IH]; [lra|]. rewrite sc_succ. pose proof (sc_pos k). lra.
Qed.

Lemma sc_sum m : sumn sc m = 2 * at_ - 2 * sc m.
Proof.
  induction m as [|k IH]; simpl.
  - unfold sc. simpl. field.
  - rewrite IH. rewrite sc_succ. lra.
Qed.

Lemma I_self x : 0 <= x -> x <= 381 / 1000 -> I x x = 0.
Proof. intros H0 H1. pose proof (Ibd x x H0 (Rle_refl x) H1). lra. Qed.

Lemma telescope m : I (sc m) at_ = sumn (fun j => I (sc (S j)) (sc j)) m.
Proof.
  induction m as [|k IH]; simpl.
  - unfold sc. simpl. replace (at_ / 1) with at_ by field. apply I_self; lra.
  - assert (H : I (sc (S k)) at_ = I (sc (S k)) (sc k) + I (sc k) at_).
    { pose proof (sc_pos (S k)). pose proof (sc_le k). pose proof (sc_succ k). pose proof (sc_pos k).
      apply Iadd; lra. }
    rewrite H, IH. ring.
Qed.

Variable g : nat -> R.
Variable c15 : R.
Hypothesis Hc15 : 0 <= c15 <= 63 / 10 ^ 18.
(** The Gauss-Legendre remainder of each panel, from the cited bound with the
    certificate of [BvnHighPanels]. *)
Variable m : nat.
Hypothesis Hgl : forall j, (j < m)%nat -> Rabs (g j - I (sc (S j)) (sc j)) <= sc j * c15.

Lemma sumn_scale (c : R) k : sumn (fun j => sc j * c) k = c * sumn sc k.
Proof. induction k as [|k IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma sumn_err f h t k :
  (forall j, (j < k)%nat -> Rabs (f j - h j) <= t j) ->
  Rabs (sumn f k - sumn h k) <= sumn t k.
Proof.
  induction k as [|k IH]; intros H; simpl.
  - rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. lra.
  - pose proof (IH (fun j Hj => H j (Nat.lt_lt_succ_r _ _ Hj))) as I1.
    pose proof (H k (Nat.lt_succ_diag_r k)) as I2.
    replace (sumn f k + f k - (sumn h k + h k)) with ((sumn f k - sumn h k) + (f k - h k)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma trunc_sum : Rabs (sumn g m - I (sc m) at_) <= c15 * (2 * at_).
Proof.
  rewrite telescope.
  eapply Rle_trans; [apply (sumn_err g (fun j => I (sc (S j)) (sc j)) (fun j => sc j * c15) m Hgl)|].
  rewrite (sumn_scale c15 m), sc_sum. pose proof (sc_pos m). nra.
Qed.

Lemma I_nonneg_hi x y : 0 <= x -> x <= y -> y <= 381 / 1000 -> 0 <= I x y <= 10818 / 10000 * (y - x).
Proof. exact (Ibd x y). Qed.

Variables (ts : R -> R -> R * R).
Hypothesis Hts : forall a b, fst (ts a b) = rnd (a + b) /\ fst (ts a b) + snd (ts a b) = a + b.
Variables (l e : list R) (Cl ae : R).
Hypothesis Hnodes : Forall2 node_ok l e.
Hypothesis Hlen : (length l <= 112)%nat.
Hypothesis Hsum : ssum e = sumn g m.
(** The closed form's value against the integral over [[0, s_f]]. *)
Hypothesis Hcl : Rabs (Cl - I 0 (sc m)) <= 161 / 10 ^ 18.
(** The exact scale, [a], against the computed [a~]. *)
Hypothesis Hae : Rabs (at_ - ae) <= 203 / 100 * u * ae.
Hypothesis Hae1 : 0 < ae <= 38 / 100.

Theorem J_bound :
  let r := dwsum ts 0 0 l in
  let P := rnd (fst r + snd r) in
  Rabs (rnd (Cl + P) - I 0 ae) <= 94 / 10 ^ 17.
Proof.
  intros r P.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη. pose proof u_value as Huv.
  destruct delta_value as [Hd1 Hd0].
  destruct (ssum_nodes l e Hnodes) as [S0 [S1 S2]].
  pose proof trunc_sum as Ht. pose proof (sc_le m) as Hscm.
  pose proof (sc_pos m) as Hscp.
  assert (HI0 : 0 <= I 0 (sc m) /\ 0 <= I (sc m) at_ /\ I 0 at_ = I 0 (sc m) + I (sc m) at_ /\ I 0 at_ <= 10818 / 10000 * at_).
  { pose proof (Ibd 0 (sc m) (Rle_refl 0) ltac:(lra) ltac:(lra)) as A.
    pose proof (Ibd (sc m) at_ ltac:(lra) Hscm ltac:(lra)) as B.
    pose proof (Ibd 0 at_ (Rle_refl 0) ltac:(lra) ltac:(lra)) as C.
    pose proof (Iadd 0 (sc m) at_ (Rle_refl 0) ltac:(lra) Hscm ltac:(lra)) as D.
    repeat split; lra. }
  destruct HI0 as [HA [HB [HC HD]]].
  assert (Hc2 : c15 * (2 * at_) <= 5 / 10 ^ 17).
  { assert (c15 * (2 * at_) <= 63 / 10 ^ 18 * (2 * (381 / 1000))) by (apply Rmult_le_compat; [lra | lra | lra | lra]).
    assert (63 / 10 ^ 18 * (2 * (381 / 1000)) <= 5 / 10 ^ 17) by interval. lra. }
  apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  assert (HSe : ssum e <= 4123 / 10 ^ 4).
  { rewrite Hsum.
    assert (10818 / 10000 * at_ <= 10818 / 10000 * (381 / 1000)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (10818 / 10000 * (381 / 1000) + 5 / 10 ^ 17 <= 4123 / 10 ^ 4) by interval. lra. }
  assert (HSl : Rabs (ssum l) <= 4124 / 10 ^ 4).
  { assert (delta * ssum e <= delta * (4123 / 10 ^ 4)) by (apply Rmult_le_compat_l; lra).
    assert (delta * (4123 / 10 ^ 4) <= 1 / 10 ^ 12) by (unfold delta; rewrite Huv; interval).
    pose proof (Rabs_le_inv _ _ S1) as [A B]. apply Rabs_le. lra. }
  assert (HNode : delta * ssum e <= 54 / 10 ^ 17).
  { assert (delta * ssum e <= delta * (4123 / 10 ^ 4)) by (apply Rmult_le_compat_l; lra).
    assert (delta * (4123 / 10 ^ 4) <= 54 / 10 ^ 17) by (unfold delta; rewrite Huv; interval). lra. }
  (* the double-word sum *)
  assert (Hlen' : INR (length l) <= 112) by (replace 112 with (INR 112) by (simpl; lra); apply le_INR; exact Hlen).
  assert (Hn0 : 0 <= INR (length l)) by apply pos_INR.
  assert (Hc54 : c54 / 2 <= 1 / 10 ^ 16) by exact c55_small.
  pose proof c54_pos as Hcp.
  assert (Hsab : sabs l <= 4124 / 10 ^ 4).
  { assert ((1 + delta) * ssum e <= (1 + delta) * (4123 / 10 ^ 4)) by (apply Rmult_le_compat_l; lra).
    assert ((1 + delta) * (4123 / 10 ^ 4) <= 4124 / 10 ^ 4) by (unfold delta; rewrite Huv; interval). lra. }
  assert (Hdw1 : Rabs 0 + sabs l + INR (length l) * (c54 / 2) < 46 / 100).
  { rewrite Rabs_R0. assert (INR (length l) * (c54 / 2) <= 112 * (1 / 10 ^ 16)) by (apply Rmult_le_compat; [lra | lra | lra | lra]).
    assert (112 * (1 / 10 ^ 16) <= 1 / 10 ^ 10) by interval. lra. }
  assert (Hdw2 : Rabs 0 + INR (length l) * (1 / 10 ^ 15) <= 1 / 10 ^ 12).
  { rewrite Rabs_R0. assert (INR (length l) * (1 / 10 ^ 15) <= 112 * (1 / 10 ^ 15)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (112 * (1 / 10 ^ 15) <= 1 / 10 ^ 12) by interval. lra. }
  pose proof (dw_ok ts Hts l 0 0 Hdw1 Hdw2) as Hdw. cbv zeta in Hdw.
  fold r in Hdw. destruct Hdw as [Hw1 [Hw2 Hw3]].
  replace (0 + 0 + ssum l) with (ssum l) in Hw1 by ring.
  assert (Hdwe : INR (length l) * (1 / 10 ^ 27) <= 1 / 10 ^ 24).
  { assert (INR (length l) * (1 / 10 ^ 27) <= 112 * (1 / 10 ^ 27)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (112 * (1 / 10 ^ 27) <= 1 / 10 ^ 24) by interval. lra. }
  assert (Hhl : Rabs (fst r + snd r) <= 4125 / 10 ^ 4).
  { pose proof (Rabs_triang (fst r + snd r - ssum l) (ssum l)) as T.
    replace (fst r + snd r - ssum l + ssum l) with (fst r + snd r) in T by ring.
    assert (1 / 10 ^ 24 <= 1 / 10 ^ 5) by interval. lra. }
  pose proof (rnd_abs (fst r + snd r)) as HP1. fold P in HP1.
  assert (HP2 : Rabs (P - (fst r + snd r)) <= 46 / 10 ^ 18 + 1 / 10 ^ 290).
  { assert (u * Rabs (fst r + snd r) <= u * (4125 / 10 ^ 4)) by (apply Rmult_le_compat_l; lra).
    assert (u * (4125 / 10 ^ 4) <= 46 / 10 ^ 18) by (rewrite Huv; interval).
    assert (eta <= 1 / 10 ^ 290) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 290) by interval; lra). lra. }
  (* P against the integral over [s_f, a~] *)
  assert (HP3 : Rabs (P - I (sc m) at_) <= 46 / 10 ^ 18 + 1 / 10 ^ 290 + 1 / 10 ^ 24 + 54 / 10 ^ 17 + 5 / 10 ^ 17).
  { apply Rabs_le_inv in HP2. destruct HP2 as [P1 P2]. apply Rabs_le_inv in Hw1. destruct Hw1 as [W1 W2].
    apply Rabs_le_inv in S1. destruct S1 as [Q1 Q2]. apply Rabs_le. split; lra. }
  (* the closed form and the sum *)
  assert (HCl : Rabs (Cl + P - I 0 at_) <= 161 / 10 ^ 18 + (46 / 10 ^ 18 + 1 / 10 ^ 290 + 1 / 10 ^ 24 + 54 / 10 ^ 17 + 5 / 10 ^ 17)).
  { apply Rabs_le_inv in Hcl. destruct Hcl as [C1 C2]. apply Rabs_le_inv in HP3. destruct HP3 as [R1 R2].
    apply Rabs_le. split; lra. }
  assert (HClb : Rabs (Cl + P) <= 4126 / 10 ^ 4).
  { apply Rabs_le_inv in HCl. destruct HCl as [C1 C2].
    assert (10818 / 10000 * at_ <= 10818 / 10000 * (381 / 1000)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (10818 / 10000 * (381 / 1000) + 161 / 10 ^ 18 + (46 / 10 ^ 18 + 1 / 10 ^ 290 + 1 / 10 ^ 24 + 54 / 10 ^ 17 + 5 / 10 ^ 17) <= 4126 / 10 ^ 4) by interval.
    apply Rabs_le. split; lra. }
  pose proof (rnd_abs (Cl + P)) as HF1.
  assert (HF2 : Rabs (rnd (Cl + P) - (Cl + P)) <= 46 / 10 ^ 18 + 1 / 10 ^ 290).
  { assert (u * Rabs (Cl + P) <= u * (4126 / 10 ^ 4)) by (apply Rmult_le_compat_l; lra).
    assert (u * (4126 / 10 ^ 4) <= 46 / 10 ^ 18) by (rewrite Huv; interval).
    assert (eta <= 1 / 10 ^ 290) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 290) by interval; lra). lra. }
  (* the sliver *)
  assert (Hsl : Rabs (I 0 at_ - I 0 ae) <= 94 / 10 ^ 18).
  { assert (Hdiff : forall x y, 0 < x -> x <= y -> y <= 381 / 1000 -> I 0 y - I 0 x <= 10818 / 10000 * (y - x)).
    { intros x y Hx Hxy Hy. pose proof (Iadd 0 x y (Rle_refl 0) (Rlt_le _ _ Hx) Hxy Hy) as A.
      pose proof (Ibd x y (Rlt_le _ _ Hx) Hxy Hy) as B. lra. }
    pose proof (Rabs_le_inv _ _ Hae) as [H1 H2].
    assert (Hq : 203 / 100 * u * ae <= 203 / 100 * u * (38 / 100)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (Hz : 10818 / 10000 * (203 / 100 * u * (38 / 100)) <= 94 / 10 ^ 18) by (rewrite Huv; interval).
    assert (Hz2 : 0 <= 203 / 100 * u * ae) by (apply Rmult_le_pos; [lra | lra]).
    destruct (Rle_dec at_ ae) as [Hle|Hgt].
    - assert (ae <= 381 / 1000) by lra. pose proof (Hdiff at_ ae ltac:(lra) Hle ltac:(lra)) as D.
      pose proof (Ibd at_ ae ltac:(lra) Hle ltac:(lra)) as B. pose proof (Iadd 0 at_ ae (Rle_refl 0) ltac:(lra) Hle ltac:(lra)) as A.
      assert (Hm : 10818 / 10000 * (ae - at_) <= 10818 / 10000 * (203 / 100 * u * (38 / 100))) by (apply Rmult_le_compat_l; lra).
      apply Rabs_le. split; lra.
    - pose proof (Hdiff ae at_ ltac:(lra) ltac:(lra) ltac:(lra)) as D.
      pose proof (Ibd ae at_ ltac:(lra) ltac:(lra) ltac:(lra)) as B. pose proof (Iadd 0 ae at_ (Rle_refl 0) ltac:(lra) ltac:(lra) ltac:(lra)) as A.
      assert (Hm : 10818 / 10000 * (at_ - ae) <= 10818 / 10000 * (203 / 100 * u * (38 / 100))) by (apply Rmult_le_compat_l; lra).
      apply Rabs_le. split; lra. }
  apply Rabs_le_inv in HF2. destruct HF2 as [F1 F2]. apply Rabs_le_inv in HCl. destruct HCl as [K1 K2].
  apply Rabs_le_inv in Hsl. destruct Hsl as [L1 L2].
  assert (Hfin : 161 / 10 ^ 18 + (46 / 10 ^ 18 + 1 / 10 ^ 290 + 1 / 10 ^ 24 + 54 / 10 ^ 17 + 5 / 10 ^ 17) + (46 / 10 ^ 18 + 1 / 10 ^ 290) + 94 / 10 ^ 18 <= 94 / 10 ^ 17) by interval with (i_prec 100).
  apply Rabs_le. split; lra.
Qed.
End Compose.
