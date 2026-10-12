(** A reflective enclosure of [ln] at a positive rational, for checking whole
    tables of logarithms by one computation each ([vm_compute]) instead of a
    proof per entry.

    For [a > b > 0], [ln(a/b) = ln((1 + t)/(1 − t))] with [t = (a − b)/(a + b)]
    in [[0, 1)], and [ln((1 + t)/(1 − t)) = 2·(t + t^3/3 + t^5/5 + …)]. The
    first [n] terms are a lower bound, and adding [2·t^(2n+1)/(1 − t^2)] gives
    an upper bound ([ln_ser_bounds], by the mean value theorem: the
    difference's derivative is [2·t^(2n)/(1 − t^2)]). [ln_bounds] evaluates
    both in integer arithmetic scaled by [2^m], rounding each product and
    quotient outward, so its result [(L, U)] satisfies
    [L·2^-m <= ln(a/b) <= U·2^-m] for every [a, b > 0], [m >= 0] and [n]
    ([ln_bounds_ok]); [n] and [m] only decide how tight it is. [a < b] is
    taken as [−ln(b/a)]. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.

Open Scope R_scope.

(** * The series and its remainder *)

Fixpoint ser (n : nat) (t : R) : R :=
  match n with
  | O => 0
  | S k => ser k t + 2 / INR (2 * k + 1) * t ^ (2 * k + 1)
  end.

Fixpoint dser (n : nat) (t : R) : R :=
  match n with
  | O => 0
  | S k => dser k t + 2 * t ^ (2 * k)
  end.

Lemma lim_eq f x l l' : derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros H E. rewrite <- E. exact H. Qed.

Lemma ser_deriv n t : derivable_pt_lim (ser n) t (dser n t).
Proof.
  induction n as [|k IH].
  - change (ser 0) with (fct_cte 0). apply derivable_pt_lim_const.
  - change (ser (S k)) with (plus_fct (ser k) (mult_real_fct (2 / INR (2 * k + 1)) (fun t => t ^ (2 * k + 1)))).
    eapply lim_eq.
    + apply derivable_pt_lim_plus; [exact IH | apply derivable_pt_lim_scal, derivable_pt_lim_pow].
    + cbn [dser]. replace (Init.Nat.pred (2 * k + 1)) with (2 * k)%nat by lia.
      assert (0 < INR (2 * k + 1)) by (apply lt_0_INR; lia). field. lra.
Qed.

Lemma dser_closed n t : (1 - t ^ 2) * dser n t = 2 * (1 - t ^ (2 * n)).
Proof.
  induction n as [|k IH].
  - simpl. ring.
  - cbn [dser]. replace (2 * S k)%nat with (2 * k + 2)%nat by lia. rewrite pow_add.
    rewrite Rmult_plus_distr_l, IH. ring.
Qed.

(** [f(t) = ln(1 + t) − ln(1 − t) − ser n t], with [f' = 2·t^(2n)/(1 − t^2)]. *)
Definition gap (n : nat) (t : R) : R := ln (1 + t) - ln (1 - t) - ser n t.

Lemma gap_deriv n t : -1 < t < 1 -> derivable_pt_lim (gap n) t (2 * t ^ (2 * n) / (1 - t ^ 2)).
Proof.
  intros [H1 H2].
  assert (D1 : derivable_pt_lim (fun t => ln (1 + t)) t (/ (1 + t) * 1)).
  { apply (derivable_pt_lim_comp (fun t => 1 + t) ln t 1 (/ (1 + t))).
    - eapply lim_eq; [apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id] | ring].
    - apply derivable_pt_lim_ln. lra. }
  assert (D2 : derivable_pt_lim (fun t => ln (1 - t)) t (/ (1 - t) * (-1))).
  { apply (derivable_pt_lim_comp (fun t => 1 - t) ln t (-1) (/ (1 - t))).
    - eapply lim_eq; [apply derivable_pt_lim_minus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id] | ring].
    - apply derivable_pt_lim_ln. lra. }
  change (gap n) with (minus_fct (minus_fct (fun t => ln (1 + t)) (fun t => ln (1 - t))) (ser n)).
  eapply lim_eq.
  - apply derivable_pt_lim_minus; [apply derivable_pt_lim_minus; [exact D1 | exact D2] | apply ser_deriv].
  - assert (P : 0 < 1 - t ^ 2) by nra.
    apply Rmult_eq_reg_l with (1 - t ^ 2); [ | lra].
    replace ((1 - t ^ 2) * (/ (1 + t) * 1 - / (1 - t) * -1 - dser n t))
      with (2 - (1 - t ^ 2) * dser n t) by (field; lra).
    rewrite dser_closed. field. lra.
Qed.

Lemma gap_0 n : gap n 0 = 0.
Proof.
  unfold gap. rewrite Rplus_0_r, Rminus_0_r, ln_1.
  induction n as [|k IH]; [simpl; ring | ].
  cbn [ser]. replace (2 * k + 1)%nat with (S (2 * k)) by lia. simpl pow at 1.
  rewrite Rmult_0_l, Rmult_0_r. lra.
Qed.

(** The series' partial sums bound [ln((1 + T)/(1 − T))] on both sides. *)
Theorem ln_ser_bounds n T : 0 <= T < 1 ->
  ser n T <= ln (1 + T) - ln (1 - T) <= ser n T + 2 * T ^ (2 * n + 1) / (1 - T ^ 2).
Proof.
  intros [H0 H1].
  destruct (Req_dec T 0) as [Z | Z].
  { subst T. pose proof (gap_0 n) as G. unfold gap in G. rewrite pow_ne_zero by lia. lra. }
  destruct (MVT_cor2 (gap n) (fun t => 2 * t ^ (2 * n) / (1 - t ^ 2)) 0 T ltac:(lra)
              ltac:(intros c Hc; apply gap_deriv; lra)) as [c [E [C0 C1]]].
  rewrite gap_0, Rminus_0_r, Rminus_0_r in E. unfold gap in E.
  assert (Pc : 0 < 1 - c ^ 2) by nra. assert (PT : 0 < 1 - T ^ 2) by nra.
  assert (Lc : 0 <= c ^ (2 * n)) by (apply pow_le; lra).
  assert (Mc : c ^ (2 * n) <= T ^ (2 * n)) by (apply pow_incr; lra).
  assert (Dc : 1 - T ^ 2 <= 1 - c ^ 2) by (assert (c ^ 2 <= T ^ 2) by (apply pow_incr; lra); lra).
  split.
  - assert (0 <= 2 * c ^ (2 * n) / (1 - c ^ 2) * T)
      by (apply Rmult_le_pos; [unfold Rdiv; apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] | lra]).
    lra.
  - assert (Q : 2 * c ^ (2 * n) / (1 - c ^ 2) <= 2 * T ^ (2 * n) / (1 - T ^ 2)).
    { unfold Rdiv. apply Rmult_le_compat; [lra | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
      apply Rinv_le_contravar; lra. }
    replace (2 * T ^ (2 * n + 1) / (1 - T ^ 2)) with (2 * T ^ (2 * n) / (1 - T ^ 2) * T)
      by (rewrite pow_add; field; lra).
    assert (2 * c ^ (2 * n) / (1 - c ^ 2) * T <= 2 * T ^ (2 * n) / (1 - T ^ 2) * T)
      by (apply Rmult_le_compat_r; lra).
    lra.
Qed.

(** * Integer evaluation, rounded outward *)

(** [⌈x / y⌉] for [y > 0]. *)
Definition cdiv (x y : Z) : Z := - (- x / y).

Lemma IZR_div_le x y : (0 < y)%Z -> IZR (x / y) <= IZR x / IZR y.
Proof.
  intros Hy. pose proof (Z.mul_div_le x y Hy) as D. apply IZR_le in D. rewrite mult_IZR in D.
  assert (0 < IZR y) by (apply IZR_lt; exact Hy).
  apply Rmult_le_reg_r with (IZR y); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma IZR_cdiv_ge x y : (0 < y)%Z -> IZR x / IZR y <= IZR (cdiv x y).
Proof.
  intros Hy. unfold cdiv. rewrite opp_IZR. pose proof (IZR_div_le (- x) y Hy) as D.
  rewrite opp_IZR in D. unfold Rdiv in *. lra.
Qed.

Lemma div_nonneg x y : (0 <= x)%Z -> (0 < y)%Z -> (0 <= x / y)%Z.
Proof. intros. apply Z.div_pos; lia. Qed.

(** Terms [k .. k + n − 1] of the series: from [lo <= S·t^(2k+1) <= hi], the
    sums of the terms rounded down and up, and the bound on [S·t^(2(k+n)+1)]
    from above. [p2/q2 = t^2]. *)
Fixpoint sums (p2 q2 : Z) (k n : nat) (lo hi : Z) : Z * Z * Z :=
  match n with
  | O => (0%Z, 0%Z, hi)
  | S n' =>
      let '(sl, su, h) := sums p2 q2 (S k) n' (lo * p2 / q2)%Z (cdiv (hi * p2) q2) in
      ((sl + 2 * lo / Z.of_nat (2 * k + 1))%Z, (su + cdiv (2 * hi) (Z.of_nat (2 * k + 1)))%Z, h)
  end.

Lemma sums_ok (p2 q2 : Z) (t Sc : R) n : forall k lo hi,
  (0 <= p2)%Z -> (0 < q2)%Z -> t ^ 2 = IZR p2 / IZR q2 -> 0 <= t -> 0 < Sc ->
  (0 <= lo)%Z -> IZR lo <= Sc * t ^ (2 * k + 1) <= IZR hi ->
  let '(sl, su, h) := sums p2 q2 k n lo hi in
  IZR sl <= Sc * (ser (k + n) t - ser k t) <= IZR su /\ Sc * t ^ (2 * (k + n) + 1) <= IZR h.
Proof.
  induction n as [|n IH]; intros k lo hi P2 Q2 Tt T0 S0 L0 [L H].
  - cbn [sums]. rewrite Nat.add_0_r. split; [lra | exact H].
  - cbn [sums].
    assert (Qr : 0 < IZR q2) by (apply IZR_lt; exact Q2).
    assert (Pr : 0 <= IZR p2) by (apply IZR_le; exact P2).
    assert (St : Sc * t ^ (2 * S k + 1) = Sc * t ^ (2 * k + 1) * (IZR p2 / IZR q2)).
    { rewrite <- Tt. replace (2 * S k + 1)%nat with (2 * k + 1 + 2)%nat by lia.
      rewrite pow_add. ring. }
    assert (L' : IZR (lo * p2 / q2) <= Sc * t ^ (2 * S k + 1)).
    { apply Rle_trans with (IZR (lo * p2) / IZR q2); [apply IZR_div_le, Q2 | ].
      rewrite St, mult_IZR. unfold Rdiv. rewrite <- Rmult_assoc.
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat, Qr | ].
      apply Rmult_le_compat_r; [exact Pr | exact L]. }
    assert (H' : Sc * t ^ (2 * S k + 1) <= IZR (cdiv (hi * p2) q2)).
    { apply Rle_trans with (IZR (hi * p2) / IZR q2); [ | apply IZR_cdiv_ge, Q2].
      rewrite St, mult_IZR. unfold Rdiv. rewrite <- Rmult_assoc.
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat, Qr | ].
      apply Rmult_le_compat_r; [exact Pr | exact H]. }
    assert (L0' : (0 <= lo * p2 / q2)%Z) by (apply div_nonneg; [nia | exact Q2]).
    specialize (IH (S k) (lo * p2 / q2)%Z (cdiv (hi * p2) q2) P2 Q2 Tt T0 S0 L0' (conj L' H')).
    destruct (sums p2 q2 (S k) n (lo * p2 / q2) (cdiv (hi * p2) q2)) as [[sl su] h].
    destruct IH as [[A1 A2] A3].
    replace (S k + n)%nat with (k + S n)%nat in A1, A2, A3 by lia.
    set (d := Z.of_nat (2 * k + 1)) in *.
    assert (Dp : (0 < d)%Z) by (unfold d; lia).
    assert (Dr : IZR d = INR (2 * k + 1)) by (unfold d; rewrite INR_IZR_INZ; reflexivity).
    assert (Dr0 : 0 < IZR d) by (apply IZR_lt; exact Dp).
    (* the term [k]: 2/(2k+1)·t^(2k+1) *)
    assert (Term : Sc * (ser (S k) t - ser k t) = 2 * (Sc * t ^ (2 * k + 1)) / IZR d).
    { cbn [ser]. rewrite Dr. field. rewrite <- Dr. lra. }
    replace (Sc * (ser (k + S n) t - ser k t))
      with (Sc * (ser (k + S n) t - ser (S k) t) + Sc * (ser (S k) t - ser k t)) by ring.
    rewrite Term. split; [split | exact A3].
    + rewrite plus_IZR. apply Rplus_le_compat; [exact A1 | ].
      apply Rle_trans with (IZR (2 * lo) / IZR d); [apply IZR_div_le, Dp | ].
      rewrite mult_IZR. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | lra].
    + rewrite plus_IZR. apply Rplus_le_compat; [exact A2 | ].
      apply Rle_trans with (IZR (2 * hi) / IZR d); [ | apply IZR_cdiv_ge, Dp].
      rewrite mult_IZR. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | lra].
Qed.

(** [ln(a/b)·2^m] for [a > b > 0], enclosed: [n] terms and the remainder. *)
Definition ln_pos (a b m : Z) (n : nat) : Z * Z :=
  let p := (a - b)%Z in
  let q := (a + b)%Z in
  let lo := (2 ^ m * p / q)%Z in
  let hi := cdiv (2 ^ m * p) q in
  let '(sl, su, h) := sums (p * p) (q * q) 0 n lo hi in
  (sl, (su + cdiv (2 * h * (q * q)) (q * q - p * p))%Z).

Definition ln_bounds (a b m : Z) (n : nat) : Z * Z :=
  if (a =? b)%Z then (0%Z, 0%Z)
  else if (b <? a)%Z then ln_pos a b m n
  else let '(l, u) := ln_pos b a m n in ((- u)%Z, (- l)%Z).

Lemma ln_pos_ok a b m n : (0 < b)%Z -> (b < a)%Z -> (0 <= m)%Z ->
  IZR (fst (ln_pos a b m n)) * bpow radix2 (- m) <= ln (IZR a / IZR b)
    <= IZR (snd (ln_pos a b m n)) * bpow radix2 (- m).
Proof.
  intros Hb Hab Hm. unfold ln_pos. cbv zeta.
  set (p := (a - b)%Z). set (q := (a + b)%Z).
  assert (Pp : (0 < p)%Z) by (unfold p; lia). assert (Pq : (0 < q)%Z) by (unfold q; lia).
  assert (Pr : 0 < IZR p) by (apply IZR_lt; exact Pp). assert (Qr : 0 < IZR q) by (apply IZR_lt; exact Pq).
  set (t := IZR p / IZR q).
  assert (T0 : 0 <= t) by (unfold t; apply Rlt_le, Rdiv_lt_0_compat; lra).
  assert (T1 : t < 1) by (unfold t; apply Rmult_lt_reg_r with (IZR q); [lra | ];
                          unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_l, Rmult_1_r;
                          apply IZR_lt; unfold p, q; lia).
  set (Sc := IZR (2 ^ m)).
  assert (SB : Sc = bpow radix2 m) by (unfold Sc; change (2 ^ m)%Z with (Zpower radix2 m); apply IZR_Zpower; exact Hm).
  assert (S0 : 0 < Sc) by (rewrite SB; apply bpow_gt_0).
  assert (Tt : t ^ 2 = IZR (p * p) / IZR (q * q)) by (unfold t; rewrite !mult_IZR; field; lra).
  assert (Init : IZR (2 ^ m * p / q) <= Sc * t ^ (2 * 0 + 1) <= IZR (cdiv (2 ^ m * p) q)).
  { simpl pow. rewrite Rmult_1_r. split.
    - apply Rle_trans with (IZR (2 ^ m * p) / IZR q); [apply IZR_div_le, Pq | ].
      rewrite mult_IZR. fold Sc. unfold t, Rdiv. lra.
    - apply Rle_trans with (IZR (2 ^ m * p) / IZR q); [ | apply IZR_cdiv_ge, Pq].
      rewrite mult_IZR. fold Sc. unfold t, Rdiv. lra. }
  assert (L0 : (0 <= 2 ^ m * p / q)%Z) by (apply div_nonneg; [apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg | ]; lia | exact Pq]).
  pose proof (sums_ok (p * p) (q * q) t Sc n 0 _ _ ltac:(nia) ltac:(nia) Tt T0 S0 L0 Init) as SO.
  destruct (sums (p * p) (q * q) 0 n (2 ^ m * p / q) (cdiv (2 ^ m * p) q)) as [[sl su] h].
  destruct SO as [[A1 A2] A3]. cbn [fst snd].
  rewrite Nat.add_0_l in A1, A2, A3. cbn [ser] in A1, A2. rewrite Rminus_0_r in A1, A2.
  (* ln(a/b) = ln(1 + t) − ln(1 − t) *)
  assert (Ab : IZR a / IZR b = (1 + t) / (1 - t)).
  { unfold t. assert (Ea : IZR a = (IZR q + IZR p) / 2) by (unfold p, q; rewrite plus_IZR, minus_IZR; field).
    assert (Eb : IZR b = (IZR q - IZR p) / 2) by (unfold p, q; rewrite plus_IZR, minus_IZR; field).
    assert (0 < IZR q - IZR p) by (rewrite <- minus_IZR; apply IZR_lt; unfold p, q; lia).
    rewrite Ea, Eb. field. split; lra. }
  rewrite Ab. unfold Rdiv. rewrite ln_mult, ln_Rinv by (try apply Rinv_0_lt_compat; lra). fold (Rminus (ln (1 + t)) (ln (1 - t))).
  destruct (ln_ser_bounds n t (conj T0 T1)) as [B1 B2].
  assert (Pinv : bpow radix2 (- m) = / Sc) by (rewrite SB, bpow_opp; reflexivity).
  rewrite Pinv. split.
  - apply Rmult_le_reg_l with Sc; [exact S0 | ]. rewrite <- Rmult_assoc, (Rmult_comm Sc), Rmult_assoc, Rinv_r, Rmult_1_r by lra.
    apply Rle_trans with (1 := A1). apply Rmult_le_compat_l; lra.
  - apply Rmult_le_reg_l with Sc; [exact S0 | ]. rewrite <- (Rmult_comm (/ Sc)), <- Rmult_assoc, Rinv_r, Rmult_1_l by lra.
    rewrite plus_IZR.
    assert (Qp : (0 < q * q - p * p)%Z) by nia.
    assert (Rem : Sc * (2 * t ^ (2 * n + 1) / (1 - t ^ 2)) <= IZR (cdiv (2 * h * (q * q)) (q * q - p * p))).
    { apply Rle_trans with (IZR (2 * h * (q * q)) / IZR (q * q - p * p)); [ | apply IZR_cdiv_ge, Qp].
      assert (Om : 1 - t ^ 2 = IZR (q * q - p * p) / IZR (q * q))
        by (rewrite Tt, minus_IZR, !mult_IZR; field; lra).
      assert (Qq : 0 < IZR (q * q)) by (rewrite mult_IZR; nra).
      assert (Qd : 0 < IZR (q * q - p * p)) by (apply IZR_lt; exact Qp).
      rewrite Om, !mult_IZR. rewrite mult_IZR in Qq.
      replace (Sc * (2 * t ^ (2 * n + 1) / (IZR (q * q - p * p) / (IZR q * IZR q))))
        with (2 * (Sc * t ^ (2 * n + 1)) * (IZR q * IZR q) / IZR (q * q - p * p)) by (field; lra).
      unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | ].
      apply Rmult_le_compat_r; [nra | lra]. }
    apply Rle_trans with (Sc * ser n t + Sc * (2 * t ^ (2 * n + 1) / (1 - t ^ 2))); [ | lra].
    rewrite <- Rmult_plus_distr_l. apply Rmult_le_compat_l; lra.
Qed.

(** [L·2^-m <= ln(a/b) <= U·2^-m] for [(L, U) = ln_bounds a b m n]. *)
Theorem ln_bounds_ok a b m n : (0 < a)%Z -> (0 < b)%Z -> (0 <= m)%Z ->
  IZR (fst (ln_bounds a b m n)) * bpow radix2 (- m) <= ln (IZR a / IZR b)
    <= IZR (snd (ln_bounds a b m n)) * bpow radix2 (- m).
Proof.
  intros Ha Hb Hm. unfold ln_bounds.
  destruct (Z.eqb_spec a b) as [E | E].
  { subst b. cbn [fst snd]. unfold Rdiv. rewrite Rinv_r by (apply not_0_IZR; lia). rewrite ln_1. lra. }
  destruct (Z.ltb_spec b a) as [L | L]; [apply ln_pos_ok; lia | ].
  pose proof (ln_pos_ok b a m n Ha ltac:(lia) Hm) as P.
  destruct (ln_pos b a m n) as [l u]. cbn [fst snd] in *. rewrite !opp_IZR.
  assert (Fl : ln (IZR a / IZR b) = - ln (IZR b / IZR a)).
  { assert (0 < IZR a) by (apply IZR_lt; lia). assert (0 < IZR b) by (apply IZR_lt; lia).
    rewrite <- ln_Rinv by (apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
  rewrite Fl. lra.
Qed.
