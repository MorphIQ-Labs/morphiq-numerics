(** Accurate radix-log reconstruction (docs/log2.md, sections 4 and 5).
    These are the Q128 operation sequences in log2/mod.rs. The reconstruction
    theorems consume the shared logarithm's 2^-123 relative bound; they do not
    establish the public fast-path decisions or whole-entry composition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Q128 QSpec.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import ExpAccurate LnAccurate LogRadixConstants.
Open Scope R_scope.

Definition scale10 a := Q128.mul a inv_ln10_q.
Definition reconstruct2 e a :=
  let w := Q128.mul a inv_ln2_q in
  if (e =? 0)%Z then w else Q128.add (qf (fe e)) w.

Definition log2_acc x :=
  let '(e, i, y, r) := LnReduction.reduce x in
  reconstruct2 e (acc_value 0 i r (LnReduction.z_exact y r)).
Definition log10_acc x := scale10 (ln_acc x).

Lemma relative_error a v eps : 0 <= eps ->
  Rabs (a - v) <= eps * Rabs v ->
  exists d, Rabs d <= eps /\ a = v * (1 + d).
Proof.
  intros E H. destruct (Req_dec v 0) as [V | V].
  - subst v. rewrite Rabs_R0, Rmult_0_r, Rminus_0_r in H.
    apply Rabs_le_inv in H. exists 0. split; [rewrite Rabs_R0; exact E | lra].
  - exists ((a - v) / v). split; [ | field; exact V].
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact V.
    apply Rmult_le_reg_r with (Rabs v); [apply Rabs_pos_lt, V | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, V). exact H.
Qed.

(** A common bound for both radix reciprocals, including a zero input. *)
Theorem scale_bound a c v b : NZ a -> NZ c -> 0 < b ->
  Rabs (Q128.qval a - v) <= / 2 ^ 123 * Rabs v ->
  Rabs (Q128.qval c * b - 1) <= / 2 ^ 127 ->
  NZ (Q128.mul a c) /\
  Rabs (Q128.qval (Q128.mul a c) - v / b) <= 5 / 2 ^ 125 * Rabs (v / b).
Proof.
  intros Na Nc Pb Ha Hc.
  destruct (relative_error (Q128.qval a) v (/ 2 ^ 123) ltac:(left; interval) Ha) as [da [Da Va]].
  set (dc := Q128.qval c * b - 1) in *.
  assert (Vc : Q128.qval c = / b * (1 + dc)) by (unfold dc; field; lra).
  destruct (mul_any a c Na Nc) as [N [m [M V]]].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in M.
  rewrite bpow_m in M. split; [exact N | ].
  rewrite V, Va, Vc.
  replace (v * (1 + da) * (/ b * (1 + dc)) * (1 + m) - v / b)
    with ((v / b) * ((1 + da) * (1 + dc) * (1 + m) - 1)) by (unfold Rdiv; ring).
  rewrite Rabs_mult, Rmult_comm.
  apply Rmult_le_compat_r; [apply Rabs_pos | ].
  apply Rabs_le_inv in Da. apply Rabs_le_inv in Hc.
  interval with (i_prec 160).
Qed.

Theorem scale10_bound a v : NZ a ->
  Rabs (Q128.qval a - v) <= / 2 ^ 123 * Rabs v ->
  NZ (scale10 a) /\
  Rabs (Q128.qval (scale10 a) - v / ln 10) <= / 2 ^ 122 * Rabs (v / ln 10).
Proof.
  intros Na H. destruct (scale_bound a inv_ln10_q v (ln 10) Na
    (or_intror inv_ln10_q_normalized) ltac:(interval) H inv_ln10_q_residual) as [N E].
  split; [exact N | ]. apply Rle_trans with (1 := E).
  apply Rmult_le_compat_r; [apply Rabs_pos | interval].
Qed.

(** For a nonzero integer exponent and |w| <= 0.51, cancellation cannot
    amplify w by more than 1.1. This covers the documented reduced range. *)
Lemma reconstruction_ratios e w : e <> 0%Z -> Rabs w <= 0.51 ->
  Rabs w <= 1.1 * Rabs (IZR e + w) /\
  Rabs (IZR e) <= 3 * Rabs (IZR e + w).
Proof.
  intros Ne W.
  assert (E : 1 <= Rabs (IZR e)).
  { rewrite <- abs_IZR. change 1 with (IZR 1). apply IZR_le. lia. }
  pose proof (Rabs_triang_inv (IZR e) (-w)) as T.
  rewrite Rabs_Ropp in T. replace (IZR e - -w) with (IZR e + w) in T by ring.
  split; lra.
Qed.

Theorem reconstruct2_bound e a ly : (Z.abs e <= 1074)%Z -> NZ a ->
  Rabs (Q128.qval a - ly) <= / 2 ^ 123 * Rabs ly ->
  Rabs (ly / ln 2) <= 0.51 ->
  NZ (reconstruct2 e a) /\
  Rabs (Q128.qval (reconstruct2 e a) - (IZR e + ly / ln 2))
    <= / 2 ^ 122 * Rabs (IZR e + ly / ln 2).
Proof.
  intros He Na Ha Hw.
  destruct (scale_bound a inv_ln2_q ly (ln 2) Na
    (or_intror inv_ln2_q_normalized) ltac:(interval) Ha inv_ln2_q_residual) as [Nw Ew].
  unfold reconstruct2. destruct (Z.eqb_spec e 0) as [E0 | E0].
  - subst e. rewrite Rplus_0_l. split; [exact Nw | ].
    apply Rle_trans with (1 := Ew). apply Rmult_le_compat_r; [apply Rabs_pos | interval].
  - destruct (fe_ok e ltac:(lia)) as [Fe Ve].
    assert (Vq : Q128.qval (qf (fe e)) = IZR e) by (unfold qf; rewrite from_f64_b64 by exact Fe; exact Ve).
    destruct (add_any (qf (fe e)) _ (from_f64_nz _) Nw) as [Ns Es].
    rewrite Vq in Es.
    change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in Es.
    rewrite bpow_m in Es.
    set (w := ly / ln 2) in *.
    set (p := Q128.qval (Q128.mul a inv_ln2_q)) in *.
    set (t := IZR e + w).
    destruct (reconstruction_ratios e w E0 Hw) as [Wr Er]. fold t in Wr, Er.
    assert (P : Rabs p <= 3 * Rabs t).
    { pose proof (Rabs_triang_inv p w).
      assert (0 <= 5 / 2 ^ 125 <= 1) by (split; interval).
      pose proof (Rabs_pos w). pose proof (Rabs_pos t). nra. }
    assert (S : Rabs (Q128.qval (Q128.add (qf (fe e)) (Q128.mul a inv_ln2_q)) - (IZR e + p))
       <= / 2 ^ 126 * (3 * Rabs t)).
    { apply Rle_trans with (1 := Es). apply Rmult_le_compat_l; [left; interval | ].
      apply Rmax_lub; assumption. }
    split; [exact Ns | ]. fold w t p.
    replace (Q128.qval (Q128.add (qf (fe e)) (Q128.mul a inv_ln2_q)) - t)
      with ((Q128.qval (Q128.add (qf (fe e)) (Q128.mul a inv_ln2_q)) - (IZR e + p)) + (p - w))
      by (unfold t; ring).
    apply Rle_trans with (1 := Rabs_triang _ _).
    assert (K : / 2 ^ 126 * 3 + 5 / 2 ^ 125 * 1.1 <= / 2 ^ 122) by interval.
    assert (P0 : 0 <= 5 / 2 ^ 125) by (left; interval).
    pose proof (Rabs_pos t). nra.
Qed.

(** The shared ln theorem discharges the scaling premise for log10's
    accurate path on every finite positive input except the screened one. *)
Theorem log10_acc_bound x : finite x -> 0 < B x -> B x <> 1 ->
  NZ (log10_acc x) /\
  Rabs (Q128.qval (log10_acc x) - ln (B x) / ln 10)
    <= / 2 ^ 122 * Rabs (ln (B x) / ln 10).
Proof.
  intros Fx Px N1. destruct (ln_acc_ok x Fx Px N1) as [N [E _]].
  exact (scale10_bound _ _ (or_intror N) E).
Qed.

(** The exponent-free shared ln evaluator, including y=1. *)
Lemma reduced_ln_bound i y : (i < 128)%nat -> finite y ->
  LnTables.ln_lo i <= B y < LnTables.ln_hi i ->
  Binary64.Grid.on_grid (-53) (B y) ->
  NZ (acc_value 0 i (LnTables.ln_r i) (LnReduction.z_exact y (LnTables.ln_r i))) /\
  Rabs (Q128.qval (acc_value 0 i (LnTables.ln_r i) (LnReduction.z_exact y (LnTables.ln_r i))) - ln (B y))
    <= / 2 ^ 123 * Rabs (ln (B y)).
Proof.
  intros Hi Fy Iy Gy.
  destruct (LnReduction.z_exact_ok y i Hi Fy Iy) as [Nz Vz].
  pose proof (LnReduction.z_range y i Hi Iy Gy) as [_ [Zb _]].
  destruct (LnReduction.ln_range i Hi) as [L1 [L2 _]].
  destruct (Req_dec (B y) 1) as [Y1 | Y1].
  - assert (I0 : i = 0%nat).
    { unfold LnTables.ln_lo, LnTables.ln_hi in Iy. rewrite Y1 in Iy.
      destruct (i <? 53)%nat.
      - assert (INR i = INR 0) by (simpl; pose proof (pos_INR i); lra).
        apply INR_eq in H. exact H.
      - assert (INR (S i) <= INR 128) by (apply le_INR; lia).
        replace (INR 128) with 128 in H by (rewrite INR_IZR_INZ; reflexivity). lra. }
    subst i.
    assert (R1 : B (LnTables.ln_r 0) = 1) by exact (proj2 LnReduction.c_one_ok).
    assert (Fr : finite (LnTables.ln_r 0)) by exact (proj1 LnReduction.c_one_ok).
    assert (Cmp : Flocq.IEEE754.Binary.Bcompare 53 1024 (LnTables.ln_r 0) LnReduction.c_one = Some Eq)
      by (apply (proj2 (cmp_one _ Fr)); exact R1).
    assert (Z0 : Q128.qval (LnReduction.z_exact y (LnTables.ln_r 0)) = 0) by (rewrite Vz, Y1, R1; ring).
    destruct (series_ok _ Nz ltac:(rewrite Z0, Rabs_R0; lra)) as [Ng _].
    destruct (mul_any _ _ Nz Ng) as [N [m [_ Vm]]].
    unfold acc_value. cbn [Z.eqb]. rewrite Cmp.
    change (NZ (lnz (LnReduction.z_exact y (LnTables.ln_r 0))) /\
      Rabs (Q128.qval (lnz (LnReduction.z_exact y (LnTables.ln_r 0))) - ln (B y))
        <= / 2 ^ 123 * Rabs (ln (B y))).
    split; [exact N | ]. unfold lnz. rewrite Vm, Z0, Y1, ln_1.
    rewrite !Rmult_0_l, Rminus_0_r, !Rabs_R0, Rmult_0_r. lra.
  - assert (Nl : 0 * ln 2 + ln (B y) <> 0).
    { intros H. apply Y1. rewrite <- (exp_ln (B y)) by lra.
      replace (ln (B y)) with 0 by lra. apply exp_0. }
    destruct (acc_value_ok 0 i (B y) (LnReduction.z_exact y (LnTables.ln_r i)) Hi ltac:(lia)
      ltac:(assert (0 < / 2 ^ 52) by interval; lra)
      Nz ltac:(rewrite Vz; lra) ltac:(intros _ _; exact Vz)
      ltac:(rewrite Vz; replace (1 + (B y * B (LnTables.ln_r i) - 1)) with (B y * B (LnTables.ln_r i)) by ring;
            rewrite Rminus_diag_eq, Rabs_R0, Rmult_0_l by reflexivity;
            apply Rmult_le_pos; [left; interval | apply Rabs_pos]) Nl) as [N E].
    replace (IZR 0 * ln 2 + ln (B y)) with (ln (B y)) in E by ring.
    split; [right; exact N | exact E].
Qed.

Theorem log2_acc_bound x : finite x -> 0 < B x ->
  NZ (log2_acc x) /\
  Rabs (Q128.qval (log2_acc x) - ln (B x) / ln 2)
    <= / 2 ^ 122 * Rabs (ln (B x) / ln 2).
Proof.
  intros Fx Px. pose proof (LnReduction.reduce_ok x Fx Px) as R.
  unfold log2_acc. destruct (LnReduction.reduce x) as [[[e i] y] r].
  destruct R as [Hi [Er [Fy [Iy [Gy [Ex He]]]]]]. subst r.
  destruct (reduced_ln_bound i y Hi Fy Iy Gy) as [Na Ha].
  destruct (LnReduction.ln_range i Hi) as [L1 [L2 _]].
  assert (L : ln (B x) / ln 2 = IZR e + ln (B y) / ln 2).
  { rewrite Ex, ln_pow2 by lra. field. assert (0 < ln 2) by interval. lra. }
  rewrite L. apply reconstruct2_bound; [lia | exact Na | exact Ha | ].
  assert (Yrange : 0.70703125 <= B y <= 1.4140625) by lra.
  interval with (i_prec 100).
Qed.
