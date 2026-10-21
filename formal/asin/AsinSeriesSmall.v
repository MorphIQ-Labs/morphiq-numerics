(** asin's series below 1/128: the transcription's evaluation against
    formal/asin/series_tail.g. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel AsinSqrtStep ExpReduction.
Require asin_series_tail.
Open Scope R_scope.

(** The polynomial's coefficients, as the certificate spells them. *)
Definition q0r : R := IZR 6004799503160661 * bpow radix2 (-55).
Definition q1r : R := IZR 5404319552932043 * bpow radix2 (-56).
Definition q2r : R := IZR 6433708013541321 * bpow radix2 (-57).
Definition q3r : R := IZR 554061174771559 * bpow radix2 (-54).

(** The certificate [formal/asin/series_tail.g], at its real variable. *)
Lemma series_tail_certificate x_ : / 2 ^ 28 <= x_ <= 0.0078126 ->
  let zh := rn x_ in
  let uh := rn (zh * zh) in
  let p3 := rn (q2r + rn (uh * q3r)) in
  let p2 := rn (q1r + rn (uh * p3)) in
  let ps := rn (q0r + rn (uh * p2)) in
  let a3 := rn (zh * uh) in
  let tail := rn (a3 * ps) in
  let P := q0r + zh * zh * (q1r + zh * zh * (q2r + zh * zh * q3r)) in
  let Tx := zh * zh * zh * P in
  Rabs ((tail - Tx) / Tx) <= / 2 ^ 51.
Proof.
  intros X zh uh p3 p2 ps a3 tail P Tx.
  assert (G : BND ((tail - Tx) / Tx) (makepairF (Float2 (-1) (-51)) (Float2 1 (-51)))).
  { subst zh uh p3 p2 ps a3 tail P Tx. unfold q0r, q1r, q2r, q3r.
    gappa_goal (asin_series_tail.l1 x_). }
  apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all.
  apply Rabs_le. lra.
Qed.

(** [asin_shifter] is [ExpReduction.shifter], whose rounding is proved. *)
Lemma shifter_bits' : bits_of_b64 shifter = 4843621399236968448%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma asin_shifter_eq : asin_shifter = shifter.
Proof.
  unfold asin_shifter, aw.
  replace (0x4338000000000000)%Z with (bits_of_b64 shifter) by (rewrite shifter_bits'; reflexivity).
  unfold b64_of_bits, bits_of_b64. exact (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl shifter).
Qed.

Lemma sixty_four_val : B asin_64 = 64 /\ finite asin_64.
Proof.
  split.
  - unfold asin_64, aw. rewrite (bits_val 0x4050000000000000 false 4503599627370496%positive 46 eq_refl).
    simpl. field.
  - exact (bits_finite 0x4050000000000000 false 4503599627370496%positive (-46) eq_refl).
Qed.

Lemma znearest_small y : 0 <= y <= / 2 -> Znearest ne y = 0%Z.
Proof.
  intros [H0 H1]. assert (Fl : Zfloor y = 0%Z) by (apply Zfloor_imp; simpl; lra).
  unfold Znearest. rewrite Fl. replace (y - IZR 0) with y by (simpl; ring).
  destruct (Rcompare y (/ 2)) eqn:C.
  - unfold ne. simpl. reflexivity.
  - reflexivity.
  - apply Rcompare_Gt_inv in C. lra.
Qed.

(** [64 z] is exact for a binary64 [z] in [[2^-28, 1/128]]. *)
Lemma times_64_exact z : finite z -> bpow radix2 (-28) <= B z -> B z <= bpow radix2 (-7) ->
  finite (fmul z asin_64) /\ B (fmul z asin_64) = B z * 64.
Proof.
  intros Fz L U. destruct sixty_four_val as [V6 F6].
  assert (Gs : fmtF (B z * bpow radix2 6)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (-27 <= mag radix2 (B z))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq.
      - replace (-27 - 1)%Z with (-28)%Z by reflexivity. exact L.
      - pose proof (bpow_gt_0 radix2 (-28)). lra. }
    unfold emin, prec. lia. }
  assert (Pb : bpow radix2 (-7) = / 128) by (change (-7)%Z with (Zneg 7); rewrite bpow_neg; reflexivity).
  assert (Pc : 0 < bpow radix2 (-28)) by apply bpow_gt_0.
  assert (E6 : B z * B asin_64 = B z * bpow radix2 6).
  { rewrite V6. change (bpow radix2 6) with 64. reflexivity. }
  assert (Bd : bnd 1 0 (B z * B asin_64)).
  { apply bnd0. rewrite V6. apply Rabs_le. change (IZR 1) with 1. rewrite Pb in U. lra. }
  destruct (fmul_bnd 1 0 z asin_64 Fz F6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [F [E _]].
  split; [exact F | ].
  rewrite E, E6, round_generic by (try exact _; exact Gs).
  change (bpow radix2 6) with 64. reflexivity.
Qed.

Lemma zero_val : B asin_zero = 0 /\ finite asin_zero.
Proof. split; vm_compute; reflexivity. Qed.

(** Below 1/128 the index is zero, so the series branch is taken. *)
Lemma index_zero z : finite z -> bpow radix2 (-28) <= B z -> B z <= bpow radix2 (-7) ->
  asin_cmp (fsub (fadd (fmul z asin_64) asin_shifter) asin_shifter) asin_zero = Some Eq.
Proof.
  intros Fz L U. destruct (times_64_exact z Fz L U) as [Fy Ey].
  rewrite asin_shifter_eq.
  assert (Pb : bpow radix2 (-7) = / 128) by (change (-7)%Z with (Zneg 7); rewrite bpow_neg; reflexivity).
  assert (Pc : 0 < bpow radix2 (-28)) by apply bpow_gt_0.
  rewrite Pb in U.
  assert (Hy0 : 0 <= B (fmul z asin_64) <= / 2) by (rewrite Ey; lra).
  assert (Hb50 : Rabs (B (fmul z asin_64)) <= bpow radix2 50).
  { rewrite Rabs_pos_eq by lra. change (bpow radix2 50) with 1125899906842624%R. lra. }
  destruct (shifter_round (fmul z asin_64) Fy Hb50) as [Fn En].
  rewrite (znearest_small _ Hy0) in En. simpl in En.
  destruct zero_val as [Bz Fzero].
  unfold asin_cmp. rewrite (Bcompare_correct 53 1024 _ asin_zero Fn Fzero), En, Bz.
  rewrite Rcompare_Eq; reflexivity.
Qed.

(** The range of a rounded nonnegative product or sum, from the operands'. *)
Lemma mul_range a b ea eb : finite a -> finite b ->
  0 <= B a <= bpow radix2 ea -> 0 <= B b <= bpow radix2 eb -> (-500 <= ea)%Z -> (-500 <= eb)%Z -> (ea <= 0)%Z -> (eb <= 0)%Z ->
  finite (fmul a b) /\ B (fmul a b) = rndF (B a * B b) /\ 0 <= B (fmul a b) <= bpow radix2 (ea + eb).
Proof.
  intros Fa Fb [A0 A1] [B0 B1] Ha Hb Hc Hd.
  assert (Hp : Rabs (B a * B b) <= bpow radix2 (ea + eb)).
  { rewrite Rabs_pos_eq by nra. rewrite bpow_plus. apply Rmult_le_compat; assumption. }
  assert (Hbnd : bnd 1 (ea + eb) (B a * B b)) by (apply bnd_p; change (IZR 1) with 1; rewrite Rmult_1_l; exact Hp).
  destruct (fmul_bnd 1 (ea + eb) a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  split; [exact F | split; [exact E | ]].
  split.
  - rewrite E. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | nra].
  - rewrite E. apply round_le_generic; [exact _ | exact _ | apply fmt_bpow; lia | ].
    rewrite bpow_plus. nra.
Qed.

Lemma add_range a b e : finite a -> finite b -> 0 <= B a -> 0 <= B b -> B a + B b <= bpow radix2 e -> (-1000 <= e)%Z -> (e <= 0)%Z ->
  finite (fadd a b) /\ B (fadd a b) = rndF (B a + B b) /\ 0 <= B (fadd a b) <= bpow radix2 e.
Proof.
  intros Fa Fb A0 B0 Hs He Hf.
  assert (Hbnd : bnd 1 e (B a + B b)).
  { apply bnd_p. change (IZR 1) with 1. rewrite Rmult_1_l. rewrite Rabs_pos_eq by lra. exact Hs. }
  destruct (fadd_bnd 1 e a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  split; [exact F | split; [exact E | ]].
  split.
  - rewrite E. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | lra].
  - rewrite E. apply round_le_generic; [exact _ | exact _ | apply fmt_bpow; lia | exact Hs].
Qed.

Lemma bpow_pos_n (n : nat) : bpow radix2 (Z.of_nat n) = 2 ^ n.
Proof.
  induction n as [|n IH]; [reflexivity | ].
  rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite bpow_plus, IH.
  change (bpow radix2 1) with 2. simpl. ring.
Qed.

Lemma bpow_negn (n : nat) : bpow radix2 (- Z.of_nat n) = / 2 ^ n.
Proof. rewrite bpow_opp, bpow_pos_n. reflexivity. Qed.

(** The polynomial's coefficients as binary64 values. *)
Lemma q0_val : B (aw (nth (Z.to_nat 0%Z) asin_poly0 0%Z)) = q0r /\ finite (aw (nth (Z.to_nat 0%Z) asin_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 0%Z) asin_poly0 0%Z) with 0x3fc5555555555555%Z. unfold aw. split.
  - rewrite (bits_val 0x3fc5555555555555 false 6004799503160661%positive 55 eq_refl).
    unfold q0r. change (-55)%Z with (- Z.of_nat 55)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3fc5555555555555 false 6004799503160661%positive (-55) eq_refl).
Qed.

Lemma q1_val : B (aw (nth (Z.to_nat 1%Z) asin_poly0 0%Z)) = q1r /\ finite (aw (nth (Z.to_nat 1%Z) asin_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 1%Z) asin_poly0 0%Z) with 0x3fb33333333488cb%Z. unfold aw. split.
  - rewrite (bits_val 0x3fb33333333488cb false 5404319552932043%positive 56 eq_refl).
    unfold q1r. change (-56)%Z with (- Z.of_nat 56)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3fb33333333488cb false 5404319552932043%positive (-56) eq_refl).
Qed.

Lemma q2_val : B (aw (nth (Z.to_nat 2%Z) asin_poly0 0%Z)) = q2r /\ finite (aw (nth (Z.to_nat 2%Z) asin_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 2%Z) asin_poly0 0%Z) with 0x3fa6db6c60bc57c9%Z. unfold aw. split.
  - rewrite (bits_val 0x3fa6db6c60bc57c9 false 6433708013541321%positive 57 eq_refl).
    unfold q2r. change (-57)%Z with (- Z.of_nat 57)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3fa6db6c60bc57c9 false 6433708013541321%positive (-57) eq_refl).
Qed.

Lemma q3_val : B (aw (nth (Z.to_nat 3%Z) asin_poly0 0%Z)) = q3r /\ finite (aw (nth (Z.to_nat 3%Z) asin_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 3%Z) asin_poly0 0%Z) with 0x3f9f7ea6b818f670%Z. unfold aw. split.
  - rewrite (bits_val 0x3f9f7ea6b818f670 false 8864978796344944%positive 58 eq_refl).
    unfold q3r. change (-54)%Z with (- Z.of_nat 54)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3f9f7ea6b818f670 false 8864978796344944%positive (-58) eq_refl).
Qed.

(** The coefficients' ranges. *)
Lemma qr_facts : 0 <= q0r <= 0.17 /\ 0 <= q1r <= 0.08 /\ 0 <= q2r <= 0.05 /\ 0 <= q3r <= bpow radix2 (-5).
Proof.
  unfold q0r, q1r, q2r, q3r.
  change (-55)%Z with (- Z.of_nat 55)%Z. change (-56)%Z with (- Z.of_nat 56)%Z.
  change (-57)%Z with (- Z.of_nat 57)%Z. change (-54)%Z with (- Z.of_nat 54)%Z.
  rewrite !bpow_negn. change (-5)%Z with (- Z.of_nat 5)%Z. rewrite bpow_negn.
  simpl. repeat split; try (apply Rmult_le_pos; [apply IZR_le; lia | apply Rlt_le, Rinv_0_lt_compat; apply pow_lt; lra]);
  unfold Rdiv; lra.
Qed.

Lemma rn_id x : fmtF x -> rn x = x.
Proof. intros F. change (rn x) with (rndF x). apply round_generic; [exact _ | exact F]. Qed.

Ltac bnum n := change (- Z.of_nat n)%Z with (- Z.of_nat n)%Z.

Lemma bm1 : bpow radix2 (-1) = / 2.
Proof. rewrite (bpow_negn 1 : bpow radix2 (-1) = / 2 ^ 1). simpl. field. Qed.
Lemma bm2 : bpow radix2 (-2) = / 4.
Proof. rewrite (bpow_negn 2 : bpow radix2 (-2) = / 2 ^ 2). simpl. field. Qed.
Lemma bm3 : bpow radix2 (-3) = / 8.
Proof. rewrite (bpow_negn 3 : bpow radix2 (-3) = / 2 ^ 3). simpl. field. Qed.
Lemma bm5 : bpow radix2 (-5) = / 32.
Proof. rewrite (bpow_negn 5 : bpow radix2 (-5) = / 2 ^ 5). simpl. field. Qed.
Lemma bm7 : bpow radix2 (-7) = / 128.
Proof. rewrite (bpow_negn 7 : bpow radix2 (-7) = / 2 ^ 7). simpl. field. Qed.
Lemma bm14 : bpow radix2 (-14) = / 16384.
Proof. rewrite (bpow_negn 14 : bpow radix2 (-14) = / 2 ^ 14). simpl. field. Qed.
Lemma bm16 : bpow radix2 (-16) = / 65536.
Proof. rewrite (bpow_negn 16 : bpow radix2 (-16) = / 2 ^ 16). simpl. field. Qed.
Lemma bm17 : bpow radix2 (-17) = / 131072.
Proof. rewrite (bpow_negn 17 : bpow radix2 (-17) = / 2 ^ 17). simpl. field. Qed.
Lemma bm19 : bpow radix2 (-19) = / 524288.
Proof. rewrite (bpow_negn 19 : bpow radix2 (-19) = / 2 ^ 19). simpl. field. Qed.
Lemma bm21 : bpow radix2 (-21) = / 2097152.
Proof. rewrite (bpow_negn 21 : bpow radix2 (-21) = / 2 ^ 21). simpl. field. Qed.

(** The series branch's evaluation: the double-word result is the exact sum of
    the argument and the exact cubic term, with the tail's relative error and
    [add_f64]'s. *)
Theorem series_small_eval zh zl : finite zh -> finite zl ->
  bpow radix2 (-28) <= B zh -> B zh <= bpow radix2 (-7) ->
  B zh = rndF (B zh + B zl) -> Rabs (B zl) <= B zh / 2 ->
  exists h l, asin_series zh zl = (h, l) /\ finite h /\ finite l /\
    exists ec ea, Rabs ec <= / 2 ^ 51 /\ Rabs ea <= / 2 ^ 104 /\
      let Tx := B zh * B zh * B zh * (q0r + B zh * B zh * (q1r + B zh * B zh * (q2r + B zh * B zh * q3r))) in
      B h + B l = (B zh + B zl + Tx * (1 + ec)) * (1 + ea).
Proof.
  intros Fh Fl L U Dw Hl.
  unfold asin_series. cbv zeta. rewrite (index_zero zh Fh L U). cbv iota.
  destruct q0_val as [E0 F0]. destruct q1_val as [E1 F1]. destruct q2_val as [E2 F2]. destruct q3_val as [E3 F3].
  destruct qr_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]].
  set (Q0 := aw (nth (Z.to_nat 0%Z) asin_poly0 0%Z)) in *.
  set (Q1 := aw (nth (Z.to_nat 1%Z) asin_poly0 0%Z)) in *.
  set (Q2 := aw (nth (Z.to_nat 2%Z) asin_poly0 0%Z)) in *.
  set (Q3 := aw (nth (Z.to_nat 3%Z) asin_poly0 0%Z)) in *.
  assert (Hz0 : 0 <= B zh) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  destruct (mul_range zh zh (-7) (-7) Fh Fh (conj Hz0 U) (conj Hz0 U) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fz2 [Ez2 [Z20 Z21]]].
  change (-7 + -7)%Z with (-14)%Z in Z21. set (z2 := fmul zh zh) in *.
  (* m3 = z2 q3 *)
  destruct (mul_range z2 Q3 (-14) (-5) Fz2 F3 (conj Z20 Z21) ltac:(rewrite E3; split; assumption) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm3 [Em3 [M30 M31]]]. set (m3 := fmul z2 Q3) in *.
  change (-14 + -5)%Z with (-19)%Z in M31. pose proof M31 as M31n; rewrite bm19 in M31n.
  (* p3 = q2 + m3 *)
  destruct (add_range Q2 m3 (-3) F2 Fm3 ltac:(rewrite E2; lra) M30 ltac:(rewrite E2, bm3; lra) ltac:(lia) ltac:(lia)) as [Fp3 [Ep3 [P30 P31]]]. set (p3 := fadd Q2 m3) in *.
  pose proof P31 as P31n; rewrite bm3 in P31n.
  (* m2 = z2 p3 *)
  destruct (mul_range z2 p3 (-14) (-3) Fz2 Fp3 (conj Z20 Z21) (conj P30 P31) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm2 [Em2 [M20 M21]]]. set (m2 := fmul z2 p3) in *.
  change (-14 + -3)%Z with (-17)%Z in M21. pose proof M21 as M21n; rewrite bm17 in M21n.
  (* p2 = q1 + m2 *)
  destruct (add_range Q1 m2 (-2) F1 Fm2 ltac:(rewrite E1; lra) M20 ltac:(rewrite E1, bm2; lra) ltac:(lia) ltac:(lia)) as [Fp2 [Ep2 [P20 P21]]]. set (p2 := fadd Q1 m2) in *.
  pose proof P21 as P21n; rewrite bm2 in P21n.
  (* m1 = z2 p2 *)
  destruct (mul_range z2 p2 (-14) (-2) Fz2 Fp2 (conj Z20 Z21) (conj P20 P21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm1 [Em1 [M10 M11]]]. set (m1 := fmul z2 p2) in *.
  change (-14 + -2)%Z with (-16)%Z in M11. pose proof M11 as M11n; rewrite bm16 in M11n.
  (* ps = q0 + m1 *)
  destruct (add_range Q0 m1 (-1) F0 Fm1 ltac:(rewrite E0; lra) M10 ltac:(rewrite E0, bm1; lra) ltac:(lia) ltac:(lia)) as [Fps [Eps [Ps0 Ps1]]]. set (ps := fadd Q0 m1) in *.
  pose proof Ps1 as Ps1n; rewrite bm1 in Ps1n.
  (* a3 = zh z2 *)
  destruct (mul_range zh z2 (-7) (-14) Fh Fz2 (conj Hz0 U) (conj Z20 Z21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fa3 [Ea3 [A30 A31]]]. set (a3 := fmul zh z2) in *.
  change (-7 + -14)%Z with (-21)%Z in A31.
  (* tail = a3 ps *)
  destruct (mul_range a3 ps (-21) (-1) Fa3 Fps (conj A30 A31) (conj Ps0 Ps1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Ftail [Etail [T0 T1]]].
  change (-21 + -1)%Z with (-22)%Z in T1. set (tail := fmul a3 ps) in *.
  (* the tail's certificate *)
  assert (HX : rn (B zh) = B zh) by (apply rn_id; apply B_fmt).
  assert (X1 : / 2 ^ 28 <= B zh <= 0.0078126).
  { split.
    - change (-28)%Z with (- Z.of_nat 28)%Z in L. rewrite bpow_negn in L. exact L.
    - rewrite bm7 in U. lra. }
  pose proof (series_tail_certificate (B zh) X1) as C. cbv zeta in C. rewrite HX in C.
  assert (Htail : B tail = rn (rn (B zh * rn (B zh * B zh)) * rn (q0r + rn (rn (B zh * B zh) * rn (q1r + rn (rn (B zh * B zh) * rn (q2r + rn (rn (B zh * B zh) * q3r)))))))).
  { rewrite Etail, Ea3, Eps, Em1, Ep2, Em2, Ep3, Em3, Ez2, E0, E1, E2, E3. reflexivity. }
  rewrite <- Htail in C.
  set (X := B zh) in *.
  assert (Pz : 0 <= q1r + X * X * (q2r + X * X * q3r)).
  { assert (0 <= X * X) by nra. assert (0 <= X * X * q3r) by nra.
    assert (0 <= q2r + X * X * q3r) by lra. assert (0 <= X * X * (q2r + X * X * q3r)) by nra. lra. }
  assert (Pp : 0 < q0r + X * X * (q1r + X * X * (q2r + X * X * q3r))).
  { assert (0 < q0r) by (unfold q0r; apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
    assert (0 <= X * X * (q1r + X * X * (q2r + X * X * q3r))) by nra. lra. }
  assert (Xp : 0 < X) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  assert (Txp : 0 < X * X * X * (q0r + X * X * (q1r + X * X * (q2r + X * X * q3r)))) by (repeat apply Rmult_lt_0_compat; assumption).
  set (Tx := X * X * X * (q0r + X * X * (q1r + X * X * (q2r + X * X * q3r)))) in *.
  (* the final sum *)
  assert (Hzl : Rabs (B zl) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. apply Rle_trans with (X / 2); [exact Hl | pose proof (bpow_gt_0 radix2 (-7)); lra]. }
  assert (Hzh : Rabs X <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. rewrite Rabs_pos_eq by lra. exact U. }
  assert (Ht : Rabs (B tail) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-22)); [ | apply bpow_le; lia]. rewrite Rabs_pos_eq by lra. exact T1. }
  pose proof (add_f64_ieee zh zl tail Fh Fl Ftail Dw Hzh Hzl Ht) as AF.
  destruct (add_f64_64 zh zl tail) as [h l] eqn:Ead. cbv iota in AF. destruct AF as [Fh' [Fl' Bd]].
  exists h, l. split; [reflexivity | ]. split; [exact Fh' | ]. split; [exact Fl' | ].
  set (Xs := X + B zl + B tail) in *.
  assert (Hxs : 0 < Xs).
  { unfold Xs. apply Rabs_le_inv in Hl. pose proof (Rabs_pos (B tail)). 
    assert (0 <= B tail) by (rewrite Rabs_pos_eq in * by lra; lra). lra. }
  exists ((B tail - Tx) / Tx), ((B h + B l - Xs) / Xs). split; [ | split].
  - exact C.
  - apply Rle_trans with (1 := Bd). replace (- prec)%Z with (-53)%Z by (unfold prec; reflexivity). rewrite bp53.
    assert (p104 : 2 ^ 104 = 20282409603651670423947251286016) by (simpl; ring). rewrite p104. 
    assert (Hs : (/ 9007199254740992) ^ 2 = / 81129638414606681695789005144064) by (simpl; field). rewrite Hs. lra.
  - cbv zeta.
    assert (Tx0 : Tx <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Txp).
    assert (Xs0 : Xs <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Hxs).
    assert (Hec : Tx * (1 + (B tail - Tx) / Tx) = B tail) by (field; exact Tx0).
    replace (X + B zl + Tx * (1 + (B tail - Tx) / Tx)) with Xs by (unfold Xs; lra).
    field. exact Xs0.
Qed.
