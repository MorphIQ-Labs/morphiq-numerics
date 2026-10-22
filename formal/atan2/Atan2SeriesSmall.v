(** atan2's series below 1/128: the transcription's evaluation against
    formal/atan2/series_tail.g, and its tiny-argument case. The kernel evaluates
    [P = -Q] with the coefficients' signs, which is [-Q]'s operations negated;
    rounding to nearest is odd, so every intermediate is the negation of the
    certificate's. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
From Interval Require Import Tactic.
Require Import Ln1pLemmas StageGappa AsinTables AsinKernel AsinSqrtStep AsinNormal ExpReduction AsinSeriesSmall AsinSegment
  Atan2Tables Atan2Kernel.
Require atan2_series_tail.
Open Scope R_scope.

(** The polynomial's coefficient magnitudes, as the certificate spells them. *)
Definition aq0 : R := IZR 6004799503160661 * bpow radix2 (-54).
Definition aq1 : R := IZR 7205759403705275 * bpow radix2 (-55).
Definition aq2 : R := IZR 5146968125827051 * bpow radix2 (-55).
Definition aq3 : R := IZR 7952018364870011 * bpow radix2 (-56).

(** [Q(u) = q0 - u (q1 - u (q2 - u q3))], so that [atan z = z - z^3 Q(z^2)]. *)
Definition aQ (u : R) : R := aq0 - u * (aq1 - u * (aq2 - u * aq3)).

(** The certificate [formal/atan2/series_tail.g], at its real variable. *)
Lemma atan_series_tail_certificate x_ : / 2 ^ 100 <= x_ <= 0.0078126 ->
  let zh := rn x_ in
  let uh := rn (zh * zh) in
  let p3 := rn (aq2 - rn (uh * aq3)) in
  let p2 := rn (aq1 - rn (uh * p3)) in
  let ps := rn (aq0 - rn (uh * p2)) in
  let a3 := rn (zh * uh) in
  let tail := rn (a3 * ps) in
  let P := aq0 - zh * zh * (aq1 - zh * zh * (aq2 - zh * zh * aq3)) in
  let Tx := zh * zh * zh * P in
  Rabs ((tail - Tx) / Tx) <= / 2 ^ 51.
Proof.
  intros X zh uh p3 p2 ps a3 tail P Tx.
  assert (G : BND ((tail - Tx) / Tx) (makepairF (Float2 (-1) (-51)) (Float2 1 (-51)))).
  { subst zh uh p3 p2 ps a3 tail P Tx. unfold aq0, aq1, aq2, aq3.
    gappa_goal (atan2_series_tail.l1 x_). }
  apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all.
  apply Rabs_le. lra.
Qed.

(** The coefficients' ranges. *)
Lemma aq_facts : 0.3333 <= aq0 <= 0.3334 /\ 0.1999 <= aq1 <= 0.2 /\ 0.1428 <= aq2 <= 0.1429 /\ 0.1103 <= aq3 <= 0.1104.
Proof. unfold aq0, aq1, aq2, aq3. bpow_num. repeat split; interval with (i_prec 100). Qed.

(** The table words: magnitudes with the signs of [-Q]'s terms. *)
Lemma aq0_val : B (aw (nth (Z.to_nat 0%Z) atan2_poly0 0%Z)) = - aq0 /\ finite (aw (nth (Z.to_nat 0%Z) atan2_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 0%Z) atan2_poly0 0%Z) with 0xbfd5555555555555%Z. unfold aw. split.
  - rewrite (bits_val 0xbfd5555555555555 true 6004799503160661%positive 54 eq_refl).
    unfold aq0. change (-54)%Z with (- Z.of_nat 54)%Z. rewrite bpow_negn. simpl (cond_Zopp true _).
    replace (IZR (Z.neg 6004799503160661)) with (- IZR (Z.pos 6004799503160661)) by (rewrite <- opp_IZR; reflexivity). field.
  - exact (bits_finite 0xbfd5555555555555 true 6004799503160661%positive (-54) eq_refl).
Qed.

Lemma aq1_val : B (aw (nth (Z.to_nat 1%Z) atan2_poly0 0%Z)) = aq1 /\ finite (aw (nth (Z.to_nat 1%Z) atan2_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 1%Z) atan2_poly0 0%Z) with 0x3fc99999999843bb%Z. unfold aw. split.
  - rewrite (bits_val 0x3fc99999999843bb false 7205759403705275%positive 55 eq_refl).
    unfold aq1. change (-55)%Z with (- Z.of_nat 55)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3fc99999999843bb false 7205759403705275%positive (-55) eq_refl).
Qed.

Lemma aq2_val : B (aw (nth (Z.to_nat 2%Z) atan2_poly0 0%Z)) = - aq2 /\ finite (aw (nth (Z.to_nat 2%Z) atan2_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 2%Z) atan2_poly0 0%Z) with 0xbfc24923e6cf67eb%Z. unfold aw. split.
  - rewrite (bits_val 0xbfc24923e6cf67eb true 5146968125827051%positive 55 eq_refl).
    unfold aq2. change (-55)%Z with (- Z.of_nat 55)%Z. rewrite bpow_negn. simpl (cond_Zopp true _).
    replace (IZR (Z.neg 5146968125827051)) with (- IZR (Z.pos 5146968125827051)) by (rewrite <- opp_IZR; reflexivity). field.
  - exact (bits_finite 0xbfc24923e6cf67eb true 5146968125827051%positive (-55) eq_refl).
Qed.

Lemma aq3_val : B (aw (nth (Z.to_nat 3%Z) atan2_poly0 0%Z)) = aq3 /\ finite (aw (nth (Z.to_nat 3%Z) atan2_poly0 0%Z)).
Proof.
  change (nth (Z.to_nat 3%Z) atan2_poly0 0%Z) with 0x3fbc40518de2ad7b%Z. unfold aw. split.
  - rewrite (bits_val 0x3fbc40518de2ad7b false 7952018364870011%positive 56 eq_refl).
    unfold aq3. change (-56)%Z with (- Z.of_nat 56)%Z. rewrite bpow_negn. simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3fbc40518de2ad7b false 7952018364870011%positive (-56) eq_refl).
Qed.

(** [64 z] is exact for a binary64 [z] in [[2^-900, 2^-7]], and its index is zero. *)
Lemma times_64_exact_a z : finite z -> bpow radix2 (-900) <= B z -> B z <= bpow radix2 (-7) ->
  finite (fmul z asin_64) /\ B (fmul z asin_64) = B z * 64.
Proof.
  intros Fz L U. destruct sixty_four_val as [V6 F6].
  assert (Gs : fmtF (B z * bpow radix2 6)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (-899 <= mag radix2 (B z))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq.
      - replace (-899 - 1)%Z with (-900)%Z by reflexivity. exact L.
      - pose proof (bpow_gt_0 radix2 (-900)). lra. }
    unfold emin, prec. lia. }
  assert (Pb : bpow radix2 (-7) = / 128) by (change (-7)%Z with (Zneg 7); rewrite bpow_neg; reflexivity).
  assert (Pc : 0 < bpow radix2 (-900)) by apply bpow_gt_0.
  assert (E6 : B z * B asin_64 = B z * bpow radix2 6).
  { rewrite V6. change (bpow radix2 6) with 64. reflexivity. }
  assert (Bd : bnd 1 0 (B z * B asin_64)).
  { apply bnd0. rewrite V6. apply Rabs_le. change (IZR 1) with 1. rewrite Pb in U. lra. }
  destruct (fmul_bnd 1 0 z asin_64 Fz F6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [F [E _]].
  split; [exact F | ].
  rewrite E, E6, round_generic by (try exact _; exact Gs).
  change (bpow radix2 6) with 64. reflexivity.
Qed.

Lemma index_zero_a z : finite z -> bpow radix2 (-900) <= B z -> B z <= bpow radix2 (-7) ->
  asin_cmp (fsub (fadd (fmul z asin_64) asin_shifter) asin_shifter) asin_zero = Some Eq.
Proof.
  intros Fz L U. destruct (times_64_exact_a z Fz L U) as [Fy Ey].
  rewrite asin_shifter_eq.
  assert (Pb : bpow radix2 (-7) = / 128) by (change (-7)%Z with (Zneg 7); rewrite bpow_neg; reflexivity).
  assert (Pc : 0 < bpow radix2 (-900)) by apply bpow_gt_0.
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

(** The series branch's tail [tk], [-RN(RN(zh RN(zh^2)) ps)]: the certificate's
    operations negated. *)
Definition p3r (u : R) : R := rn (aq2 - rn (u * aq3)).
Definition p2r (u : R) : R := rn (aq1 - rn (u * p3r u)).
Definition ps_of (u : R) : R := rn (aq0 - rn (u * p2r u)).

Lemma series_chain zh zl : finite zh -> finite zl -> bpow radix2 (-900) <= B zh -> B zh <= bpow radix2 (-7) ->
  exists tk, atan2_series zh zl = add_f64_64 zh zl tk /\ finite tk /\ Rabs (B tk) <= bpow radix2 (-22) /\
    B tk = - rn (rn (B zh * rn (B zh * B zh)) * ps_of (rn (B zh * B zh))) /\
    0 <= ps_of (rn (B zh * B zh)) <= / 2 /\ Rabs (B zh) <= bpow radix2 (-7).
Proof.
  intros Fh Fl L U.
  unfold atan2_series. cbv zeta. rewrite (index_zero_a zh Fh L U). cbv iota.
  destruct aq0_val as [E0 F0]. destruct aq1_val as [E1 F1]. destruct aq2_val as [E2 F2]. destruct aq3_val as [E3 F3].
  destruct aq_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]].
  set (Q0 := aw (nth (Z.to_nat 0%Z) atan2_poly0 0%Z)) in *.
  set (Q1 := aw (nth (Z.to_nat 1%Z) atan2_poly0 0%Z)) in *.
  set (Q2 := aw (nth (Z.to_nat 2%Z) atan2_poly0 0%Z)) in *.
  set (Q3 := aw (nth (Z.to_nat 3%Z) atan2_poly0 0%Z)) in *.
  pose proof (bpow_gt_0 radix2 (-900)) as P900.
  assert (Hz0 : 0 <= B zh) by lra.
  assert (U7 : Rabs (B zh) <= bpow radix2 (-7)) by (rewrite Rabs_pos_eq by lra; exact U).
  destruct (mul_range zh zh (-7) (-7) Fh Fh (conj Hz0 U) (conj Hz0 U) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fz2 [Ez2 [Z20 Z21]]].
  change (-7 + -7)%Z with (-14)%Z in Z21. set (z2 := fmul zh zh) in *.
  assert (Z2a : Rabs (B z2) <= bpow radix2 (-14)) by (rewrite Rabs_pos_eq by lra; exact Z21).
  (* m3 = z2 q3 *)
  assert (D3 : 0 <= B Q3 <= bpow radix2 (-3)) by (rewrite E3; bpow_num; lra).
  destruct (mul_range z2 Q3 (-14) (-3) Fz2 F3 (conj Z20 Z21) D3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm3 [Em3 [M30 M31]]].
  change (-14 + -3)%Z with (-17)%Z in M31. set (m3 := fmul z2 Q3) in *.
  (* p3 = -q2 + m3 *)
  assert (S3 : Rabs (B Q2) + Rabs (B m3) <= bpow radix2 (-2)).
  { rewrite E2, Rabs_Ropp, (Rabs_pos_eq aq2) by lra. rewrite Rabs_pos_eq by lra. bpow_num. bpow_num_in M31. nra. }
  destruct (addS Q2 m3 (-2) F2 Fm3 S3 ltac:(lia) ltac:(lia)) as [Fp3 [Ep3 Bp3]]. set (p3 := fadd Q2 m3) in *.
  (* m2 = z2 p3 *)
  destruct (mulS z2 p3 (-14) (-2) Fz2 Fp3 Z2a Bp3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm2 [Em2 Bm2]].
  change (-14 + -2)%Z with (-16)%Z in Bm2. set (m2 := fmul z2 p3) in *.
  (* p2 = q1 + m2 *)
  assert (S2 : Rabs (B Q1) + Rabs (B m2) <= bpow radix2 (-2)).
  { rewrite E1, (Rabs_pos_eq aq1) by lra. bpow_num. bpow_num_in Bm2. nra. }
  destruct (addS Q1 m2 (-2) F1 Fm2 S2 ltac:(lia) ltac:(lia)) as [Fp2 [Ep2 Bp2]]. set (p2 := fadd Q1 m2) in *.
  (* m1 = z2 p2 *)
  destruct (mulS z2 p2 (-14) (-2) Fz2 Fp2 Z2a Bp2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm1 [Em1 Bm1]].
  change (-14 + -2)%Z with (-16)%Z in Bm1. set (m1 := fmul z2 p2) in *.
  (* ps = -q0 + m1 *)
  assert (S1 : Rabs (B Q0) + Rabs (B m1) <= bpow radix2 (-1)).
  { rewrite E0, Rabs_Ropp, (Rabs_pos_eq aq0) by lra. bpow_num. bpow_num_in Bm1. nra. }
  destruct (addS Q0 m1 (-1) F0 Fm1 S1 ltac:(lia) ltac:(lia)) as [Fps [Eps Bps]]. set (ps := fadd Q0 m1) in *.
  (* a3 = zh z2 *)
  destruct (mul_range zh z2 (-7) (-14) Fh Fz2 (conj Hz0 U) (conj Z20 Z21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fa3 [Ea3 [A30 A31]]].
  change (-7 + -14)%Z with (-21)%Z in A31. set (a3 := fmul zh z2) in *.
  (* tail = a3 ps *)
  destruct (mulS a3 ps (-21) (-1) Fa3 Fps ltac:(rewrite Rabs_pos_eq by lra; exact A31) Bps ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Ftail [Etail Btail]].
  change (-21 + -1)%Z with (-22)%Z in Btail. set (tk := fmul a3 ps) in *.
  exists tk. split; [reflexivity | ]. split; [exact Ftail | ]. split; [exact Btail | ].
  (* the real form: oddness of rounding *)
  set (u := rn (B zh * B zh)) in *.
  assert (Hu : B z2 = u) by (rewrite Ez2; reflexivity).
  assert (Hp3 : B p3 = - p3r u).
  { unfold p3r. rewrite Ep3, E2, Em3, Hu, E3. replace (- aq2 + rndF (u * aq3)) with (- (aq2 - rn (u * aq3))) by (change (rn (u * aq3)) with (rndF (u * aq3)); ring).
    apply round_NE_opp_ne. }
  assert (Hm2 : B m2 = - rn (u * p3r u)).
  { rewrite Em2, Hu, Hp3. replace (u * - p3r u) with (- (u * p3r u)) by ring. apply round_NE_opp_ne. }
  assert (Hp2 : B p2 = p2r u).
  { unfold p2r. rewrite Ep2, E1, Hm2. replace (aq1 + - rn (u * p3r u)) with (aq1 - rn (u * p3r u)) by ring. reflexivity. }
  assert (Hm1 : B m1 = rn (u * p2r u)) by (rewrite Em1, Hu, Hp2; reflexivity).
  assert (Hps : B ps = - ps_of u).
  { unfold ps_of. rewrite Eps, E0, Hm1. replace (- aq0 + rn (u * p2r u)) with (- (aq0 - rn (u * p2r u))) by ring. apply round_NE_opp_ne. }
  assert (Ha3 : B a3 = rn (B zh * u)) by (rewrite Ea3, Hu; reflexivity).
  split.
  - rewrite Etail, Ha3, Hps. replace (rn (B zh * u) * - ps_of u) with (- (rn (B zh * u) * ps_of u)) by ring.
    apply round_NE_opp_ne.
  - split; [ | exact U7].
    assert (Hps' : Rabs (ps_of u) <= / 2) by (rewrite <- Rabs_Ropp, <- Hps; bpow_num_in Bps; exact Bps).
    assert (Hm1b : Rabs (rn (u * p2r u)) <= / 65536) by (rewrite <- Hm1; bpow_num_in Bm1; exact Bm1).
    split.
    + unfold ps_of. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ].
      apply Rabs_le_inv in Hm1b. lra.
    + exact (Rle_trans _ _ _ (Rle_abs _) Hps').
Qed.

Lemma aQ_pos X : 0 <= X <= bpow radix2 (-7) -> 0.3332 <= aQ (X * X) <= 0.3334.
Proof.
  intros [X0 X1]. destruct aq_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]].
  assert (XX0 : 0 <= X * X) by nra.
  assert (XX : X * X <= / 16384) by (bpow_num_in X1; nra).
  set (w := X * X) in *.
  assert (M3 : 0 <= w * aq3 <= 0.00001) by (split; nra).
  assert (H3 : 0.1427 <= aq2 - w * aq3 <= 0.1429) by (split; nra).
  assert (M2 : 0 <= w * (aq2 - w * aq3) <= 0.00001) by (split; nra).
  assert (H2 : 0.1998 <= aq1 - w * (aq2 - w * aq3) <= 0.2) by (split; nra).
  assert (M1 : 0 <= w * (aq1 - w * (aq2 - w * aq3)) <= 0.00002) by (split; nra).
  unfold aQ. split; nra.
Qed.

(** The series branch for [zh] in [[2^-100, 2^-7]]: the result is the exact sum of the
    argument and minus the cubic term, with the tail's relative error [2^-51]
    (series_tail.g) and the double-word addition's. *)
Theorem atan2_series_eval zh zl : finite zh -> finite zl ->
  bpow radix2 (-100) <= B zh -> B zh <= bpow radix2 (-7) ->
  B zh = rndF (B zh + B zl) -> Rabs (B zl) <= B zh / 2 ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    exists ec ea, Rabs ec <= / 2 ^ 51 /\ Rabs ea <= / 2 ^ 104 /\
      let Tx := B zh * B zh * B zh * aQ (B zh * B zh) in
      B h + B l = (B zh + B zl - Tx * (1 + ec)) * (1 + ea).
Proof.
  intros Fh Fl L U Dw Hl.
  assert (L9 : bpow radix2 (-900) <= B zh) by (apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | exact L]).
  destruct (series_chain zh zl Fh Fl L9 U) as [tk [Hs [Ftk [Btk [Etk [[Ps0 Ps1] U7]]]]]].
  pose proof (bpow_gt_0 radix2 (-100)) as P100.
  set (X := B zh) in *.
  assert (Xp : 0 < X) by lra.
  assert (X1 : / 2 ^ 100 <= X <= 0.0078126).
  { split.
    - change (-100)%Z with (- Z.of_nat 100)%Z in L. rewrite bpow_negn in L. exact L.
    - bpow_num_in U. lra. }
  pose proof (atan_series_tail_certificate X X1) as C. cbv zeta in C.
  assert (HX : rn X = X) by (apply rn_id; apply B_fmt). rewrite HX in C.
  set (Tc := rn (rn (X * rn (X * X)) * ps_of (rn (X * X)))) in *.
  assert (C' : Rabs ((Tc - X * X * X * aQ (X * X)) / (X * X * X * aQ (X * X))) <= / 2 ^ 51) by exact C.
  assert (X0 : 0 <= X) by lra.
  destruct (aQ_pos X (conj X0 U)) as [Q0 Q1].
  set (Tx := X * X * X * aQ (X * X)) in *.
  assert (Xcube : 0 < X * X * X) by (repeat apply Rmult_lt_0_compat; lra).
  assert (Txp : 0 < Tx) by (subst Tx; apply Rmult_lt_0_compat; [exact Xcube | lra]).
  assert (XX : X * X <= / 16384) by (bpow_num_in U; nra).
  assert (TxU : Tx <= 0.3334 * (X * X * X)) by (subst Tx; nra).
  assert (Hr : Rabs (Tc - Tx) <= / 2 ^ 51 * Tx).
  { assert (E : Tc - Tx = (Tc - Tx) / Tx * Tx) by (field; lra).
    rewrite E, Rabs_mult, (Rabs_pos_eq Tx) by lra.
    apply Rmult_le_compat_r; [lra | exact C']. }
  assert (P51 : / 2 ^ 51 <= 1 / 1000000) by interval with (i_prec 100).
  assert (Tcb : Rabs Tc <= 0.34 * (X * X * X)).
  { apply Rle_trans with (Rabs Tx + Rabs (Tc - Tx)).
    - replace Tc with (Tx + (Tc - Tx)) at 1 by ring. apply Rabs_triang.
    - rewrite (Rabs_pos_eq Tx) by lra. nra. }
  assert (Htk : Rabs (B tk) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-22)); [ | apply bpow_le; lia]. rewrite Rabs_pos_eq in * by lra. exact Btk. }
  assert (Hzl : Rabs (B zl) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. apply Rle_trans with (X / 2); [exact Hl | lra]. }
  assert (Hzh : Rabs X <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. exact U7. }
  pose proof (add_f64_ieee zh zl tk Fh Fl Ftk Dw Hzh Hzl Htk) as AF.
  pose proof (add_f64_normalized_ieee zh zl tk Fh Fl Ftk Dw Hzh Hzl Htk) as AFN.
  rewrite Hs. destruct (add_f64_64 zh zl tk) as [h l] eqn:Ead. cbv iota in AF, AFN. destruct AF as [Fh' [Fl' Bd]].
  destruct AFN as [_ [_ Nrm]].
  exists h, l. split; [reflexivity | ]. split; [exact Fh' | ]. split; [exact Fl' | ]. split; [exact Nrm | ].
  set (Xs := X + B zl + B tk) in *.
  assert (Hxs : 0 < Xs).
  { unfold Xs. apply Rabs_le_inv in Hl. rewrite Etk. 
    assert (Tcz : Rabs Tc <= X / 10) by (nra).
    apply Rabs_le_inv in Tcz. lra. }
  exists ((Tc - Tx) / Tx), ((B h + B l - Xs) / Xs). split; [ | split].
  - exact C'.
  - apply Rle_trans with (1 := Bd). replace (- prec)%Z with (-53)%Z by (unfold prec; reflexivity). rewrite bp53.
    assert (p104 : 2 ^ 104 = 20282409603651670423947251286016) by (simpl; ring). rewrite p104.
    assert (Hs2 : (/ 9007199254740992) ^ 2 = / 81129638414606681695789005144064) by (simpl; field). rewrite Hs2. lra.
  - cbv zeta.
    assert (Tx0 : Tx <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Txp).
    assert (Xs0 : Xs <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Hxs).
    assert (Hec : Tx * (1 + (Tc - Tx) / Tx) = Tc) by (field; exact Tx0).
    replace (X + B zl - Tx * (1 + (Tc - Tx) / Tx)) with Xs by (unfold Xs; rewrite Etk; lra).
    field. exact Xs0.
Qed.

(** A rounded value's magnitude, from a bound on the exact one. *)
Lemma rn_bound x A : Rabs x <= A -> Rabs (rn x) <= A + A / 1000000 + bpow radix2 (-1075).
Proof.
  intros H. pose proof (rnd_err_abs x) as R. pose proof (Rabs_pos x).
  assert (B53 : bpow radix2 (-53) <= / 1000000) by (bpow_num; interval with (i_prec 100)).
  change (rn x) with (rndF x).
  pose proof (Rabs_triang_inv (rndF x) x) as T.
  assert (bpow radix2 (-53) * Rabs x <= / 1000000 * A) by (apply Rmult_le_compat; [apply bpow_ge_0 | apply Rabs_pos | exact B53 | exact H]).
  lra.
Qed.

(** Below [2^-100] the cubic term is negligible: the tail is below [zh 2^-170]. *)
Theorem atan2_series_tiny zh zl : finite zh -> finite zl ->
  bpow radix2 (-900) <= B zh -> B zh <= bpow radix2 (-100) ->
  B zh = rndF (B zh + B zl) -> Rabs (B zl) <= B zh / 2 ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    exists tau ea, Rabs tau <= B zh * bpow radix2 (-170) /\ Rabs ea <= / 2 ^ 104 /\
      B h + B l = (B zh + B zl + tau) * (1 + ea).
Proof.
  intros Fh Fl L U Dw Hl.
  assert (U7 : B zh <= bpow radix2 (-7)) by (apply Rle_trans with (bpow radix2 (-100)); [exact U | apply bpow_le; lia]).
  destruct (series_chain zh zl Fh Fl L U7) as [tk [Hs [Ftk [Btk [Etk [[Ps0 Ps1] _]]]]]].
  pose proof (bpow_gt_0 radix2 (-900)) as P900.
  set (X := B zh) in *.
  assert (Xp : 0 < X) by lra.
  set (u := rn (X * X)) in *.
  set (ps := ps_of u) in *.
  assert (P1075 : bpow radix2 (-1075) <= X * bpow radix2 (-175)).
  { apply Rle_trans with (bpow radix2 (-900) * bpow radix2 (-175)).
    - rewrite <- bpow_plus. apply bpow_le. lia.
    - apply Rmult_le_compat_r; [apply bpow_ge_0 | exact L]. }
  assert (X2 : X * X <= bpow radix2 (-200)).
  { replace (-200)%Z with (-100 + -100)%Z by reflexivity. rewrite bpow_plus. pose proof (bpow_ge_0 radix2 (-100)). nra. }
  assert (B53 : bpow radix2 (-53) <= / 1000000) by (bpow_num; interval with (i_prec 100)).
  assert (B199 : bpow radix2 (-199) = 2 * bpow radix2 (-200)).
  { replace (-199)%Z with (-200 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (B175 : bpow radix2 (-174) = 2 * bpow radix2 (-175)).
  { replace (-174)%Z with (-175 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (B170 : bpow radix2 (-170) = 32 * bpow radix2 (-175)).
  { replace (-170)%Z with (-175 + 5)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 5) with 32. ring. }
  assert (B200s : bpow radix2 (-200) <= bpow radix2 (-175) / 1000).
  { replace (-200)%Z with (-175 + -25)%Z by reflexivity. rewrite bpow_plus.
    assert (bpow radix2 (-25) <= / 1000) by (bpow_num; interval with (i_prec 100)). pose proof (bpow_ge_0 radix2 (-175)). nra. }
  assert (B1075 : bpow radix2 (-1075) <= bpow radix2 (-200) / 1000).
  { replace (-1075)%Z with (-200 + -875)%Z by reflexivity. rewrite bpow_plus.
    assert (bpow radix2 (-875) <= / 1000) by (apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; interval with (i_prec 100)]).
    pose proof (bpow_ge_0 radix2 (-200)). nra. }
  pose proof (bpow_gt_0 radix2 (-200)) as P200. pose proof (bpow_gt_0 radix2 (-175)) as P175.
  (* u = RN(X^2) *)
  assert (Hu : Rabs u <= bpow radix2 (-199)).
  { pose proof (rn_bound (X * X) (bpow radix2 (-200)) ltac:(rewrite Rabs_pos_eq by nra; exact X2)) as R.
    apply Rle_trans with (1 := R). nra. }
  (* a3 = RN(X u) *)
  assert (Hxu : Rabs (X * u) <= X * bpow radix2 (-199)).
  { rewrite Rabs_mult, (Rabs_pos_eq X) by lra. nra. }
  pose proof (rn_bound (X * u) (X * bpow radix2 (-199)) Hxu) as Ha3.
  set (a3 := rn (X * u)) in *.
  assert (E1 : X * bpow radix2 (-199) <= X * bpow radix2 (-175) / 400).
  { pose proof (Rmult_le_compat_l X _ _ (Rlt_le _ _ Xp) B200s) as F1. rewrite B199. nra. }
  assert (Ha3' : Rabs a3 <= X * bpow radix2 (-174)).
  { apply Rle_trans with (1 := Ha3). rewrite B175. nra. }
  (* tail = RN(a3 ps) *)
  assert (Hps : Rabs ps <= / 2) by (rewrite Rabs_pos_eq by lra; exact Ps1).
  assert (Hap : Rabs (a3 * ps) <= X * bpow radix2 (-175)).
  { rewrite Rabs_mult. pose proof (Rabs_pos a3). pose proof (Rabs_pos ps). nra. }
  pose proof (rn_bound (a3 * ps) (X * bpow radix2 (-175)) Hap) as Htl.
  assert (Htau : Rabs (B tk) <= X * bpow radix2 (-170)).
  { rewrite Etk. rewrite Rabs_Ropp. apply Rle_trans with (1 := Htl). rewrite B170. nra. }
  assert (Htk : Rabs (B tk) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-22)); [ | apply bpow_le; lia]. rewrite Rabs_pos_eq in * by lra. exact Btk. }
  assert (Hzl : Rabs (B zl) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. apply Rle_trans with (X / 2); [exact Hl | lra]. }
  assert (Hzh : Rabs X <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [ | apply bpow_le; lia]. rewrite Rabs_pos_eq by lra. exact U7. }
  pose proof (add_f64_ieee zh zl tk Fh Fl Ftk Dw Hzh Hzl Htk) as AF.
  pose proof (add_f64_normalized_ieee zh zl tk Fh Fl Ftk Dw Hzh Hzl Htk) as AFN.
  rewrite Hs. destruct (add_f64_64 zh zl tk) as [h l] eqn:Ead. cbv iota in AF, AFN. destruct AF as [Fh' [Fl' Bd]].
  destruct AFN as [_ [_ Nrm]].
  exists h, l. split; [reflexivity | ]. split; [exact Fh' | ]. split; [exact Fl' | ]. split; [exact Nrm | ].
  set (Xs := X + B zl + B tk) in *.
  assert (Hxs : 0 < Xs).
  { unfold Xs. apply Rabs_le_inv in Hl. apply Rabs_le_inv in Htau.
    assert (bpow radix2 (-170) <= / 4) by (apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]).
    nra. }
  exists (B tk), ((B h + B l - Xs) / Xs). split; [exact Htau | split].
  - apply Rle_trans with (1 := Bd). replace (- prec)%Z with (-53)%Z by (unfold prec; reflexivity). rewrite bp53.
    assert (p104 : 2 ^ 104 = 20282409603651670423947251286016) by (simpl; ring). rewrite p104.
    assert (Hs2 : (/ 9007199254740992) ^ 2 = / 81129638414606681695789005144064) by (simpl; field). rewrite Hs2. lra.
  - cbv zeta.
    assert (Xs0 : Xs <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Hxs).
    replace (X + B zl + B tk) with Xs by (unfold Xs; reflexivity).
    field. exact Xs0.
Qed.
