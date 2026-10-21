(** asin's table segments: the reduction to [t = z - k/64] and the generic
    evaluation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error Sterbenz IEEE754.Binary IEEE754.Bits.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingCore.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel AsinSqrtStep AsinSeriesSmall ExpReduction.
Import ListNotations.
Open Scope R_scope.

(** [64 z] is exact for a binary64 [z] in [[2^-28, 1]]. *)
Lemma times_64_exact_wide z : finite z -> bpow radix2 (-28) <= B z -> B z <= 1 ->
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
  assert (Pc : 0 < bpow radix2 (-28)) by apply bpow_gt_0.
  assert (E6 : B z * B asin_64 = B z * bpow radix2 6).
  { rewrite V6. change (bpow radix2 6) with 64. reflexivity. }
  assert (Bd : bnd 1 6 (B z * B asin_64)).
  { apply bnd_p. rewrite V6. change (IZR 1) with 1. rewrite Rmult_1_l.
    apply Rabs_le. change (bpow radix2 6) with 64. lra. }
  destruct (fmul_bnd 1 6 z asin_64 Fz F6 ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Bd) as [F [E _]].
  split; [exact F | ].
  rewrite E, E6, round_generic by (try exact _; exact Gs).
  change (bpow radix2 6) with 64. reflexivity.
Qed.

(** The shifter index of [z] in [[1/128, 1]] is [Znearest ne (64 z)]. *)
Lemma index_value z : finite z -> / 128 <= B z -> B z <= 1 ->
  finite (fsub (fadd (fmul z asin_64) asin_shifter) asin_shifter) /\
  B (fsub (fadd (fmul z asin_64) asin_shifter) asin_shifter) = IZR (Znearest ne (B z * 64)).
Proof.
  intros Fz L U.
  assert (L28 : bpow radix2 (-28) <= B z).
  { pose proof (bpow_gt_0 radix2 (-28)). apply Rle_trans with (/ 128); [ | exact L].
    change (-28)%Z with (- Z.of_nat 28)%Z. rewrite bpow_negn. simpl. lra. }
  destruct (times_64_exact_wide z Fz L28 U) as [Fy Ey].
  rewrite asin_shifter_eq.
  assert (Hb50 : Rabs (B (fmul z asin_64)) <= bpow radix2 50).
  { rewrite Ey, Rabs_pos_eq by lra. change (bpow radix2 50) with 1125899906842624%R. lra. }
  destruct (shifter_round (fmul z asin_64) Fy Hb50) as [Fn En]. rewrite Ey in En. cbv zeta in Fn, En.
  split; assumption.
Qed.

(** The transcription's [i as usize]. *)
Lemma asin_index_ok f n : finite f -> B f = IZR n -> (0 <= n)%Z -> asin_index f = n.
Proof.
  intros Ff Bf Hn.
  destruct f as [s | s | s pl Hpl | s m e Hb]; unfold asin_index.
  - simpl in Bf. symmetry in Bf. apply eq_IZR in Bf. lia.
  - discriminate Ff.
  - discriminate Ff.
  - simpl in Bf. unfold F2R in Bf. simpl in Bf. destruct s.
    + exfalso. simpl in Bf. change (Zneg m) with (Z.opp (Zpos m)) in Bf. rewrite opp_IZR in Bf.
      assert (0 < IZR (Zpos m) * bpow radix2 e) by (apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
      assert (0 <= IZR n) by (apply IZR_le; lia). nra.
    + simpl in Bf.
      destruct (Z.ltb_spec e 0) as [Neg | Pos].
      * (* e < 0: n 2^-e = m *)
        assert (E : (n * 2 ^ (- e) = Zpos m)%Z).
        { apply eq_IZR. rewrite mult_IZR.
          assert (Hp : IZR (2 ^ (- e)) = bpow radix2 (- e)) by (apply (IZR_Zpower radix2); lia).
          rewrite Hp. rewrite <- Bf. rewrite Rmult_assoc. rewrite <- bpow_plus. replace (e + - e)%Z with 0%Z by ring. simpl. ring. }
        rewrite <- E. rewrite Z.shiftr_div_pow2 by lia.
        apply Z.div_mul. apply Z.pow_nonzero; lia.
      * (* e >= 0: n = m 2^e *)
        assert (E : n = (Zpos m * 2 ^ e)%Z).
        { apply eq_IZR. rewrite mult_IZR. assert (Hp : IZR (2 ^ e) = bpow radix2 e) by (apply (IZR_Zpower radix2); lia).
          rewrite Hp. symmetry. exact Bf. }
        rewrite E. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma inv64_val : B asin_inv64 = / 64 /\ finite asin_inv64.
Proof.
  split.
  - unfold asin_inv64, aw. rewrite (bits_val 0x3f90000000000000 false 4503599627370496%positive 58 eq_refl).
    simpl (cond_Zopp false _). field.
  - exact (bits_finite 0x3f90000000000000 false 4503599627370496%positive (-58) eq_refl).
Qed.

Lemma bm6 : bpow radix2 (-6) = / 64.
Proof. rewrite (bpow_negn 6 : bpow radix2 (-6) = / 2 ^ 6). simpl. field. Qed.

(** [i / 64] is exact for the table index [i = k]. *)
Lemma scaled_index_exact i k : finite i -> B i = IZR k -> (1 <= k <= 45)%Z ->
  finite (fmul i asin_inv64) /\ B (fmul i asin_inv64) = IZR k / 64.
Proof.
  intros Fi Bi Hk. destruct inv64_val as [V F].
  assert (Hk1 : 1 <= IZR k) by (change 1 with (IZR 1); apply IZR_le; lia).
  assert (Hk2 : IZR k <= 45) by (change 45 with (IZR 45); apply IZR_le; lia).
  assert (G : fmtF (IZR k / 64)).
  { replace (IZR k / 64) with (IZR k * bpow radix2 (-6)) by (rewrite bm6; field). apply bnd_fmt; lia. }
  assert (Bd : bnd 1 0 (B i * B asin_inv64)).
  { apply bnd0. rewrite Bi, V. apply Rabs_le. change (IZR 1) with 1. lra. }
  destruct (fmul_bnd 1 0 i asin_inv64 Fi F ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [Fm [Em _]].
  split; [exact Fm | ].
  rewrite Em, Bi, V. replace (IZR k * / 64) with (IZR k / 64) by field.
  apply round_generic; [exact _ | exact G].
Qed.

(** [z - k/64] is exact (Sterbenz) for [|z - k/64| <= 1/128], [k >= 1]. *)
Lemma sub_table_exact zh a k : finite zh -> finite a -> B a = IZR k / 64 -> (1 <= k <= 45)%Z ->
  Rabs (B zh - IZR k / 64) <= / 128 ->
  finite (fsub zh a) /\ B (fsub zh a) = B zh - IZR k / 64.
Proof.
  intros Fz Fa Ba Hk D.
  assert (Hk1 : 1 <= IZR k) by (change 1 with (IZR 1); apply IZR_le; lia).
  apply Rabs_le_inv in D.
  assert (Gd : fmtF (B zh - B a)).
  { apply (sterbenz radix2 (FLT_exp emin prec) (B zh) (B a) (B_fmt zh) (B_fmt a)). rewrite Ba. lra. }
  assert (Bd : bnd 1 0 (B zh - B a)).
  { apply bnd0. rewrite Ba. apply Rabs_le. change (IZR 1) with 1. lra. }
  destruct (fsub_bnd 1 0 zh a Fz Fa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [F [E _]].
  split; [exact F | ].
  rewrite E, Ba. apply round_generic; [exact _ | ]. rewrite <- Ba. exact Gd.
Qed.

Lemma bm52 : bpow radix2 (-52) = / 4503599627370496.
Proof. rewrite (bpow_negn 52 : bpow radix2 (-52) = / 2 ^ 52). simpl. field. Qed.

Lemma bm59 : bpow radix2 (-59) = / 576460752303423488.
Proof. rewrite (bpow_negn 59 : bpow radix2 (-59) = / 2 ^ 59). simpl. field. Qed.

Lemma bm60 : bpow radix2 (-60) = / 1152921504606846976.
Proof. rewrite (bpow_negn 60 : bpow radix2 (-60) = / 2 ^ 60). simpl. field. Qed.

(** The second [two_sum] of the segment branch: [t = th + tl] is the exact
    sum of [x' = z - k/64] and [zl], [th] is within [0.0078126] and [tl] within
    [8.7e-19]. *)
Lemma t_split x' zl : finite x' -> finite zl -> Rabs (B x') <= / 128 ->
  (B x' = 0 \/ bpow radix2 (-59) <= Rabs (B x')) ->
  Rabs (B zl) <= bpow radix2 (-60) -> (B zl = 0 \/ bpow radix2 (-900) <= Rabs (B zl)) ->
  let '(th, tl) := two_sum64 x' zl in
  finite th /\ finite tl /\ B th = rndF (B x' + B zl) /\ B th + B tl = B x' + B zl /\
  Rabs (B th) <= 0.0078126 /\ Rabs (B tl) <= 8.7e-19 /\ (B th = 0 \/ bpow radix2 (-900) <= Rabs (B th)) /\
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th).
Proof.
  intros Fx Fz Hx Hxn Hz Hzn.
  assert (Hts := two_sum_ieee x' zl Fx Fz
    ltac:(apply Rle_trans with 1; [apply Rle_trans with (/ 128); [exact Hx | lra] | change 1 with (bpow radix2 0); apply bpow_le; lia])
    ltac:(apply Rle_trans with (bpow radix2 (-60)); [exact Hz | apply bpow_le; lia])).
  destruct (two_sum64 x' zl) as [th tl] eqn:E. cbv beta iota in Hts. destruct Hts as [Fth [Ftl [Eth Esum]]].
  refine (conj Fth (conj Ftl (conj Eth (conj Esum _)))).
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53.
  assert (P60 : bpow radix2 (-60) = / 1152921504606846976) by exact bm60.
  assert (P59 : bpow radix2 (-59) = / 576460752303423488) by exact bm59.
  assert (Pg : bpow radix2 (-1022) <= bpow radix2 (-900)) by (apply bpow_le; lia).
  assert (Hbig : bpow radix2 (-59) <= Rabs (B x') -> bpow radix2 (-60) <= Rabs (B x' + B zl)).
  { intros X1. rewrite P60. rewrite P59 in X1. rewrite P60 in Hz.
    apply Rabs_le_inv in Hz. destruct (Rle_dec 0 (B x')) as [Pp | Pn].
    + rewrite Rabs_pos_eq in X1 by exact Pp. apply Rle_trans with (B x' + B zl); [lra | apply Rle_abs].
    + rewrite Rabs_left in X1 by lra. rewrite <- Rabs_Ropp. apply Rle_trans with (- (B x' + B zl)); [lra | apply Rle_abs]. }
  destruct (Req_dec (B x' + B zl) 0) as [Z0 | NZ].
  - (* x = 0 *)
    assert (T0 : B th = 0) by (rewrite Eth, Z0; apply round_0; exact _).
    assert (L0 : B tl = 0) by lra.
    rewrite T0, L0. rewrite Rabs_R0. split; [lra | split; [lra | split; [left; reflexivity | lra]]].
  - assert (Hx1 : bpow radix2 (-1022) <= Rabs (B x' + B zl)).
    { destruct Hxn as [X0 | X1].
      - rewrite X0, Rplus_0_l in NZ |- *.
        destruct Hzn as [Z0 | Z1]; [contradiction | ]. apply Rle_trans with (bpow radix2 (-900)); assumption.
      - apply Rle_trans with (bpow radix2 (-60)); [apply bpow_le; lia | exact (Hbig X1)]. }
    pose proof (rnd_rel _ Hx1) as R. change (RNE (B x' + B zl)) with (rndF (B x' + B zl)) in R.
    rewrite <- Eth in R.
    assert (Etl : B tl = (B x' + B zl) - B th) by lra.
    rewrite P53 in R.
    assert (Hxa : Rabs (B x' + B zl) <= / 128 + / 1152921504606846976).
    { apply Rle_trans with (Rabs (B x') + Rabs (B zl)); [apply Rabs_triang | rewrite P60 in Hz; lra]. }
    assert (Htl : Rabs (B tl) <= 8.7e-19).
    { rewrite Etl. rewrite Rabs_minus_sym. 
      apply Rle_trans with (/ 9007199254740992 * Rabs (B x' + B zl)); [exact R | ].
      apply Rle_trans with (/ 9007199254740992 * (/ 128 + / 1152921504606846976)).
      - apply Rmult_le_compat_l; [lra | exact Hxa].
      - lra. }
    split; [ | split; [exact Htl | split; [ | ]]].
    + assert (Hth : B th = (B x' + B zl) - B tl) by lra.
      apply Rabs_le. apply Rabs_le_inv in Htl. apply Rabs_le_inv in Hxa. lra.
    + right. destruct Hxn as [X0 | X1].
      * rewrite X0, Rplus_0_l in Eth. rewrite Eth. rewrite round_generic by (try exact _; apply B_fmt).
        destruct Hzn as [Z0 | Z1]; [rewrite X0, Rplus_0_l in NZ; contradiction | exact Z1].
      * pose proof (Hbig X1) as H60.
        assert (Hlo : Rabs (B x' + B zl) / 2 <= Rabs (B th)).
        { assert (Htri : Rabs (B x' + B zl) - Rabs (B tl) <= Rabs (B th)).
          { replace (B th) with ((B x' + B zl) - B tl) by lra.
            apply Rle_trans with (Rabs ((B x' + B zl) - B tl)); [ | apply Rle_refl].
            apply Rabs_triang_inv. }
          pose proof (Rabs_pos (B x' + B zl)).
          assert (Rabs (B tl) <= / 9007199254740992 * Rabs (B x' + B zl)).
          { rewrite Etl. rewrite Rabs_minus_sym. exact R. }
          lra. }
        apply Rle_trans with (bpow radix2 (-61)); [apply bpow_le; lia | ].
        replace (bpow radix2 (-61)) with (bpow radix2 (-60) / 2).
        -- apply Rle_trans with (Rabs (B x' + B zl) / 2); [lra | exact Hlo].
        -- replace (-61)%Z with (-60 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field.
    + assert (Etl' : Rabs (B tl) <= / 9007199254740992 * Rabs (B x' + B zl)) by (rewrite Etl; rewrite Rabs_minus_sym; exact R).
      replace (B x' + B zl) with (B th + B tl) in Etl' by lra.
      pose proof (Rabs_triang (B th) (B tl)) as Tr. pose proof (Rabs_pos (B tl)). pose proof (Rabs_pos (B th)).
      rewrite bm52.
      assert (Rabs (B th + B tl) <= Rabs (B th) + Rabs (B tl)) by exact Tr.
      nra.
Qed.

(** One Horner step stays below [2^12] for coefficients below [2^11]. *)
Lemma horner_step th g h : finite th -> finite g -> finite h ->
  Rabs (B th) <= bpow radix2 (-6) -> Rabs (B g) <= bpow radix2 11 -> Rabs (B h) <= bpow radix2 12 ->
  finite (fadd g (fmul th h)) /\ B (fadd g (fmul th h)) = rndF (B g + rndF (B th * B h)) /\
  Rabs (B (fadd g (fmul th h))) <= bpow radix2 12.
Proof.
  intros Ft Fg Fh T G H.
  assert (Pm : bpow radix2 (-6) * bpow radix2 12 = bpow radix2 6).
  { rewrite <- bpow_plus. reflexivity. }
  assert (Hm : bnd 1 6 (B th * B h)).
  { apply bnd_p. change (IZR 1) with 1. rewrite Rmult_1_l. rewrite Rabs_mult.
    rewrite <- Pm. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fmul_bnd 1 6 th h Ft Fh ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hm) as [Fm [Em Bm]].
  assert (Bm' : Rabs (B (fmul th h)) <= 64).
  { unfold bnd in Bm. change (bpow radix2 6) with 64 in Bm. change (IZR 1) with 1 in Bm. lra. }
  assert (G' : Rabs (B g) <= 2048) by (change (bpow radix2 11) with 2048 in G; exact G).
  assert (Ha : bnd 1 12 (B g + B (fmul th h))).
  { apply bnd_p. change (IZR 1) with 1. rewrite Rmult_1_l. change (bpow radix2 12) with 4096.
    apply Rle_trans with (Rabs (B g) + Rabs (B (fmul th h))); [apply Rabs_triang | lra]. }
  destruct (fadd_bnd 1 12 g (fmul th h) Fg Fm ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Ha) as [Fa [Ea Ba]].
  repeat split; try assumption.
  - rewrite Ea, Em. reflexivity.
  - unfold bnd in Ba. change (IZR 1) with 1 in Ba. rewrite Rmult_1_l in Ba. exact Ba.
Qed.

(** The transcription's Horner chain. *)
Definition hf (th c4 c5 c6 c7 c8 c9 c10 c11 c12 : f64) : f64 :=
  fadd c4 (fmul th (fadd c5 (fmul th (fadd c6 (fmul th (fadd c7 (fmul th (fadd c8 (fmul th (fadd c9 (fmul th (fadd c10 (fmul th (fadd c11 (fmul th c12))))))))))))))).

Lemma horner_chain th c4 c5 c6 c7 c8 c9 c10 c11 c12 :
  finite th -> finite c4 -> finite c5 -> finite c6 -> finite c7 -> finite c8 -> finite c9 -> finite c10 -> finite c11 -> finite c12 ->
  Rabs (B th) <= bpow radix2 (-6) ->
  Rabs (B c4) <= bpow radix2 11 -> Rabs (B c5) <= bpow radix2 11 -> Rabs (B c6) <= bpow radix2 11 ->
  Rabs (B c7) <= bpow radix2 11 -> Rabs (B c8) <= bpow radix2 11 -> Rabs (B c9) <= bpow radix2 11 ->
  Rabs (B c10) <= bpow radix2 11 -> Rabs (B c11) <= bpow radix2 11 -> Rabs (B c12) <= bpow radix2 11 ->
  finite (hf th c4 c5 c6 c7 c8 c9 c10 c11 c12) /\
  let t := B th in
  let h8 := B c12 in
  let h7 := rn (B c11 + rn (t * h8)) in
  let h6 := rn (B c10 + rn (t * h7)) in
  let h5 := rn (B c9 + rn (t * h6)) in
  let h4 := rn (B c8 + rn (t * h5)) in
  let h3 := rn (B c7 + rn (t * h4)) in
  let h2 := rn (B c6 + rn (t * h3)) in
  let h1 := rn (B c5 + rn (t * h2)) in
  let h0 := rn (B c4 + rn (t * h1)) in
  B (hf th c4 c5 c6 c7 c8 c9 c10 c11 c12) = h0 /\ Rabs h0 <= bpow radix2 12.
Proof.
  intros Ft F4 F5 F6 F7 F8 F9 F10 F11 F12 T G4 G5 G6 G7 G8 G9 G10 G11 G12.
  assert (Up : forall v, Rabs v <= bpow radix2 11 -> Rabs v <= bpow radix2 12).
  { intros v H. apply Rle_trans with (bpow radix2 11); [exact H | apply bpow_le; lia]. }
  destruct (horner_step th c11 c12 Ft F11 F12 T G11 (Up _ G12)) as [Fa7 [Ea7 Ba7]].
  destruct (horner_step th c10 _ Ft F10 Fa7 T G10 Ba7) as [Fa6 [Ea6 Ba6]].
  destruct (horner_step th c9 _ Ft F9 Fa6 T G9 Ba6) as [Fa5 [Ea5 Ba5]].
  destruct (horner_step th c8 _ Ft F8 Fa5 T G8 Ba5) as [Fa4 [Ea4 Ba4]].
  destruct (horner_step th c7 _ Ft F7 Fa4 T G7 Ba4) as [Fa3 [Ea3 Ba3]].
  destruct (horner_step th c6 _ Ft F6 Fa3 T G6 Ba3) as [Fa2 [Ea2 Ba2]].
  destruct (horner_step th c5 _ Ft F5 Fa2 T G5 Ba2) as [Fa1 [Ea1 Ba1]].
  destruct (horner_step th c4 _ Ft F4 Fa1 T G4 Ba1) as [Fa0 [Ea0 Ba0]].
  split; [exact Fa0 | ]. cbv zeta.
  assert (E : B (hf th c4 c5 c6 c7 c8 c9 c10 c11 c12) = rn (B c4 + rn (B th * rn (B c5 + rn (B th * rn (B c6 + rn (B th *
    rn (B c7 + rn (B th * rn (B c8 + rn (B th * rn (B c9 + rn (B th * rn (B c10 + rn (B th * rn (B c11 + rn (B th * B c12))))))))))))))))).
  { unfold hf. rewrite Ea0, Ea1, Ea2, Ea3, Ea4, Ea5, Ea6, Ea7. reflexivity. }
  split; [exact E | ]. rewrite <- E. exact Ba0.
Qed.

(** Horner polynomials over a list of coefficients, and their variation. *)
Fixpoint pl (a : list R) (x : R) : R :=
  match a with nil => 0 | c :: a' => c + x * pl a' x end.

(** [bl a]: a bound on [|pl a x|] for [|x| <= T]; [sl a]: the Lipschitz constant
    [sum j |a_j| T^(j-1)]. *)
Fixpoint bl (T : R) (a : list R) : R :=
  match a with nil => 0 | c :: a' => Rabs c + T * bl T a' end.
Fixpoint sl (T : R) (a : list R) : R :=
  match a with nil => 0 | _ :: a' => T * sl T a' + bl T a' end.

Lemma pl_bound T a x : 0 <= T -> Rabs x <= T -> Rabs (pl a x) <= bl T a.
Proof.
  intros HT Hx. induction a as [|c a IH]; simpl.
  - rewrite Rabs_R0. lra.
  - apply Rle_trans with (Rabs c + Rabs (x * pl a x)); [apply Rabs_triang | ].
    rewrite Rabs_mult. assert (Rabs x * Rabs (pl a x) <= T * bl T a).
    { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
    lra.
Qed.

Lemma bl_nonneg T a : 0 <= T -> 0 <= bl T a.
Proof.
  intros HT. induction a as [|c a IH]; simpl; [lra | ].
  pose proof (Rabs_pos c). assert (0 <= T * bl T a) by nra. lra.
Qed.

Lemma pl_diff T a x y : 0 <= T -> Rabs x <= T -> Rabs y <= T -> Rabs (pl a y - pl a x) <= sl T a * Rabs (y - x).
Proof.
  intros HT Hx Hy. induction a as [|c a IH]; simpl.
  - rewrite Rminus_diag_eq by reflexivity. rewrite Rabs_R0. lra.
  - replace (c + y * pl a y - (c + x * pl a x)) with (y * (pl a y - pl a x) + (y - x) * pl a x) by ring.
    apply Rle_trans with (Rabs (y * (pl a y - pl a x)) + Rabs ((y - x) * pl a x)); [apply Rabs_triang | ].
    rewrite !Rabs_mult.
    pose proof (bl_nonneg T a HT). pose proof (pl_bound T a x HT Hx). pose proof (Rabs_pos (y - x)).
    assert (Rabs y * Rabs (pl a y - pl a x) <= T * (sl T a * Rabs (y - x))).
    { apply Rmult_le_compat; try apply Rabs_pos; try assumption. }
    assert (Rabs (y - x) * Rabs (pl a x) <= Rabs (y - x) * bl T a) by (apply Rmult_le_compat_l; assumption).
    nra.
Qed.

(** A segment's evaluation certificate (formal/asin/eval_<kk>.g), over its
    coefficients: [c_hi], [c_lo], [g0 .. g8], the claimed bound, and the bound
    [dgb] on [dg], which stands for [G(th + tl) - G(th)]. *)
Definition EvalCert (cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 bound dgb : R) : Prop :=
  forall th_ tl_ dg, -0.0078126 <= th_ <= 0.0078126 -> -8.7e-19 <= tl_ <= 8.7e-19 -> -dgb <= dg <= dgb ->
   let th := rn th_ in let tl := rn tl_ in
   let ph := rn (th * cH) in let pl := th * cH - ph in
   let m1 := rn (th * cL) in let m2 := rn (tl * cH) in let m3 := rn (m1 + m2) in
   let s1 := rn (pl + m3) in let t2 := rn (th * th) in
   let hh7 := rn (g7 + rn (th * g8)) in let hh6 := rn (g6 + rn (th * hh7)) in
   let hh5 := rn (g5 + rn (th * hh6)) in let hh4 := rn (g4 + rn (th * hh5)) in
   let hh3 := rn (g3 + rn (th * hh4)) in let hh2 := rn (g2 + rn (th * hh3)) in
   let hh1 := rn (g1 + rn (th * hh2)) in let hh0 := rn (g0 + rn (th * hh1)) in
   let HH7 := g7 + th * g8 in let HH6 := g6 + th * HH7 in let HH5 := g5 + th * HH6 in
   let HH4 := g4 + th * HH5 in let HH3 := g3 + th * HH4 in let HH2 := g2 + th * HH3 in
   let HH1 := g1 + th * HH2 in let HH0 := g0 + th * HH1 in
   let n := rn (t2 * hh0) in let tail := rn (s1 + n) in
   let tt := th + tl in
   let Vx := pl + cL * th + cH * tl + cL * tl + tt * tt * (HH0 + dg) in
   Rabs (tail - Vx) <= bound /\ Rabs hh0 <= 2.

(** A certificate's [BND] goal as an absolute-value bound ([ml = -m]). *)
Lemma rabs_bnd x (m ml : Z) e b : ml = (- m)%Z -> IZR m * bpow radix2 e <= b ->
  BND x (makepairF (Float2 ml e) (Float2 m e)) -> Rabs x <= b.
Proof.
  intros Hml H B. apply bnd_to in B. destruct B as [B1 B2].
  rewrite Hml, opp_IZR in B1. apply Rabs_le. split; lra.
Qed.

(** The segment branch's reduction: for [zh] in [[1/128, 0.7072]] with index [k]
    the transcription forms [th + tl = (zh - k/64) + zl] exactly. *)
Lemma segment_reduction zh zl (k : Z) : (1 <= k <= 45)%Z ->
  finite zh -> finite zl -> / 128 <= B zh -> B zh <= 0.7072 -> Znearest ne (B zh * 64) = k ->
  Rabs (B zl) <= bpow radix2 (-60) -> (B zl = 0 \/ bpow radix2 (-900) <= Rabs (B zl)) ->
  let i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter in
  asin_cmp i asin_zero = Some Gt /\ asin_index i = k /\
  finite (fmul i asin_inv64) /\ B (fmul i asin_inv64) = IZR k / 64 /\
  finite (fsub zh (fmul i asin_inv64)) /\ B (fsub zh (fmul i asin_inv64)) = B zh - IZR k / 64 /\
  (B zh - IZR k / 64 = 0 \/ bpow radix2 (-59) <= Rabs (B zh - IZR k / 64)) /\
  Rabs (B zh - IZR k / 64) <= / 128.
Proof.
  intros Hk Fz Fl L U Hn Hl Hln i.
  destruct (index_value zh Fz L ltac:(lra)) as [Fi Ei]. rewrite Hn in Ei.
  fold i in Fi, Ei.
  assert (Hk1 : 1 <= IZR k) by (change 1 with (IZR 1); apply IZR_le; lia).
  assert (Hk2 : IZR k <= 45) by (change 45 with (IZR 45); apply IZR_le; lia).
  (* comparison with zero *)
  destruct zero_val as [Bz Fzero].
  assert (Cgt : asin_cmp i asin_zero = Some Gt).
  { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 i asin_zero Fi Fzero), Ei, Bz. rewrite Rcompare_Gt; [reflexivity | lra]. }
  assert (Ix : asin_index i = k) by (apply asin_index_ok; [exact Fi | exact Ei | lia]).
  destruct (scaled_index_exact i k Fi Ei Hk) as [Fa Ea].
  assert (Hd : Rabs (B zh - IZR k / 64) <= / 128).
  { pose proof (Znearest_half (fun n => negb (Z.even n)) (B zh * 64)) as H. fold ne in H. rewrite Hn in H.
    apply Rabs_le_inv in H. apply Rabs_le. lra. }
  destruct (sub_table_exact zh (fmul i asin_inv64) k Fz Fa Ea Hk Hd) as [Fs Es].
  refine (conj Cgt (conj Ix (conj Fa (conj Ea (conj Fs (conj Es (conj _ Hd))))))).
  (* the grid: zh is a multiple of 2^-59, so is k/64 *)
  assert (Hr : bpow radix2 (-7) <= Rabs (B zh)).
  { rewrite Rabs_pos_eq by lra. change (-7)%Z with (- Z.of_nat 7)%Z. rewrite bpow_negn. simpl. lra. }
  pose proof (grid_fmt_bound (FLT_exp emin prec) (-7) (B zh) ltac:(intros e; unfold FLT_exp, emin, prec; lia) (B_fmt zh) (or_intror Hr)) as G1.
  replace (-7 - 52)%Z with (-59)%Z in G1 by reflexivity.
  assert (G2 : on_grid (-59) (IZR k / 64)).
  { exists (k * 2 ^ 53)%Z. rewrite mult_IZR.
    assert (Hp : IZR (2 ^ 53) = bpow radix2 53) by (apply (IZR_Zpower radix2); lia).
    rewrite Hp. rewrite Rmult_assoc. rewrite <- bpow_plus.
    replace (53 + -59)%Z with (-6)%Z by reflexivity. rewrite bm6. field. }
  pose proof (grid_minus _ _ _ G1 G2) as G3.
  destruct (Req_dec (B zh - IZR k / 64) 0) as [Z0 | NZ]; [left; exact Z0 | right].
  exact (grid_nonzero _ _ G3 NZ).
Qed.

(** Signed range lemmas: a rounded product or sum, finite, within the exact bound. *)
Lemma mulS a b ea eb : finite a -> finite b -> Rabs (B a) <= bpow radix2 ea -> Rabs (B b) <= bpow radix2 eb ->
  (-500 <= ea)%Z -> (-500 <= eb)%Z -> (ea <= 100)%Z -> (eb <= 100)%Z ->
  finite (fmul a b) /\ B (fmul a b) = rndF (B a * B b) /\ Rabs (B (fmul a b)) <= bpow radix2 (ea + eb).
Proof.
  intros Fa Fb A B' Ha Hb Hc Hd.
  assert (Hbnd : bnd 1 (ea + eb) (B a * B b)).
  { apply bnd_p. change (IZR 1) with 1. rewrite Rmult_1_l. rewrite Rabs_mult, bpow_plus.
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fmul_bnd 1 (ea + eb) a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  split; [exact F | split; [exact E | ]].
  unfold bnd in Bd. change (IZR 1) with 1 in Bd. rewrite Rmult_1_l in Bd. exact Bd.
Qed.

Lemma addS a b e : finite a -> finite b -> Rabs (B a) + Rabs (B b) <= bpow radix2 e -> (-1000 <= e)%Z -> (e <= 100)%Z ->
  finite (fadd a b) /\ B (fadd a b) = rndF (B a + B b) /\ Rabs (B (fadd a b)) <= bpow radix2 e.
Proof.
  intros Fa Fb S He Hf.
  assert (Hbnd : bnd 1 e (B a + B b)).
  { apply bnd_p. change (IZR 1) with 1. rewrite Rmult_1_l.
    apply Rle_trans with (Rabs (B a) + Rabs (B b)); [apply Rabs_triang | exact S]. }
  destruct (fadd_bnd 1 e a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  split; [exact F | split; [exact E | ]].
  unfold bnd in Bd. change (IZR 1) with 1 in Bd. rewrite Rmult_1_l in Bd. exact Bd.
Qed.

(** Rounding preserves a bound [2^-p |t|] when [2^-p |t|] is a binary64. *)
Lemma rn_scaled y p t : (0 <= p <= 100)%Z -> fmtF t -> (t = 0 \/ bpow radix2 (-900) <= Rabs t) ->
  Rabs y <= bpow radix2 (- p) * Rabs t -> Rabs (rndF y) <= bpow radix2 (- p) * Rabs t.
Proof.
  intros Hp Ft Ht Hy.
  assert (Fc : fmtF (bpow radix2 (- p) * Rabs t)).
  { destruct Ht as [T0 | Tn].
    - rewrite T0, Rabs_R0, Rmult_0_r. apply generic_format_0.
    - rewrite Rmult_comm. apply mult_bpow_exact_FLT; [apply generic_format_abs; exact Ft | ].
      assert (M : (-899 <= mag radix2 (Rabs t))%Z).
      { apply mag_ge_bpow. rewrite Rabs_Rabsolu. replace (-899 - 1)%Z with (-900)%Z by reflexivity. exact Tn. }
      unfold emin, prec. lia. }
  assert (Hc0 : 0 <= bpow radix2 (- p) * Rabs t) by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos]).
  apply Rabs_le_inv in Hy. apply Rabs_le.
  split.
  - apply round_ge_generic; [exact _ | exact _ | | lra].
    replace (- (bpow radix2 (- p) * Rabs t)) with (- (bpow radix2 (- p) * Rabs t)) by reflexivity.
    apply generic_format_opp. exact Fc.
  - apply round_le_generic; [exact _ | exact _ | exact Fc | lra].
Qed.

(** One rounded operation whose exact result is within [2^-p |t|] (and [|t| <= 1]):
    finite, rounded as the model says, and still within [2^-p |t|]. *)
Lemma mul_scaled a b p t : finite a -> finite b -> (0 <= p <= 100)%Z -> fmtF t -> Rabs t <= 1 ->
  (t = 0 \/ bpow radix2 (-900) <= Rabs t) -> Rabs (B a * B b) <= bpow radix2 (- p) * Rabs t ->
  finite (fmul a b) /\ B (fmul a b) = rndF (B a * B b) /\ Rabs (B (fmul a b)) <= bpow radix2 (- p) * Rabs t.
Proof.
  intros Fa Fb Hp Ft Ht1 Ht Hy.
  assert (Hb : bnd 1 0 (B a * B b)).
  { apply bnd0. change (IZR 1) with 1. apply Rle_trans with (bpow radix2 (- p) * Rabs t); [exact Hy | ].
    assert (bpow radix2 (- p) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
    pose proof (Rabs_pos t). nra. }
  destruct (fmul_bnd 1 0 a b Fa Fb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb) as [F [E _]].
  split; [exact F | split; [exact E | ]]. rewrite E. apply rn_scaled; assumption.
Qed.

Lemma add_scaled a b p t : finite a -> finite b -> (0 <= p <= 100)%Z -> fmtF t -> Rabs t <= 1 ->
  (t = 0 \/ bpow radix2 (-900) <= Rabs t) -> Rabs (B a + B b) <= bpow radix2 (- p) * Rabs t ->
  finite (fadd a b) /\ B (fadd a b) = rndF (B a + B b) /\ Rabs (B (fadd a b)) <= bpow radix2 (- p) * Rabs t.
Proof.
  intros Fa Fb Hp Ft Ht1 Ht Hy.
  assert (Hb : bnd 1 0 (B a + B b)).
  { apply bnd0. change (IZR 1) with 1. apply Rle_trans with (bpow radix2 (- p) * Rabs t); [exact Hy | ].
    assert (bpow radix2 (- p) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
    pose proof (Rabs_pos t). nra. }
  destruct (fadd_bnd 1 0 a b Fa Fb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb) as [F [E _]].
  split; [exact F | split; [exact E | ]]. rewrite E. apply rn_scaled; assumption.
Qed.

(** The transcription's tail. *)
Definition tail_of (th tl cH cL g pl : f64) : f64 :=
  fadd (fadd pl (fadd (fmul th cL) (fmul tl cH))) (fmul (fmul th th) g).

Lemma bscale p : (0 <= p)%Z -> bpow radix2 (- p) <= 1.
Proof. intros H. change 1 with (bpow radix2 0). apply bpow_le. lia. Qed.

Lemma tail_facts th tl cH cL g pl :
  finite th -> finite tl -> finite cH -> finite cL -> finite g -> finite pl ->
  Rabs (B th) <= bpow radix2 (-6) -> (B th = 0 \/ bpow radix2 (-900) <= Rabs (B th)) ->
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th) -> Rabs (B pl) <= bpow radix2 (-52) * Rabs (B th) ->
  1 <= B cH <= 2 -> Rabs (B cL) <= bpow radix2 (-50) -> Rabs (B g) <= 2 ->
  finite (tail_of th tl cH cL g pl) /\
  B (tail_of th tl cH cL g pl) = rn (rn (B pl + rn (rn (B th * B cL) + rn (B tl * B cH))) + rn (rn (B th * B th) * B g)) /\
  Rabs (B (tail_of th tl cH cL g pl)) <= bpow radix2 (-4) * Rabs (B th).
Proof.
  intros Ft Fl FH FL Fg Fp T6 Tn Tl Pl H1 CL G.
  assert (Tf : fmtF (B th)) by apply B_fmt.
  assert (T1 : Rabs (B th) <= 1).
  { apply Rle_trans with (bpow radix2 (-6)); [exact T6 | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
  assert (B6 : bpow radix2 (-6) <= 1) by (pose proof (bscale 6 ltac:(lia)); replace (-6)%Z with (- 6)%Z in H by reflexivity; exact H).
  pose proof (Rabs_pos (B th)) as T0.
  (* m1 = th cL *)
  destruct (mul_scaled th cL 50 (B th) Ft FL ltac:(lia) Tf T1 Tn
    ltac:(rewrite Rabs_mult; apply Rle_trans with (Rabs (B th) * bpow radix2 (-50)); [apply Rmult_le_compat_l; [exact T0 | exact CL] | rewrite Rmult_comm; apply Rle_refl]))
    as [Fm1 [Em1 Bm1]].
  (* m2 = tl cH *)
  assert (Hm2 : Rabs (B tl * B cH) <= bpow radix2 (-51) * Rabs (B th)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra.
    assert (E : bpow radix2 (-51) = bpow radix2 (-52) * 2).
    { replace (-51)%Z with (-52 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. reflexivity. }
    rewrite E. pose proof (Rabs_pos (B tl)). assert (Rabs (B tl) * B cH <= Rabs (B tl) * 2) by (apply Rmult_le_compat_l; lra). lra. }
  destruct (mul_scaled tl cH 51 (B th) Fl FH ltac:(lia) Tf T1 Tn Hm2) as [Fm2 [Em2 Bm2]].
  (* m3 = m1 + m2 *)
  assert (Hs49 : bpow radix2 (-50) + bpow radix2 (-51) <= bpow radix2 (-49)).
  { replace (-49)%Z with (-50 + 1)%Z by reflexivity. replace (-51)%Z with (-50 + -1)%Z by reflexivity.
    rewrite !bpow_plus. change (bpow radix2 1) with 2. change (bpow radix2 (-1)) with (/ 2).
    pose proof (bpow_ge_0 radix2 (-50)). lra. }
  destruct (add_scaled (fmul th cL) (fmul tl cH) 49 (B th) Fm1 Fm2 ltac:(lia) Tf T1 Tn
    ltac:(apply Rle_trans with (Rabs (B (fmul th cL)) + Rabs (B (fmul tl cH))); [apply Rabs_triang | pose proof (Rmult_le_compat_r (Rabs (B th)) _ _ T0 Hs49); assert (Bm1' : Rabs (B (fmul th cL)) <= bpow radix2 (-50) * Rabs (B th)) by exact Bm1; assert (Bm2' : Rabs (B (fmul tl cH)) <= bpow radix2 (-51) * Rabs (B th)) by exact Bm2; assert (Gl : bpow radix2 (-49) * Rabs (B th) = bpow radix2 (- (49)) * Rabs (B th)) by reflexivity; lra]))
    as [Fm3 [Em3 Bm3]].
  (* s1 = pl + m3 *)
  assert (Hs48 : bpow radix2 (-52) + bpow radix2 (-49) <= bpow radix2 (-48)).
  { replace (-48)%Z with (-49 + 1)%Z by reflexivity. replace (-52)%Z with (-49 + -3)%Z by reflexivity.
    rewrite !bpow_plus. change (bpow radix2 1) with 2. change (bpow radix2 (-3)) with (/ 8).
    pose proof (bpow_ge_0 radix2 (-49)). lra. }
  assert (Bm3' : Rabs (B (fadd (fmul th cL) (fmul tl cH))) <= bpow radix2 (-49) * Rabs (B th)) by exact Bm3.
  assert (Pl' : Rabs (B pl) <= bpow radix2 (-52) * Rabs (B th)) by exact Pl.
  destruct (add_scaled pl (fadd (fmul th cL) (fmul tl cH)) 48 (B th) Fp Fm3 ltac:(lia) Tf T1 Tn
    ltac:(apply Rle_trans with (Rabs (B pl) + Rabs (B (fadd (fmul th cL) (fmul tl cH)))); [apply Rabs_triang | pose proof (Rmult_le_compat_r (Rabs (B th)) _ _ T0 Hs48); assert (Gl : bpow radix2 (-48) * Rabs (B th) = bpow radix2 (- (48)) * Rabs (B th)) by reflexivity; lra]))
    as [Fs1 [Es1 Bs1]].
  (* t2 = th th *)
  assert (Ht2 : Rabs (B th * B th) <= bpow radix2 (-6) * Rabs (B th)).
  { rewrite Rabs_mult. pose proof (Rmult_le_compat_l (Rabs (B th)) _ _ T0 T6). lra. }
  destruct (mul_scaled th th 6 (B th) Ft Ft ltac:(lia) Tf T1 Tn Ht2) as [Ft2 [Et2 Bt2]].
  (* n = t2 g *)
  assert (Bt2' : Rabs (B (fmul th th)) <= bpow radix2 (-6) * Rabs (B th)) by exact Bt2.
  assert (Hn : Rabs (B (fmul th th) * B g) <= bpow radix2 (-5) * Rabs (B th)).
  { rewrite Rabs_mult. pose proof (Rabs_pos (B (fmul th th))) as H0.
    assert (E5 : bpow radix2 (-5) = bpow radix2 (-6) * 2).
    { replace (-5)%Z with (-6 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. reflexivity. }
    rewrite E5. pose proof (Rmult_le_compat_l (Rabs (B (fmul th th))) _ _ H0 G).
    pose proof (Rabs_pos (B g)). lra. }
  destruct (mul_scaled (fmul th th) g 5 (B th) Ft2 Fg ltac:(lia) Tf T1 Tn Hn) as [Fn [En Bn]].
  (* tail = s1 + n *)
  assert (Bs1' : Rabs (B (fadd pl (fadd (fmul th cL) (fmul tl cH)))) <= bpow radix2 (-48) * Rabs (B th)) by exact Bs1.
  assert (Bn' : Rabs (B (fmul (fmul th th) g)) <= bpow radix2 (-5) * Rabs (B th)) by exact Bn.
  assert (Hs4 : bpow radix2 (-48) + bpow radix2 (-5) <= bpow radix2 (-4)).
  { replace (-4)%Z with (-5 + 1)%Z by reflexivity. replace (-48)%Z with (-5 + -43)%Z by reflexivity.
    rewrite !bpow_plus. change (bpow radix2 1) with 2.
    assert (bpow radix2 (-43) <= 1) by (apply (bscale 43); lia). pose proof (bpow_ge_0 radix2 (-5)). nra. }
  destruct (add_scaled (fadd pl (fadd (fmul th cL) (fmul tl cH))) (fmul (fmul th th) g) 4 (B th) Fs1 Fn ltac:(lia) Tf T1 Tn
    ltac:(apply Rle_trans with (Rabs (B (fadd pl (fadd (fmul th cL) (fmul tl cH)))) + Rabs (B (fmul (fmul th th) g))); [apply Rabs_triang | pose proof (Rmult_le_compat_r (Rabs (B th)) _ _ T0 Hs4); assert (Gl : bpow radix2 (-4) * Rabs (B th) = bpow radix2 (- (4)) * Rabs (B th)) by reflexivity; lra]))
    as [Ftl [Etl Btl]].
  unfold tail_of. refine (conj Ftl (conj _ Btl)).
  rewrite Etl, Es1, En, Et2, Em3, Em1, Em2. reflexivity.
Qed.

(** [th * c_hi]: the exact product split, the low part's bound and [|ph| >= |th|]. *)
Lemma ph_facts th cH : finite th -> finite cH ->
  Rabs (B th) <= bpow radix2 (-6) -> (B th = 0 \/ bpow radix2 (-900) <= Rabs (B th)) -> 1 <= B cH <= 2 ->
  let '(ph, pl) := two_prod64 th cH in
  finite ph /\ finite pl /\ B ph = rndF (B th * B cH) /\ B ph + B pl = B th * B cH /\
  Rabs (B pl) <= bpow radix2 (-52) * Rabs (B th) /\ Rabs (B th) <= Rabs (B ph) /\
  Rabs (B ph) <= 2 * Rabs (B th) * (1 + bpow radix2 (-52)).
Proof.
  intros Ft Fc T6 Tn H1.
  assert (Tm : Rabs (B th * B cH) <= 2 * Rabs (B th)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra. pose proof (Rabs_pos (B th)). nra. }
  assert (Tlo : Rabs (B th) <= Rabs (B th * B cH)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra. pose proof (Rabs_pos (B th)). nra. }
  assert (B6 : bpow radix2 (-6) <= 1) by (apply (bscale 6); lia).
  pose proof (two_prod_ieee (-6) 1 th cH Ft Fc T6 ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 1) with 2; lra) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(destruct Tn as [T0 | T9]; [left; rewrite T0; ring | right; apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | ]; rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra; nra])) as X.
  destruct (two_prod64 th cH) as [ph pl]. destruct X as [Fp [Fl [Ep Ex]]].
  repeat split; try assumption.
  - (* |pl| *)
    assert (Hl : B pl = B th * B cH - B ph) by lra.
    destruct (Req_dec (B th * B cH) 0) as [Z | NZ].
    + assert (B ph = 0) by (rewrite Ep, Z; apply round_0; exact _).
      assert (B pl = 0) by lra. rewrite H0, Rabs_R0.
      pose proof (Rabs_pos (B th)). pose proof (bpow_ge_0 radix2 (-52)). nra.
    + assert (Hn : bpow radix2 (-1022) <= Rabs (B th * B cH)).
      { destruct Tn as [T0 | T9]; [exfalso; apply NZ; rewrite T0; ring | ].
        apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | lra]. }
      pose proof (rnd_rel _ Hn) as R0. assert (R : Rabs (B ph - B th * B cH) <= bpow radix2 (-53) * Rabs (B th * B cH)) by (rewrite Ep; exact R0). rewrite Hl.
      rewrite Rabs_minus_sym. 
      assert (E : bpow radix2 (-52) = bpow radix2 (-53) * 2).
      { replace (-52)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. reflexivity. }
      rewrite E. pose proof (bpow_ge_0 radix2 (-53)). nra.
  - (* |th| <= |ph| *)
    rewrite Ep. rewrite <- round_NE_abs by exact _. 
    assert (Fa : fmtF (Rabs (B th))) by (apply generic_format_abs; apply B_fmt).
    rewrite <- (round_generic radix2 (FLT_exp emin prec) (Znearest ne) (Rabs (B th)) Fa) at 1.
    apply round_le; [exact _ | exact _ | exact Tlo].
  - destruct (Req_dec (B th * B cH) 0) as [Z | NZ].
    + assert (B ph = 0) by (rewrite Ep, Z; apply round_0; exact _). rewrite H, Rabs_R0.
      pose proof (Rabs_pos (B th)). pose proof (bpow_ge_0 radix2 (-52)). nra.
    + assert (Hn : bpow radix2 (-1022) <= Rabs (B th * B cH)).
      { destruct Tn as [T0 | T9]; [exfalso; apply NZ; rewrite T0; ring | ].
        apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | lra]. }
      pose proof (rnd_rel _ Hn) as R0. assert (R : Rabs (B ph - B th * B cH) <= bpow radix2 (-53) * Rabs (B th * B cH)) by (rewrite Ep; exact R0).
      pose proof (Rabs_triang_inv (B ph) (B th * B cH)) as Ti.
      assert (E : bpow radix2 (-52) = bpow radix2 (-53) * 2).
      { replace (-52)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. reflexivity. }
      pose proof (bpow_ge_0 radix2 (-53)). pose proof (Rabs_pos (B th)).
      assert (Rabs (B ph) <= Rabs (B th * B cH) + bpow radix2 (-53) * Rabs (B th * B cH)) by (pose proof (Rabs_triang_inv2 (B ph) (B th * B cH)); lra).
      nra.
Qed.

Lemma b2 : bpow radix2 2 = 4.
Proof. replace 2%Z with (1 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. lra. Qed.

Lemma Rabs_big x e m : Rabs x <= bpow radix2 e -> (e <= m)%Z -> Rabs x <= bpow radix2 m.
Proof. intros H Hm. apply Rle_trans with (bpow radix2 e); [exact H | apply bpow_le; exact Hm]. Qed.

Lemma sl_nonneg T a : 0 <= T -> 0 <= sl T a.
Proof.
  intros HT. induction a as [|c a IH]; simpl; [lra | ].
  pose proof (bl_nonneg T a HT). assert (0 <= T * sl T a) by nra. lra.
Qed.

Lemma rn_B x : rn (B x) = B x.
Proof. apply round_generic; [exact _ | apply B_fmt]. Qed.

(** The transcription's segment branch after [t = th + tl]. *)
Definition seg_result (th tl c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 : f64) : f64 * f64 :=
  let g := hf th g0 g1 g2 g3 g4 g5 g6 g7 g8 in
  let '(ph, pl) := two_prod64 th cH in
  let tail := tail_of th tl cH cL g pl in
  let '(yh, yl) := two_sum64 c0 c1 in
  let '(vh, vl) := fast_two_sum64 ph tail in
  add64 yh yl vh vl.

Definition seg_poly (g0 g1 g2 g3 g4 g5 g6 g7 g8 : f64) : list R :=
  [B g0; B g1; B g2; B g3; B g4; B g5; B g6; B g7; B g8].

Theorem segment_eval th tl c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 (bound dgb : R) :
  finite th -> finite tl -> finite c0 -> finite c1 -> finite cH -> finite cL ->
  finite g0 -> finite g1 -> finite g2 -> finite g3 -> finite g4 -> finite g5 -> finite g6 -> finite g7 -> finite g8 ->
  Rabs (B th) <= 0.0078126 -> (B th = 0 \/ bpow radix2 (-900) <= Rabs (B th)) ->
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th) -> Rabs (B tl) <= 8.7e-19 -> Rabs (B th + B tl) <= 0.0078126 ->
  1 <= B cH <= 2 -> Rabs (B cL) <= bpow radix2 (-50) ->
  Rabs (B g0) <= bpow radix2 11 -> Rabs (B g1) <= bpow radix2 11 -> Rabs (B g2) <= bpow radix2 11 ->
  Rabs (B g3) <= bpow radix2 11 -> Rabs (B g4) <= bpow radix2 11 -> Rabs (B g5) <= bpow radix2 11 ->
  Rabs (B g6) <= bpow radix2 11 -> Rabs (B g7) <= bpow radix2 11 -> Rabs (B g8) <= bpow radix2 11 ->
  Rabs (B c0) <= 2 -> Rabs (B c1) <= 2 ->
  EvalCert (B cH) (B cL) (B g0) (B g1) (B g2) (B g3) (B g4) (B g5) (B g6) (B g7) (B g8) bound dgb ->
  sl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) * 8.7e-19 <= dgb ->
  let t := B th + B tl in
  Rabs ((B cH + B cL) * t + t * t * pl (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) t) + bound < B c0 + B c1 ->
  exists h l, seg_result th tl c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 = (h, l) /\ finite h /\ finite l /\
    exists e1 ea, Rabs e1 <= bound /\ Rabs ea <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) /\
    B h + B l = (B c0 + B c1 + ((B cH + B cL) * t + t * t * pl (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) t) + e1) * (1 + ea).
Proof.
  intros Ft Fl F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 Th Tn Tl1 Tl2 Tt H1 CL G0 G1 G2 G3 G4 G5 G6 G7 G8 C0 C1 EC Hdg t HS.
  assert (T6 : Rabs (B th) <= bpow radix2 (-6)) by (rewrite bm6; lra).
  assert (Dg0 : 0 <= dgb) by (pose proof (sl_nonneg 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) ltac:(lra)); nra).
  destruct (horner_chain th g0 g1 g2 g3 g4 g5 g6 g7 g8 Ft Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 T6 G0 G1 G2 G3 G4 G5 G6 G7 G8)
    as [Fg [Eg Bg]]. cbv zeta in Eg, Bg.
  assert (Hh : Rabs (B (hf th g0 g1 g2 g3 g4 g5 g6 g7 g8)) <= 2).
  { destruct (Rabs_le_inv _ _ Th) as [Tha Thb]. destruct (Rabs_le_inv _ _ Tl2) as [Tla Tlb].
    destruct (EC (B th) (B tl) 0 ltac:(split; lra) ltac:(split; lra) ltac:(split; [lra | lra])) as [_ H2].
    cbv zeta in H2. rewrite !rn_B in H2. rewrite Eg. exact H2. }
  pose proof (ph_facts th cH Ft FH T6 Tn H1) as PH.
  destruct (two_prod64 th cH) as [ph pq] eqn:Eprod. destruct PH as [Fp [Fq [Ep [Ex [Pl [PhLo PhHi]]]]]].
  destruct (tail_facts th tl cH cL (hf th g0 g1 g2 g3 g4 g5 g6 g7 g8) pq Ft Fl FH FL Fg Fq T6 Tn Tl1 Pl H1 CL Hh)
    as [Ftl [Etail Btail]].
  set (tl_ := tail_of th tl cH cL (hf th g0 g1 g2 g3 g4 g5 g6 g7 g8) pq) in *.
  destruct (Rabs_le_inv _ _ Th) as [Tha Thb]. destruct (Rabs_le_inv _ _ Tl2) as [Tla Tlb].
  (* EvalCert at dg = G(th + tl) - G(th) *)
  set (L := seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) in *.
  assert (Hdiff : Rabs (pl L (B th + B tl) - pl L (B th)) <= dgb).
  { pose proof (pl_diff 0.0078126 L (B th) (B th + B tl) ltac:(lra) Th Tt) as D.
    replace (B th + B tl - B th) with (B tl) in D by ring.
    pose proof (sl_nonneg 0.0078126 L ltac:(lra)).
    assert (sl 0.0078126 L * Rabs (B tl) <= sl 0.0078126 L * 8.7e-19) by (apply Rmult_le_compat_l; assumption).
    lra. }
  destruct (Rabs_le_inv _ _ Hdiff) as [Dga Dgb].
  destruct (EC (B th) (B tl) (pl L (B th + B tl) - pl L (B th)) ltac:(split; lra) ltac:(split; lra) ltac:(split; lra)) as [Eb _].
  cbv zeta in Eb. rewrite !rn_B in Eb.
  assert (Ephr : rn (B th * B cH) = B ph) by (rewrite Ep; reflexivity).
  rewrite Ephr in Eb.
  assert (Epq : B pq = B th * B cH - B ph) by lra.
  rewrite Epq, Eg in Etail.
  match type of Eb with
  | Rabs (?A - ?V) <= _ =>
      assert (HA : B tl_ = A) by (rewrite Etail; reflexivity);
      assert (HF : B ph + V = (B cH + B cL) * t + t * t * pl L t) by (unfold t; unfold L, seg_poly; simpl pl; nra);
      rewrite <- HA in Eb;
      set (Vv := V) in *
  end.
  (* the fast sum of ph and the tail *)
  assert (Hmag : Rabs (B th) <= 0.0078126) by exact Th.
  assert (B4 : bpow radix2 (-4) <= 1) by (apply (bscale 4); lia).
  pose proof (Rabs_pos (B th)) as Th0.
  pose proof (Rmult_le_compat_r (Rabs (B th)) _ _ Th0 B4) as B4'.
  assert (Hlow : Rabs (B tl_) <= Rabs (B ph)) by lra.
  assert (Hph1 : Rabs (B ph) <= 0.016) by (rewrite bm52 in PhHi; lra).
  assert (Hsum1 : Rabs (B ph) + Rabs (B tl_) <= bpow radix2 0).
  { change (bpow radix2 0) with 1. lra. }
  assert (Hsum1' : Rabs (B ph + B tl_) <= 1) by (pose proof (Rabs_triang (B ph) (B tl_)); change (bpow radix2 0) with 1 in Hsum1; lra).
  assert (Hph21 : Rabs (B ph) <= bpow radix2 1021) by (apply Rabs_big with 0%Z; [change (bpow radix2 0) with 1; lra | lia]).
  assert (Htl21 : Rabs (B tl_) <= bpow radix2 1021) by (apply Rabs_big with 0%Z; [change (bpow radix2 0) with 1; lra | lia]).
  pose proof (fast_two_sum_ieee ph tl_ Fp Ftl Hph21 Htl21 (or_intror (or_introl Hlow))) as FS.
  destruct (addS ph tl_ 0 Fp Ftl Hsum1 ltac:(lia) ltac:(lia)) as [_ [Efv Bvh]].
  destruct (fast_two_sum64 ph tl_) as [vh vl] eqn:Efs. destruct FS as [Fvh [Fvl [Evh Evs]]].
  (* the leading double-word *)
  assert (C4 : Rabs (B c0) + Rabs (B c1) <= bpow radix2 2) by (rewrite b2; lra).
  destruct (addS c0 c1 2 F0 F1 C4 ltac:(lia) ltac:(lia)) as [_ [Efy Byh]].
  pose proof (two_sum_ieee c0 c1 F0 F1 (Rabs_big (B c0) 1 1020%Z ltac:(change (bpow radix2 1) with 2; lra) ltac:(lia))
    (Rabs_big (B c1) 1 1020%Z ltac:(change (bpow radix2 1) with 2; lra) ltac:(lia))) as TS.
  destruct (two_sum64 c0 c1) as [yh yl] eqn:Ey. destruct TS as [Fyh [Fyl [Eyh Eys]]].
  assert (Hyh : B yh = rndF (B yh + B yl)) by (rewrite Eys; exact Eyh).
  assert (Hvh : B vh = rndF (B vh + B vl)) by (rewrite Evs; exact Evh).
  (* magnitudes for add_ieee *)
  assert (Byh' : Rabs (B yh) <= 4) by (rewrite Eyh, <- Efy, <- b2; exact Byh).
  assert (Bvh' : Rabs (B vh) <= 1) by (rewrite Evh, <- Efv; change 1 with (bpow radix2 0); exact Bvh).
  destruct (Rabs_le_inv _ _ Byh') as [Ya Yb]. destruct (Rabs_le_inv _ _ Bvh') as [Va Vb].
  destruct (Rabs_le_inv _ _ C0) as [C0a C0b]. destruct (Rabs_le_inv _ _ C1) as [C1a C1b].
  assert (Byl' : Rabs (B yl) <= 8) by (apply Rabs_le; split; lra).
  assert (Bvl' : Rabs (B vl) <= 2).
  { destruct (Rabs_le_inv _ _ Hsum1') as [Sa Sb]. apply Rabs_le; split; lra. }
  assert (b3 : bpow radix2 3 = 8) by (replace 3%Z with (2 + 1)%Z by reflexivity; rewrite bpow_plus, b2; change (bpow radix2 1) with 2; lra).
  assert (big8 : forall x, Rabs x <= 8 -> Rabs x <= bpow radix2 1016) by (intros x Hx; apply Rabs_big with 3%Z; [rewrite b3; exact Hx | lia]).
  set (Fx := (B cH + B cL) * t + t * t * pl L t) in *.
  destruct (Rabs_le_inv Fx (Rabs Fx) (Rle_refl _)) as [Fxa Fxb].
  destruct (Rabs_le_inv _ _ Eb) as [Ea1 Eb1].
  clearbody Fx Vv.
  assert (HS' : B yh + B yl + (B vh + B vl) = B c0 + B c1 + Fx + (B tl_ - Vv)) by (rewrite Eys, Evs, <- HF; ring).
  assert (Hne : B yh + B yl + (B vh + B vl) <> 0) by (rewrite HS'; lra).
  pose proof (add_ieee yh yl vh vl Fyh Fyl Hyh Fvh Fvl Hvh (big8 (B yh) ltac:(lra)) (big8 (B yl) Byl') (big8 (B vh) ltac:(lra)) (big8 (B vl) ltac:(lra)) Hne) as AD.
  destruct (add64 yh yl vh vl) as [zh zl] eqn:Ea. destruct AD as [Fzh [Fzl Err]].
  exists zh, zl. split; [ | split; [exact Fzh | split; [exact Fzl | ]]].
  - unfold seg_result. cbv zeta. rewrite Eprod, Ey. fold tl_. rewrite Efs. exact Ea.
  - exists (B tl_ - Vv), ((B zh + B zl - (B yh + B yl + (B vh + B vl))) / (B yh + B yl + (B vh + B vl))).
    split; [exact Eb | split; [exact Err | ]].
    rewrite <- HS'. field. exact Hne.
Qed.

(** A table row's hypotheses on its coefficients, with the certificate's
    absolute bound [bound] on the tail's evaluation error. *)
Definition SegOk (c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 : f64) (bound : R) : Prop :=
  finite c0 /\ finite c1 /\ finite cH /\ finite cL /\ finite g0 /\ finite g1 /\ finite g2 /\ finite g3 /\
  finite g4 /\ finite g5 /\ finite g6 /\ finite g7 /\ finite g8 /\
  Rabs (B c0) <= 2 /\ Rabs (B c1) <= 2 /\ (1 <= B cH <= 2) /\ Rabs (B cL) <= bpow radix2 (-50) /\
  Rabs (B g0) <= bpow radix2 11 /\ Rabs (B g1) <= bpow radix2 11 /\ Rabs (B g2) <= bpow radix2 11 /\
  Rabs (B g3) <= bpow radix2 11 /\ Rabs (B g4) <= bpow radix2 11 /\ Rabs (B g5) <= bpow radix2 11 /\
  Rabs (B g6) <= bpow radix2 11 /\ Rabs (B g7) <= bpow radix2 11 /\ Rabs (B g8) <= bpow radix2 11 /\
  exists dgb, EvalCert (B cH) (B cL) (B g0) (B g1) (B g2) (B g3) (B g4) (B g5) (B g6) (B g7) (B g8) bound dgb /\
    sl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) * 8.7e-19 <= dgb /\
    (B cH + Rabs (B cL)) * 0.0078126 + 0.0078126 * 0.0078126 * bl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) + bound
      < B c0 + B c1.

(** The polynomial part of a segment's value stays small. *)
Lemma fx_small cH cL c01 bound (L : list R) t : 1 <= cH -> Rabs t <= 0.0078126 ->
  (cH + Rabs cL) * 0.0078126 + 0.0078126 * 0.0078126 * bl 0.0078126 L + bound < c01 ->
  Rabs ((cH + cL) * t + t * t * pl L t) + bound < c01.
Proof.
  intros H1 T S.
  pose proof (pl_bound 0.0078126 L t ltac:(lra) T) as P. pose proof (bl_nonneg 0.0078126 L ltac:(lra)) as B0.
  pose proof (Rabs_pos t). pose proof (Rabs_pos cL). pose proof (Rabs_pos (pl L t)).
  apply Rle_lt_trans with (Rabs ((cH + cL) * t) + Rabs (t * t * pl L t) + bound); [pose proof (Rabs_triang ((cH + cL) * t) (t * t * pl L t)); lra | ].
  rewrite !Rabs_mult.
  assert (Rabs (cH + cL) <= cH + Rabs cL).
  { apply Rle_trans with (Rabs cH + Rabs cL); [apply Rabs_triang | rewrite (Rabs_pos_eq cH) by lra; lra]. }
  assert (Rabs (cH + cL) * Rabs t <= (cH + Rabs cL) * 0.0078126) by (apply Rmult_le_compat; try apply Rabs_pos; lra).
  assert (Rabs t * Rabs t * Rabs (pl L t) <= 0.0078126 * 0.0078126 * bl 0.0078126 L).
  { assert (Q : Rabs t * Rabs t <= 0.0078126 * 0.0078126) by (apply Rmult_le_compat; try apply Rabs_pos; lra).
    assert (Q0 : 0 <= Rabs t * Rabs t) by (apply Rmult_le_pos; apply Rabs_pos).
    apply Rmult_le_compat; [exact Q0 | apply Rabs_pos | exact Q | exact P]. }
  lra.
Qed.

(** [SegOk] for the words of a table row. *)
Definition SegOkRow (row : list Z) (bound : R) : Prop :=
  let c := fun j => aw (nth j row 0%Z) in
  SegOk (c 0%nat) (c 1%nat) (c 2%nat) (c 3%nat) (c 4%nat) (c 5%nat) (c 6%nat) (c 7%nat) (c 8%nat) (c 9%nat)
    (c 10%nat) (c 11%nat) (c 12%nat) bound.

(** [asin_series] on a segment: the exact value it computes, up to the
    certificate's bound and one double-word addition's rounding. *)
Theorem series_segment zh zl (k : Z) (bound : R) : (1 <= k <= 45)%Z ->
  finite zh -> finite zl -> / 128 <= B zh -> B zh <= 0.7072 -> Znearest ne (B zh * 64) = k ->
  Rabs (B zl) <= bpow radix2 (-60) -> (B zl = 0 \/ bpow radix2 (-900) <= Rabs (B zl)) ->
  SegOkRow (nth (Z.to_nat (k - 1)) asin_segments []) bound ->
  let row := nth (Z.to_nat (k - 1)) asin_segments [] in
  let c := fun j => aw (nth j row 0%Z) in
  let t := (B zh - IZR k / 64) + B zl in
  exists h l, asin_series zh zl = (h, l) /\ finite h /\ finite l /\ Rabs t <= 0.0078126 /\
    exists e1 ea, Rabs e1 <= bound /\ Rabs ea <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) /\
    B h + B l = (B (c 0%nat) + B (c 1%nat)
      + ((B (c 2%nat) + B (c 3%nat)) * t + t * t * pl (seg_poly (c 4%nat) (c 5%nat) (c 6%nat) (c 7%nat) (c 8%nat) (c 9%nat) (c 10%nat) (c 11%nat) (c 12%nat)) t)
      + e1) * (1 + ea).
Proof.
  intros Hk Fz Fl L U Hn Hl Hln SO row c t.
  destruct (segment_reduction zh zl k Hk Fz Fl L U Hn Hl Hln) as [Cgt [Ix [Fa [Ea [Fs [Es [Gr Hd]]]]]]].
  set (i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter) in *.
  assert (Hx' : Rabs (B (fsub zh (fmul i asin_inv64))) <= / 128) by (rewrite Es; exact Hd).
  assert (Hxn : B (fsub zh (fmul i asin_inv64)) = 0 \/ bpow radix2 (-59) <= Rabs (B (fsub zh (fmul i asin_inv64)))) by (rewrite Es; exact Gr).
  pose proof (t_split (fsub zh (fmul i asin_inv64)) zl Fs Fl Hx' Hxn Hl Hln) as TS.
  destruct (two_sum64 (fsub zh (fmul i asin_inv64)) zl) as [th tl] eqn:Ets.
  destruct TS as [Fth [Ftl [Eth [Esum [Th [Tl2 [Tn Tl1]]]]]]].
  assert (Etsum : B th + B tl = t) by (unfold t; rewrite Esum, Es; reflexivity).
  assert (Htt : Rabs (B th + B tl) <= 0.0078126).
  { rewrite Etsum. unfold t. destruct (Rabs_le_inv _ _ Hd) as [Hd1 Hd2]. destruct (Rabs_le_inv _ _ Hl) as [Hl1 Hl2].
    rewrite bm60 in *. apply Rabs_le. split; lra. }
  unfold SegOkRow in SO. cbv zeta in SO.
  destruct SO as [F0 [F1 [FH [FL [Fg0 [Fg1 [Fg2 [Fg3 [Fg4 [Fg5 [Fg6 [Fg7 [Fg8 [C0 [C1 [H1 [CL [G0 [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [dgb [EC [Hdg HSn]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  pose proof (fx_small _ _ _ _ _ (B th + B tl) (proj1 H1) Htt HSn) as HS.
  pose proof (segment_eval th tl _ _ _ _ _ _ _ _ _ _ _ _ _ bound dgb Fth Ftl F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8
    Th Tn Tl1 Tl2 Htt H1 CL G0 G1 G2 G3 G4 G5 G6 G7 G8 C0 C1 EC Hdg HS) as SE.
  destruct SE as [h [l [Hres [Fh [Fl2 [e1 [ea [E1 [Eea Eq]]]]]]]]].
  refine (ex_intro _ h (ex_intro _ l (conj _ (conj Fh (conj Fl2 (conj _ _)))))).
  - rewrite <- Hres. unfold asin_series. cbv zeta. fold i. rewrite Cgt, Ix, Ets. unfold seg_result, hf, tail_of. cbv zeta. simpl Z.to_nat. reflexivity.
  - rewrite <- Etsum. exact Htt.
  - exists e1, ea. rewrite <- Etsum. exact (conj E1 (conj Eea Eq)).
Qed.

(** A table word as a finite binary64 whose value is [M * 2^E]; [m], [k] are the
    word's decoded mantissa and exponent. *)
Lemma word_ok_intro n (s : bool) (m : positive) (k : nat) (M d E : Z) :
  binary_float_of_bits_aux 52 11 n = F754_finite s m (- Z.of_nat k) ->
  cond_Zopp s (Zpos m) = (M * 2 ^ d)%Z -> (0 <= d)%Z -> E = (- Z.of_nat k + d)%Z ->
  finite (aw n) /\ B (aw n) = IZR M * bpow radix2 E.
Proof.
  intros D Hm Hd HE. split.
  - exact (bits_finite n s m (- Z.of_nat k) D).
  - unfold aw. rewrite (bits_val n s m k D). rewrite Hm, HE, bpow_plus, mult_IZR.
    assert (Hp : IZR (2 ^ d) = bpow radix2 d) by (apply (IZR_Zpower radix2); exact Hd).
    rewrite Hp, bpow_negn. field. apply pow_nonzero. lra.
Qed.

Lemma segok_from_values c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 bound dgb : R) :
  finite c0 -> finite c1 -> finite cH -> finite cL -> finite g0 -> finite g1 -> finite g2 -> finite g3 ->
  finite g4 -> finite g5 -> finite g6 -> finite g7 -> finite g8 ->
  B c0 = r0 -> B c1 = r1 -> B cH = rH -> B cL = rL -> B g0 = q0 -> B g1 = q1 -> B g2 = q2 -> B g3 = q3 ->
  B g4 = q4 -> B g5 = q5 -> B g6 = q6 -> B g7 = q7 -> B g8 = q8 ->
  Rabs r0 <= 2 -> Rabs r1 <= 2 -> (1 <= rH <= 2) -> Rabs rL <= bpow radix2 (-50) ->
  Rabs q0 <= bpow radix2 11 -> Rabs q1 <= bpow radix2 11 -> Rabs q2 <= bpow radix2 11 ->
  Rabs q3 <= bpow radix2 11 -> Rabs q4 <= bpow radix2 11 -> Rabs q5 <= bpow radix2 11 ->
  Rabs q6 <= bpow radix2 11 -> Rabs q7 <= bpow radix2 11 -> Rabs q8 <= bpow radix2 11 ->
  EvalCert rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 bound dgb ->
  sl 0.0078126 [q0; q1; q2; q3; q4; q5; q6; q7; q8] * 8.7e-19 <= dgb ->
  (rH + Rabs rL) * 0.0078126 + 0.0078126 * 0.0078126 * bl 0.0078126 [q0; q1; q2; q3; q4; q5; q6; q7; q8] + bound < r0 + r1 ->
  SegOk c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 bound.
Proof.
  intros F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 V0 V1 VH VL W0 W1 W2 W3 W4 W5 W6 W7 W8
    A0 A1 AH AL B0 B1 B2 B3 B4 B5 B6 B7 B8 EC Hs Hn.
  unfold SegOk. rewrite V0, V1, VH, VL, W0, W1, W2, W3, W4, W5, W6, W7, W8. unfold seg_poly. rewrite W0, W1, W2, W3, W4, W5, W6, W7, W8.
  destruct AH as [AH1 AH2]. repeat split; try assumption.
  exists dgb. exact (conj EC (conj Hs Hn)).
Qed.

(** The numeric facts of [SegOkRow]: powers of two as literals, then interval
    arithmetic over the exact table values. *)
Ltac seg_numeric := cbn [sl bl]; bpow_num; try split; interval with (i_prec 60).
