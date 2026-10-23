(** atan2's table segments: the reduction to [t = z - k/64] and the generic
    evaluation, [AsinSegment]'s with the table of 64 segments over [zh <= 1], the
    derivative word [c_hi] in [[1/2, 1]] (the derivative of [atan] falls from 1 to
    1/2) and the reduced argument's lower bound [2^-899] (all the segment branch
    needs). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error Sterbenz IEEE754.Binary IEEE754.Bits.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingCore.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel AsinSqrtStep AsinNormal AsinSeriesSmall ExpReduction AsinSegment Atan2Tables Atan2Kernel.
Import ListNotations.
Open Scope R_scope.

(** The second [two_sum] of the segment branch: [t = th + tl] is the exact
    sum of [x' = z - k/64] and [zl], [th] is within [0.0078126] and [tl] within
    [8.7e-19]. [x'] is a multiple of [2^-59] and [zl] of [2^-211] (a double-word
    low part is within [2^-53] of nothing finer), so a nonzero sum is at least
    [2^-211] and neither cancellation nor underflow reaches [th]. *)
Lemma t_split_a x' zl : finite x' -> finite zl -> Rabs (B x') <= / 128 -> on_grid (-59) (B x') ->
  Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  let '(th, tl) := two_sum64 x' zl in
  finite th /\ finite tl /\ B th = rndF (B x' + B zl) /\ B th + B tl = B x' + B zl /\
  Rabs (B th) <= 0.0078126 /\ Rabs (B tl) <= 8.7e-19 /\ (B th = 0 \/ bpow radix2 (-899) <= Rabs (B th)) /\
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th).
Proof.
  intros Fx Fz Hx Gx Hz Gz.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53.
  assert (Hts := two_sum_ieee x' zl Fx Fz
    ltac:(apply Rle_trans with 1; [apply Rle_trans with (/ 128); [exact Hx | lra] | change 1 with (bpow radix2 0); apply bpow_le; lia])
    ltac:(apply Rle_trans with (bpow radix2 (-53)); [exact Hz | apply bpow_le; lia])).
  destruct (two_sum64 x' zl) as [th tl] eqn:E. cbv beta iota in Hts. destruct Hts as [Fth [Ftl [Eth Esum]]].
  refine (conj Fth (conj Ftl (conj Eth (conj Esum _)))).
  assert (Gs : on_grid (-211) (B x' + B zl)) by (apply grid_plus; [apply (grid_le (-59)); [lia | exact Gx] | exact Gz]).
  destruct (Req_dec (B x' + B zl) 0) as [Z0 | NZ].
  - assert (T0 : B th = 0) by (rewrite Eth, Z0; apply round_0; exact _).
    assert (L0 : B tl = 0) by lra.
    rewrite T0, L0. rewrite Rabs_R0. split; [lra | split; [lra | split; [left; reflexivity | lra]]].
  - assert (Hx1 : bpow radix2 (-211) <= Rabs (B x' + B zl)) by exact (grid_nonzero _ _ Gs NZ).
    assert (Hx2 : bpow radix2 (-1022) <= Rabs (B x' + B zl)) by (apply Rle_trans with (bpow radix2 (-211)); [apply bpow_le; lia | exact Hx1]).
    pose proof (rnd_rel _ Hx2) as R. change (RNE (B x' + B zl)) with (rndF (B x' + B zl)) in R.
    rewrite <- Eth in R.
    assert (Etl : B tl = (B x' + B zl) - B th) by lra.
    rewrite P53 in R.
    assert (Hxa : Rabs (B x' + B zl) <= / 128 + / 9007199254740992).
    { apply Rle_trans with (Rabs (B x') + Rabs (B zl)); [apply Rabs_triang | rewrite P53 in Hz; lra]. }
    assert (Htl : Rabs (B tl) <= 8.7e-19).
    { rewrite Etl. rewrite Rabs_minus_sym.
      apply Rle_trans with (/ 9007199254740992 * Rabs (B x' + B zl)); [exact R | ].
      apply Rle_trans with (/ 9007199254740992 * (/ 128 + / 9007199254740992)).
      - apply Rmult_le_compat_l; [lra | exact Hxa].
      - lra. }
    split; [ | split; [exact Htl | split; [ | ]]].
    + assert (Hth : B th = (B x' + B zl) - B tl) by lra.
      apply Rabs_le. apply Rabs_le_inv in Htl. apply Rabs_le_inv in Hxa. lra.
    + right. rewrite Eth. rewrite <- round_NE_abs by exact _.
      apply Rle_trans with (bpow radix2 (-211)); [apply bpow_le; lia | ].
      rewrite <- (round_generic radix2 (FLT_exp emin prec) (Znearest ne) (bpow radix2 (-211)) (fmt_bpow (-211) ltac:(lia))) at 1.
      apply round_le; [exact _ | exact _ | exact Hx1].
    + assert (Etl' : Rabs (B tl) <= / 9007199254740992 * Rabs (B x' + B zl)) by (rewrite Etl; rewrite Rabs_minus_sym; exact R).
      replace (B x' + B zl) with (B th + B tl) in Etl' by lra.
      pose proof (Rabs_triang (B th) (B tl)) as Tr. pose proof (Rabs_pos (B tl)). pose proof (Rabs_pos (B th)).
      rewrite bm52.
      assert (Rabs (B th + B tl) <= Rabs (B th) + Rabs (B tl)) by exact Tr.
      nra.
Qed.


(** [i / 64] is exact for the table index [i = k]. *)
Lemma scaled_index_exact_a i k : finite i -> B i = IZR k -> (1 <= k <= 64)%Z ->
  finite (fmul i asin_inv64) /\ B (fmul i asin_inv64) = IZR k / 64.
Proof.
  intros Fi Bi Hk. destruct inv64_val as [V F].
  assert (Hk1 : 1 <= IZR k) by (change 1 with (IZR 1); apply IZR_le; lia).
  assert (Hk2 : IZR k <= 64) by (change 64 with (IZR 64); apply IZR_le; lia).
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
Lemma sub_table_exact_a zh a k : finite zh -> finite a -> B a = IZR k / 64 -> (1 <= k <= 64)%Z ->
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


(** The segment branch's reduction: for [zh] in [[1/128, 1]] with index [k]
    the transcription forms [th + tl = (zh - k/64) + zl] exactly. *)
Lemma segment_reduction_a zh (k : Z) : (1 <= k <= 64)%Z ->
  finite zh -> / 128 <= B zh -> B zh <= 1 -> Znearest ne (B zh * 64) = k ->
  let i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter in
  asin_cmp i asin_zero = Some Gt /\ asin_index i = k /\
  finite (fmul i asin_inv64) /\ B (fmul i asin_inv64) = IZR k / 64 /\
  finite (fsub zh (fmul i asin_inv64)) /\ B (fsub zh (fmul i asin_inv64)) = B zh - IZR k / 64 /\
  on_grid (-59) (B zh - IZR k / 64) /\
  Rabs (B zh - IZR k / 64) <= / 128.
Proof.
  intros Hk Fz L U Hn i.
  destruct (index_value zh Fz L ltac:(lra)) as [Fi Ei]. rewrite Hn in Ei.
  fold i in Fi, Ei.
  assert (Hk1 : 1 <= IZR k) by (change 1 with (IZR 1); apply IZR_le; lia).
  assert (Hk2 : IZR k <= 64) by (change 64 with (IZR 64); apply IZR_le; lia).
  (* comparison with zero *)
  destruct zero_val as [Bz Fzero].
  assert (Cgt : asin_cmp i asin_zero = Some Gt).
  { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 i asin_zero Fi Fzero), Ei, Bz. rewrite Rcompare_Gt; [reflexivity | lra]. }
  assert (Ix : asin_index i = k) by (apply asin_index_ok; [exact Fi | exact Ei | lia]).
  destruct (scaled_index_exact_a i k Fi Ei Hk) as [Fa Ea].
  assert (Hd : Rabs (B zh - IZR k / 64) <= / 128).
  { pose proof (Znearest_half (fun n => negb (Z.even n)) (B zh * 64)) as H. fold ne in H. rewrite Hn in H.
    apply Rabs_le_inv in H. apply Rabs_le. lra. }
  destruct (sub_table_exact_a zh (fmul i asin_inv64) k Fz Fa Ea Hk Hd) as [Fs Es].
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
  exact (grid_minus _ _ _ G1 G2).
Qed.


Lemma tail_facts_a th tl cH cL g pl :
  finite th -> finite tl -> finite cH -> finite cL -> finite g -> finite pl ->
  Rabs (B th) <= bpow radix2 (-6) -> (B th = 0 \/ bpow radix2 (-899) <= Rabs (B th)) ->
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th) -> Rabs (B pl) <= bpow radix2 (-52) * Rabs (B th) ->
  1 / 2 <= B cH <= 1 -> Rabs (B cL) <= bpow radix2 (-50) -> Rabs (B g) <= 2 ->
  finite (tail_of th tl cH cL g pl) /\
  B (tail_of th tl cH cL g pl) = rn (rn (B pl + rn (rn (B th * B cL) + rn (B tl * B cH))) + rn (rn (B th * B th) * B g)) /\
  Rabs (B (tail_of th tl cH cL g pl)) <= bpow radix2 (-4) * Rabs (B th).
Proof.
  intros Ft Fl FH FL Fg Fp T6 Tn899 Tl Pl H1 CL G.
  assert (Tn : B th = 0 \/ bpow radix2 (-900) <= Rabs (B th)).
  { destruct Tn899 as [T0 | T1]; [left; exact T0 | right; apply Rle_trans with (bpow radix2 (-899)); [apply bpow_le; lia | exact T1]]. }
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


(** [th * c_hi]: the exact product split, the low part's bound and [|ph| >= |th|/4]. *)
Lemma ph_facts_a th cH : finite th -> finite cH ->
  Rabs (B th) <= bpow radix2 (-6) -> (B th = 0 \/ bpow radix2 (-899) <= Rabs (B th)) -> 1 / 2 <= B cH <= 1 ->
  let '(ph, pl) := two_prod64 th cH in
  finite ph /\ finite pl /\ B ph = rndF (B th * B cH) /\ B ph + B pl = B th * B cH /\
  Rabs (B pl) <= bpow radix2 (-52) * Rabs (B th) /\ Rabs (B th) / 4 <= Rabs (B ph) /\
  Rabs (B ph) <= 2 * Rabs (B th) * (1 + bpow radix2 (-52)).
Proof.
  intros Ft Fc T6 Tn H1.
  assert (Tm : Rabs (B th * B cH) <= 2 * Rabs (B th)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra. pose proof (Rabs_pos (B th)). nra. }
  assert (Tlo : Rabs (B th) / 2 <= Rabs (B th * B cH)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B cH)) by lra. pose proof (Rabs_pos (B th)). nra. }
  assert (B6 : bpow radix2 (-6) <= 1) by (apply (bscale 6); lia).
  assert (b899 : bpow radix2 (-899) = 2 * bpow radix2 (-900)).
  { replace (-899)%Z with (-900 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (Thc : B th * B cH = 0 \/ bpow radix2 (-900) <= Rabs (B th * B cH)).
  { destruct Tn as [T0 | T9]; [left; rewrite T0; ring | right; pose proof (bpow_gt_0 radix2 (-900)); lra]. }
  assert (Thd : in_two_prod_domain (B th) (B cH)).
  { unfold in_two_prod_domain. destruct Thc as [Z | T9]; [left; exact Z | right; apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | exact T9]]. }
  pose proof (two_prod_ieee (-6) 1 th cH Ft Fc T6 ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 1) with 2; lra) ltac:(lia) ltac:(lia) ltac:(lia) Thd) as X.
  destruct (two_prod64 th cH) as [ph pl]. destruct X as [Fp [Fl [Ep Ex]]].
  assert (Hrel : Rabs (B th * B cH) = 0 \/ Rabs (B ph - B th * B cH) <= bpow radix2 (-53) * Rabs (B th * B cH)).
  { destruct (Req_dec (B th * B cH) 0) as [Z | NZ].
    - left. rewrite Z. apply Rabs_R0.
    - right. assert (Hn : bpow radix2 (-1022) <= Rabs (B th * B cH)).
      { destruct Thc as [Z | T9]; [exfalso; apply NZ; exact Z | apply Rle_trans with (bpow radix2 (-900)); [apply bpow_le; lia | exact T9]]. }
      pose proof (rnd_rel _ Hn) as R0. rewrite Ep. exact R0. }
  pose proof (bpow_ge_0 radix2 (-53)) as P53. pose proof (Rabs_pos (B th)) as Th0.
  assert (E : bpow radix2 (-52) = bpow radix2 (-53) * 2).
  { replace (-52)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. reflexivity. }
  assert (P53s : bpow radix2 (-53) <= / 2) by (replace (-53)%Z with (-1 + -52)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 (-1)) with (/ 2); pose proof (bpow_le radix2 (-52) 0 ltac:(lia)); change (bpow radix2 0) with 1 in H; nra).
  repeat split; try assumption.
  - (* |pl| *)
    assert (Hl : B pl = B th * B cH - B ph) by lra.
    destruct Hrel as [Z | R].
    + apply Rabs_eq_R0 in Z. assert (Hp0 : B ph = 0) by (rewrite Ep, Z; apply round_0; exact _).
      assert (Hl0 : B pl = 0) by lra. rewrite Hl0, Rabs_R0. nra.
    + rewrite Hl, Rabs_minus_sym. rewrite E. nra.
  - (* |th|/4 <= |ph| *)
    destruct Hrel as [Z | R].
    + apply Rabs_eq_R0 in Z. assert (Hp0 : B ph = 0) by (rewrite Ep, Z; apply round_0; exact _).
      rewrite Z, Rabs_R0 in Tlo. rewrite Hp0, Rabs_R0. lra.
    + pose proof (Rabs_triang_inv (B th * B cH) (B ph)) as Ti. rewrite Rabs_minus_sym in Ti.
      pose proof (Rabs_pos (B th * B cH)) as X0.
      assert (PX : bpow radix2 (-53) * Rabs (B th * B cH) <= Rabs (B th * B cH) / 2) by nra.
      lra.
  - destruct Hrel as [Z | R].
    + apply Rabs_eq_R0 in Z. assert (Hp0 : B ph = 0) by (rewrite Ep, Z; apply round_0; exact _). rewrite Hp0.
      rewrite Rabs_R0. pose proof (bpow_ge_0 radix2 (-52)). nra.
    + pose proof (Rabs_triang_inv (B ph) (B th * B cH)) as Ti.
      pose proof (Rabs_triang_inv2 (B ph) (B th * B cH)).
      rewrite E. nra.
Qed.



Theorem segment_eval_a th tl c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 (bound dgb : R) :
  finite th -> finite tl -> finite c0 -> finite c1 -> finite cH -> finite cL ->
  finite g0 -> finite g1 -> finite g2 -> finite g3 -> finite g4 -> finite g5 -> finite g6 -> finite g7 -> finite g8 ->
  Rabs (B th) <= 0.0078126 -> (B th = 0 \/ bpow radix2 (-899) <= Rabs (B th)) ->
  Rabs (B tl) <= bpow radix2 (-52) * Rabs (B th) -> Rabs (B tl) <= 8.7e-19 -> Rabs (B th + B tl) <= 0.0078126 ->
  1 / 2 <= B cH <= 1 -> Rabs (B cL) <= bpow radix2 (-50) ->
  Rabs (B g0) <= bpow radix2 11 -> Rabs (B g1) <= bpow radix2 11 -> Rabs (B g2) <= bpow radix2 11 ->
  Rabs (B g3) <= bpow radix2 11 -> Rabs (B g4) <= bpow radix2 11 -> Rabs (B g5) <= bpow radix2 11 ->
  Rabs (B g6) <= bpow radix2 11 -> Rabs (B g7) <= bpow radix2 11 -> Rabs (B g8) <= bpow radix2 11 ->
  Rabs (B c0) <= 2 -> Rabs (B c1) <= 2 ->
  bpow radix2 (-7) <= B c0 -> Rabs (B c1) <= bpow radix2 (-52) * B c0 ->
  EvalCert (B cH) (B cL) (B g0) (B g1) (B g2) (B g3) (B g4) (B g5) (B g6) (B g7) (B g8) bound dgb ->
  sl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) * 8.7e-19 <= dgb ->
  let t := B th + B tl in
  Rabs ((B cH + B cL) * t + t * t * pl (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) t) + bound < 49 / 50 * (B c0 + B c1) ->
  exists h l, seg_result th tl c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 = (h, l) /\ finite h /\ finite l /\
    B h = rndF (B h + B l) /\
    exists e1 ea, Rabs e1 <= bound /\ Rabs ea <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) /\
    B h + B l = (B c0 + B c1 + ((B cH + B cL) * t + t * t * pl (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) t) + e1) * (1 + ea).
Proof.
  intros Ft Fl F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 Th Tn Tl1 Tl2 Tt H1 CL G0 G1 G2 G3 G4 G5 G6 G7 G8 C0 C1 Lc0 Lc1 EC Hdg t HS.
  pose proof (Rabs_le_inv _ _ Lc1) as [Lca Lcb]. rewrite bm52 in Lca, Lcb.
  assert (Hc01 : 0 < B c0 + B c1) by (pose proof (bpow_gt_0 radix2 (-7)); lra).
  assert (T6 : Rabs (B th) <= bpow radix2 (-6)) by (rewrite bm6; lra).
  assert (Dg0 : 0 <= dgb) by (pose proof (sl_nonneg 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) ltac:(lra)); nra).
  destruct (horner_chain th g0 g1 g2 g3 g4 g5 g6 g7 g8 Ft Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 T6 G0 G1 G2 G3 G4 G5 G6 G7 G8)
    as [Fg [Eg Bg]]. cbv zeta in Eg, Bg.
  assert (Hh : Rabs (B (hf th g0 g1 g2 g3 g4 g5 g6 g7 g8)) <= 2).
  { destruct (Rabs_le_inv _ _ Th) as [Tha Thb]. destruct (Rabs_le_inv _ _ Tl2) as [Tla Tlb].
    destruct (EC (B th) (B tl) 0 ltac:(split; lra) ltac:(split; lra) ltac:(split; [lra | lra])) as [_ H2].
    cbv zeta in H2. rewrite !rn_B in H2. rewrite Eg. exact H2. }
  pose proof (ph_facts_a th cH Ft FH T6 Tn H1) as PH.
  destruct (two_prod64 th cH) as [ph pq] eqn:Eprod. destruct PH as [Fp [Fq [Ep [Ex [Pl [PhLo PhHi]]]]]].
  destruct (tail_facts_a th tl cH cL (hf th g0 g1 g2 g3 g4 g5 g6 g7 g8) pq Ft Fl FH FL Fg Fq T6 Tn Tl1 Pl H1 CL Hh)
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
  assert (b4q : bpow radix2 (-4) = / 16) by (rewrite (bpow_negn 4 : bpow radix2 (-4) = / 2 ^ 4); simpl; field).
  rewrite b4q in Btail, B4'.
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
  (* the result is a double-word number: the sizes [add64_normalized] asks for *)
  assert (b78 : bpow radix2 (-7) = 2 * bpow radix2 (-8)).
  { replace (-7)%Z with (-8 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  pose proof (bpow_gt_0 radix2 (-8)) as P8.
  assert (c01lo : bpow radix2 (-8) <= B c0 + B c1) by lra.
  assert (Hyh8 : bpow radix2 (-8) <= B yh).
  { rewrite Eyh. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | exact c01lo]. }
  assert (P53n : bpow radix2 (-53) = / 9007199254740992) by exact bp53.
  assert (Hn1 : bpow radix2 (-1022) <= Rabs (B c0 + B c1)).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-8)); [apply bpow_le; lia | exact c01lo]. }
  pose proof (rnd_rel_f _ Hn1) as R1. rewrite <- Eyh in R1. rewrite (Rabs_pos_eq (B c0 + B c1)) in R1 by lra.
  rewrite P53n in R1. pose proof R1 as R1'. apply Rabs_le_inv in R1' as [R1a R1b].
  assert (Hyl52 : Rabs (B yl) <= bpow radix2 (-52) * B yh).
  { rewrite bm52. apply Rabs_le. split; lra. }
  assert (HvS : Rabs (B ph + B tl_) <= 49 / 50 * (B c0 + B c1)).
  { replace (B ph + B tl_) with (Fx + (B tl_ - Vv)) by lra.
    apply Rle_trans with (Rabs Fx + Rabs (B tl_ - Vv)); [apply Rabs_triang | lra]. }
  assert (Htiny : bpow radix2 (-1075) <= bpow radix2 (-8) * / 1000000000000000000000).
  { assert (Ht1 : bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
    assert (Ht2 : bpow radix2 (-100) = bpow radix2 (-8) * bpow radix2 (-92)).
    { replace (-100)%Z with (-8 + -92)%Z by reflexivity. rewrite bpow_plus. reflexivity. }
    assert (Ht3 : bpow radix2 (-92) <= / 1000000000000000000000) by (bpow_num; apply Rinv_le_contravar; [lra | interval with (i_prec 100)]).
    nra. }
  pose proof (rnd_err_abs (B ph + B tl_)) as R2. rewrite <- Evh in R2. rewrite P53n in R2.
  assert (Hvl52 : Rabs (B vl) <= bpow radix2 (-52) * B yh).
  { rewrite bm52. replace (B vl) with ((B ph + B tl_) - B vh) by lra. rewrite Rabs_minus_sym.
    apply Rle_trans with (1 := R2). pose proof (Rabs_pos (B ph + B tl_)).
    assert (Htiny' : bpow radix2 (-1075) <= B yh * / 1000000000000000000000) by nra.
    lra. }
  assert (Hvh99 : Rabs (B vh) <= 99 / 100 * B yh).
  { assert (Hvv : B vh = (B ph + B tl_) + - B vl) by lra.
    pose proof (Rabs_triang (B ph + B tl_) (- B vl)) as Tr. rewrite <- Hvv in Tr. rewrite Rabs_Ropp in Tr.
    rewrite bm52 in Hvl52.
    apply Rabs_le_inv in HvS as [HvSa HvSb]. pose proof (Rabs_pos (B ph + B tl_)).
    assert (HS2 : Rabs (B ph + B tl_) <= 49 / 50 * (B c0 + B c1)) by (apply Rabs_le; split; assumption).
    lra. }
  assert (Hyh900 : B yh <= bpow radix2 900).
  { apply Rle_trans with (bpow radix2 3); [rewrite b3; lra | apply bpow_le; lia]. }
  pose proof (add64_normalized yh yl vh vl Fyh Fyl Fvh Fvl
    (Rle_trans _ _ _ (bpow_le radix2 (-900) (-8) ltac:(lia)) Hyh8) Hyh900 Hyl52 Hvl52 Hvh99) as NORM.
  pose proof (add_ieee yh yl vh vl Fyh Fyl Hyh Fvh Fvl Hvh (big8 (B yh) ltac:(lra)) (big8 (B yl) Byl') (big8 (B vh) ltac:(lra)) (big8 (B vl) ltac:(lra)) Hne) as AD.
  destruct (add64 yh yl vh vl) as [zh zl] eqn:Ea. destruct AD as [Fzh [Fzl Err]].
  try cbv iota in NORM. destruct NORM as [_ [_ Nrm]].
  exists zh, zl. split; [ | split; [exact Fzh | split; [exact Fzl | split; [exact Nrm | ]]]].
  - unfold seg_result. cbv zeta. rewrite Eprod, Ey. fold tl_. rewrite Efs. exact Ea.
  - exists (B tl_ - Vv), ((B zh + B zl - (B yh + B yl + (B vh + B vl))) / (B yh + B yl + (B vh + B vl))).
    split; [exact Eb | split; [exact Err | ]].
    rewrite <- HS'. field. exact Hne.
Qed.


(** A table row's hypotheses on its coefficients, with the certificate's
    absolute bound [bound] on the tail's evaluation error. *)
Definition SegOkA (c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 : f64) (bound : R) : Prop :=
  finite c0 /\ finite c1 /\ finite cH /\ finite cL /\ finite g0 /\ finite g1 /\ finite g2 /\ finite g3 /\
  finite g4 /\ finite g5 /\ finite g6 /\ finite g7 /\ finite g8 /\
  Rabs (B c0) <= 2 /\ Rabs (B c1) <= 2 /\ (1 / 2 <= B cH <= 1) /\ Rabs (B cL) <= bpow radix2 (-50) /\
  bpow radix2 (-7) <= B c0 /\ Rabs (B c1) <= bpow radix2 (-52) * B c0 /\
  Rabs (B g0) <= bpow radix2 11 /\ Rabs (B g1) <= bpow radix2 11 /\ Rabs (B g2) <= bpow radix2 11 /\
  Rabs (B g3) <= bpow radix2 11 /\ Rabs (B g4) <= bpow radix2 11 /\ Rabs (B g5) <= bpow radix2 11 /\
  Rabs (B g6) <= bpow radix2 11 /\ Rabs (B g7) <= bpow radix2 11 /\ Rabs (B g8) <= bpow radix2 11 /\
  exists dgb, EvalCert (B cH) (B cL) (B g0) (B g1) (B g2) (B g3) (B g4) (B g5) (B g6) (B g7) (B g8) bound dgb /\
    sl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) * 8.7e-19 <= dgb /\
    (B cH + Rabs (B cL)) * 0.0078126 + 0.0078126 * 0.0078126 * bl 0.0078126 (seg_poly g0 g1 g2 g3 g4 g5 g6 g7 g8) + bound
      < 49 / 50 * (B c0 + B c1).


(** The polynomial part of a segment's value stays small. *)
Lemma fx_small_a cH cL c01 bound (L : list R) t : 1 / 2 <= cH -> Rabs t <= 0.0078126 ->
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


(** [SegOkA] for the words of a table row. *)
Definition SegOkRowA (row : list Z) (bound : R) : Prop :=
  let c := fun j => aw (nth j row 0%Z) in
  SegOkA (c 0%nat) (c 1%nat) (c 2%nat) (c 3%nat) (c 4%nat) (c 5%nat) (c 6%nat) (c 7%nat) (c 8%nat) (c 9%nat)
    (c 10%nat) (c 11%nat) (c 12%nat) bound.


(** [atan2_series] on a segment: the exact value it computes, up to the
    certificate's bound and one double-word addition's rounding. *)
Theorem series_segment_a zh zl (k : Z) (bound : R) : (1 <= k <= 64)%Z ->
  finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 -> Znearest ne (B zh * 64) = k ->
  Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  SegOkRowA (nth (Z.to_nat (k - 1)) atan2_segments []) bound ->
  let row := nth (Z.to_nat (k - 1)) atan2_segments [] in
  let c := fun j => aw (nth j row 0%Z) in
  let t := (B zh - IZR k / 64) + B zl in
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs t <= 0.0078126 /\
    exists e1 ea, Rabs e1 <= bound /\ Rabs ea <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) /\
    B h + B l = (B (c 0%nat) + B (c 1%nat)
      + ((B (c 2%nat) + B (c 3%nat)) * t + t * t * pl (seg_poly (c 4%nat) (c 5%nat) (c 6%nat) (c 7%nat) (c 8%nat) (c 9%nat) (c 10%nat) (c 11%nat) (c 12%nat)) t)
      + e1) * (1 + ea).
Proof.
  intros Hk Fz Fl L U Hn Hl Hg SO row c t.
  destruct (segment_reduction_a zh k Hk Fz L U Hn) as [Cgt [Ix [Fa [Ea [Fs [Es [Gr Hd]]]]]]].
  set (i := fsub (fadd (fmul zh asin_64) asin_shifter) asin_shifter) in *.
  assert (Hx' : Rabs (B (fsub zh (fmul i asin_inv64))) <= / 128) by (rewrite Es; exact Hd).
  assert (Hxn : on_grid (-59) (B (fsub zh (fmul i asin_inv64)))) by (rewrite Es; exact Gr).
  pose proof (t_split_a (fsub zh (fmul i asin_inv64)) zl Fs Fl Hx' Hxn Hl Hg) as TS.
  destruct (two_sum64 (fsub zh (fmul i asin_inv64)) zl) as [th tl] eqn:Ets.
  destruct TS as [Fth [Ftl [Eth [Esum [Th [Tl2 [Tn Tl1]]]]]]].
  assert (Etsum : B th + B tl = t) by (unfold t; rewrite Esum, Es; reflexivity).
  assert (Htt : Rabs (B th + B tl) <= 0.0078126).
  { rewrite Etsum. unfold t. destruct (Rabs_le_inv _ _ Hd) as [Hd1 Hd2]. destruct (Rabs_le_inv _ _ Hl) as [Hl1 Hl2].
    rewrite bp53 in Hl1, Hl2. apply Rabs_le. split; lra. }
  unfold SegOkRowA in SO. cbv zeta in SO.
  destruct SO as [F0 [F1 [FH [FL [Fg0 [Fg1 [Fg2 [Fg3 [Fg4 [Fg5 [Fg6 [Fg7 [Fg8 [C0 [C1 [H1 [CL [Lc0 [Lc1 [G0 [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [dgb [EC [Hdg HSn]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  pose proof (fx_small_a _ _ _ _ _ (B th + B tl) (proj1 H1) Htt HSn) as HS.
  pose proof (segment_eval_a th tl _ _ _ _ _ _ _ _ _ _ _ _ _ bound dgb Fth Ftl F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8
    Th Tn Tl1 Tl2 Htt H1 CL G0 G1 G2 G3 G4 G5 G6 G7 G8 C0 C1 Lc0 Lc1 EC Hdg HS) as SE.
  destruct SE as [h [l [Hres [Fh [Fl2 [Nrm [e1 [ea [E1 [Eea Eq]]]]]]]]]].
  refine (ex_intro _ h (ex_intro _ l (conj _ (conj Fh (conj Fl2 (conj Nrm (conj _ _))))))).
  - rewrite <- Hres. unfold atan2_series. cbv zeta. fold i. rewrite Cgt, Ix, Ets. unfold seg_result, hf, tail_of. cbv zeta. simpl Z.to_nat. reflexivity.
  - rewrite <- Etsum. exact Htt.
  - exists e1, ea. rewrite <- Etsum. exact (conj E1 (conj Eea Eq)).
Qed.


Lemma segok_from_values_a c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 bound dgb : R) :
  finite c0 -> finite c1 -> finite cH -> finite cL -> finite g0 -> finite g1 -> finite g2 -> finite g3 ->
  finite g4 -> finite g5 -> finite g6 -> finite g7 -> finite g8 ->
  B c0 = r0 -> B c1 = r1 -> B cH = rH -> B cL = rL -> B g0 = q0 -> B g1 = q1 -> B g2 = q2 -> B g3 = q3 ->
  B g4 = q4 -> B g5 = q5 -> B g6 = q6 -> B g7 = q7 -> B g8 = q8 ->
  Rabs r0 <= 2 -> Rabs r1 <= 2 -> (1 / 2 <= rH <= 1) -> Rabs rL <= bpow radix2 (-50) ->
  bpow radix2 (-7) <= r0 -> Rabs r1 <= bpow radix2 (-52) * r0 ->
  Rabs q0 <= bpow radix2 11 -> Rabs q1 <= bpow radix2 11 -> Rabs q2 <= bpow radix2 11 ->
  Rabs q3 <= bpow radix2 11 -> Rabs q4 <= bpow radix2 11 -> Rabs q5 <= bpow radix2 11 ->
  Rabs q6 <= bpow radix2 11 -> Rabs q7 <= bpow radix2 11 -> Rabs q8 <= bpow radix2 11 ->
  EvalCert rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 bound dgb ->
  sl 0.0078126 [q0; q1; q2; q3; q4; q5; q6; q7; q8] * 8.7e-19 <= dgb ->
  (rH + Rabs rL) * 0.0078126 + 0.0078126 * 0.0078126 * bl 0.0078126 [q0; q1; q2; q3; q4; q5; q6; q7; q8] + bound < 49 / 50 * (r0 + r1) ->
  SegOkA c0 c1 cH cL g0 g1 g2 g3 g4 g5 g6 g7 g8 bound.
Proof.
  intros F0 F1 FH FL Fg0 Fg1 Fg2 Fg3 Fg4 Fg5 Fg6 Fg7 Fg8 V0 V1 VH VL W0 W1 W2 W3 W4 W5 W6 W7 W8
    A0 A1 AH AL Lr0 Lr1 B0 B1 B2 B3 B4 B5 B6 B7 B8 EC Hs Hn.
  unfold SegOkA. rewrite V0, V1, VH, VL, W0, W1, W2, W3, W4, W5, W6, W7, W8. unfold seg_poly. rewrite W0, W1, W2, W3, W4, W5, W6, W7, W8.
  destruct AH as [AH1 AH2]. repeat split; try assumption.
  exists dgb. exact (conj EC (conj Hs Hn)).
Qed.

