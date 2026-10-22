(** The rounding test (RoundingTest.decide_with_ok) with its lower bound on the
    leading word relaxed from [2^-900] to [2^-905]: atan2's fast path decides
    angles as small as [2^-901]. Proof text as RoundingTest's. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps RoundingCore RoundingTest.
From Binary64 Require Import IEEE64Add IEEE64Mul.
Open Scope R_scope.

Lemma ziv_pos_a (h l eps e1 Z g : R) :
  F64 h -> bpow radix2 (-905) <= h ->
  h = RNE (h + l) ->
  g <= ulp radix2 fexp64 h -> g <= h - pred radix2 fexp64 h ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) -> e1 * (1 + bpow radix2 (-50)) <= eps <= 1 ->
  Rabs (Z - (h + l)) <= e1 * Rabs Z ->
  Rabs l + RNE (eps * h) < g / 2 ->
  RNE Z = h.
Proof.
  intros Fh Hlo Hdw G1 G2 [E80 E1] [Ee Ee1] HZ Ht.
  assert (E0 : 0 < e1) by (pose proof (bpow_gt_0 radix2 (-80)); lra).
  assert (P60 : bpow radix2 (-60) = / 1152921504606846976) by reflexivity.
  assert (P50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
  assert (Hpos : 0 < h) by (pose proof (bpow_gt_0 radix2 (-905)); lra).
  (* |l| <= 2^-52 h: h = RN(h + l) with h + l normal *)
  assert (Hl : Rabs l <= bpow radix2 (-52) * h).
  { destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (h + l))) as [N | S].
    - pose proof (rnd_rel (h + l) N) as R. rewrite <- Hdw in R.
      replace (h - (h + l)) with (- l) in R by ring. rewrite Rabs_Ropp in R.
      assert (Tr : Rabs (h + l) <= h + Rabs l) by (pose proof (Rabs_triang h l) as T; rewrite (Rabs_pos_eq h) in T by lra; lra).
      rewrite P53 in R. rewrite P52. nra.
    - (* h + l tiny would round to a tiny h, contradicting h >= 2^-905 *)
      exfalso. assert (RNE (h + l) <= bpow radix2 (-1022)).
      { apply round_le_generic; auto with typeclass_instances.
        - apply generic_format_FLT_bpow; [reflexivity | lia].
        - apply Rabs_lt_inv in S. lra. }
      assert (bpow radix2 (-1022) < bpow radix2 (-905)) by (apply bpow_lt; lia). lra. }
  (* |Z - (h + l)| <= e1 (1 + 2^-51) h *)
  assert (HZ2 : Rabs (Z - (h + l)) <= e1 * (1 + bpow radix2 (-51)) * h).
  { set (D := Rabs (Z - (h + l))). set (Y := Rabs (h + l)).
    assert (Zt : Rabs Z <= Y + D).
    { unfold Y, D. replace Z with ((h + l) + (Z - (h + l))) at 1 by ring. apply Rabs_triang. }
    assert (Tr : Y <= h + Rabs l) by (unfold Y; pose proof (Rabs_triang h l) as T; rewrite (Rabs_pos_eq h) in T by lra; lra).
    assert (P51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
    rewrite P51. rewrite P52 in Hl. rewrite P60 in E1.
    assert (D0 : 0 <= D) by apply Rabs_pos.
    (* D <= e1 (Y + D) <= e1 h (1 + 2^-52) + 2^-60 D *)
    assert (S1 : D <= e1 * Y + e1 * D).
    { apply Rle_trans with (1 := HZ). rewrite <- Rmult_plus_distr_l. apply Rmult_le_compat_l; lra. }
    assert (S2 : e1 * Y <= (e1 * h) * (1 + / 4503599627370496)).
    { replace ((e1 * h) * (1 + / 4503599627370496)) with (e1 * (h * (1 + / 4503599627370496))) by ring.
      apply Rmult_le_compat_l; lra. }
    assert (S3 : e1 * D <= / 1152921504606846976 * D) by (apply Rmult_le_compat_r; lra).
    assert (X0 : 0 <= e1 * h) by nra.
    replace (e1 * (1 + / 2251799813685248) * h) with ((e1 * h) * (1 + / 2251799813685248)) by ring.
    lra. }
  (* RN(eps h) >= eps h (1 - 2^-53) >= e1 (1 + 2^-51) h *)
  assert (Hr : e1 * (1 + bpow radix2 (-51)) * h <= RNE (eps * h)).
  { assert (P50' : 0 < bpow radix2 (-50)) by apply bpow_gt_0.
    assert (Le : e1 <= eps) by nra.
    assert (N : bpow radix2 (-1022) <= Rabs (eps * h)).
    { rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
      assert (B : bpow radix2 (-1022) <= bpow radix2 (-80) * bpow radix2 (-905))
        by (rewrite <- bpow_plus; apply bpow_le; lia).
      pose proof (bpow_gt_0 radix2 (-80)). pose proof (bpow_gt_0 radix2 (-905)).
      apply Rle_trans with (1 := B). apply Rmult_le_compat; lra. }
    pose proof (rnd_rel (eps * h) N) as R. apply Rabs_le_inv in R.
    rewrite Rabs_pos_eq in R by nra.
    assert (P51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
    rewrite P51. rewrite P53 in R. rewrite P50 in Ee. nra. }
  assert (Hclose : Rabs (Z - h) < g / 2).
  { replace (Z - h) with ((Z - (h + l)) + l) by ring.
    apply Rle_lt_trans with (Rabs (Z - (h + l)) + Rabs l); [apply Rabs_triang | lra]. }
  apply round_within with g; assumption || lra.
Qed.

Lemma lo_bound_a h l : bpow radix2 (-905) <= Rabs h -> h = rndF (h + l) ->
  Rabs l <= bpow radix2 (-52) * Rabs h.
Proof.
  intros Hh Hdw.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (h + l))) as [N | S].
  - pose proof (rnd_rel (h + l) N) as R. rewrite RNE_rndF, <- Hdw in R.
    replace (h - (h + l)) with (- l) in R by ring. rewrite Rabs_Ropp in R.
    assert (T : Rabs (h + l) <= Rabs h + Rabs l) by apply Rabs_triang.
    assert (P53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
    assert (P52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
    rewrite P53 in R. rewrite P52. pose proof (Rabs_pos l). pose proof (Rabs_pos h). nra.
  - exfalso. assert (Rabs (rndF (h + l)) <= bpow radix2 (-1022)).
    { rewrite <- round_NE_abs; auto with typeclass_instances.
      apply round_le_generic; auto with typeclass_instances.
      - apply generic_format_FLT_bpow; [reflexivity | unfold emin; lia].
      - lra. }
    rewrite <- Hdw in H. assert (bpow radix2 (-1022) < bpow radix2 (-905)) by (apply bpow_lt; lia). lra.
Qed.

Theorem decide_with_bounded_ok_a hi lo eps (Z e1 : R) v :
  finite hi -> finite lo -> finite eps ->
  bpow radix2 (-905) <= Rabs (B hi) < bpow radix2 1024 ->
  B eps * Rabs (B hi) <= bpow radix2 1020 ->
  B hi = rndF (B hi + B lo) ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) ->
  e1 * (1 + bpow radix2 (-50)) <= B eps <= 1 ->
  Rabs (Z - (B hi + B lo)) <= e1 * Rabs Z ->
  decide_with hi lo eps = Some v ->
  v = hi /\ rndF Z = B hi.
Proof.
  intros Fhi Flo Feps [Hlo Hhi] Hprod Hdw He1 Heps HZ Hd.
  destruct hi as [s | s | s pl Hpl | s mx ex Hx]; try discriminate.
  { exfalso. simpl in Hlo. rewrite Rabs_R0 in Hlo. pose proof (bpow_gt_0 radix2 (-905)). lra. }
  set (hi := B754_finite 53 1024 s mx ex Hx) in *.
  (* the magnitude, and its fields *)
  assert (Bm : B (b64_abs hi) = Rabs (B hi)) by (apply B2R_Babs).
  assert (Fm : finite (b64_abs hi)) by reflexivity.
  (* ex is the canonical exponent, and hi is normal *)
  pose proof Hx as Hb. unfold bounded in Hb. apply andb_prop in Hb as [Hc _].
  pose proof (canonical_canonical_mantissa 53 1024 false mx ex Hc) as Can.
  assert (Habs : Rabs (B hi) = F2R (Float radix2 (Zpos mx) ex)).
  { unfold hi. simpl B2R. rewrite <- F2R_Zabs. f_equal. simpl. destruct s; reflexivity. }
  assert (Pa : 0 < Rabs (B hi)) by (pose proof (bpow_gt_0 radix2 (-905)); lra).
  assert (Ulp : ulp radix2 fexp64 (Rabs (B hi)) = bpow radix2 ex).
  { rewrite ulp_neq_0 by lra. rewrite Habs. unfold canonical in Can. simpl in Can.
    f_equal. symmetry. exact Can. }
  set (h := Rabs (B hi)) in *.
  (* ex's range, and a normal significand *)
  assert (U1 : h * bpow radix2 (-53) < bpow radix2 ex).
  { rewrite <- Ulp. pose proof (ulp_FLT_gt radix2 (-1074) 53 h) as U. rewrite (Rabs_pos_eq h) in U by lra. exact U. }
  assert (U2 : bpow radix2 ex <= h * bpow radix2 (-52)).
  { rewrite <- Ulp. replace (-52)%Z with (1 - 53)%Z by reflexivity. rewrite <- (Rabs_pos_eq h) at 2 by lra.
    apply ulp_FLT_le. rewrite Rabs_pos_eq by lra. apply Rle_trans with (2 := Hlo). apply bpow_le. lia. }
  assert (Ex : (-958 <= ex <= 971)%Z).
  { split.
    - cut (-959 < ex)%Z; [lia | ]. apply (lt_bpow radix2). apply Rle_lt_trans with (2 := U1).
      apply Rle_trans with (bpow radix2 (-905) * bpow radix2 (-53)).
      + rewrite <- bpow_plus. apply bpow_le. lia.
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
    - assert (E : (ex < 972)%Z).
      { apply (lt_bpow radix2). apply Rle_lt_trans with (1 := U2).
        replace (bpow radix2 972) with (bpow radix2 1024 * bpow radix2 (-52))
          by (rewrite <- bpow_plus; reflexivity).
        apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hhi]. }
      lia. }
  assert (Hm : h = IZR (Zpos mx) * bpow radix2 ex) by (rewrite Habs; reflexivity).
  assert (Mx : (2 ^ 52 <= Zpos mx < 2 ^ 53)%Z).
  { pose proof (bpow_gt_0 radix2 ex) as Pe. split.
    - apply le_IZR. apply Rmult_le_reg_r with (bpow radix2 ex); [exact Pe | ].
      rewrite <- Hm. replace (IZR (2 ^ 52)) with (bpow radix2 52) by reflexivity.
      apply Rmult_le_reg_r with (bpow radix2 (-52)); [apply bpow_gt_0 | ].
      replace (bpow radix2 52 * bpow radix2 ex * bpow radix2 (-52)) with (bpow radix2 ex)
        by (rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus; simpl; ring).
      exact U2.
    - apply lt_IZR. apply Rmult_lt_reg_r with (bpow radix2 ex); [exact Pe | ].
      rewrite <- Hm. replace (IZR (2 ^ 53)) with (bpow radix2 53) by reflexivity.
      apply Rmult_lt_reg_r with (bpow radix2 (-53)); [apply bpow_gt_0 | ].
      replace (bpow radix2 53 * bpow radix2 ex * bpow radix2 (-53)) with (bpow radix2 ex)
        by (rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus; simpl; ring).
      exact U1. }
  assert (Fh : F64 h) by (apply generic_format_abs, generic_format_B2R).
  (* the gaps around h *)
  destruct (gap_below h Fh Pa) as [Gb1 Gb2].
  (* evaluate the test *)
  unfold decide_with in Hd. change (fraction_zero (b64_abs hi)) with (Zpos mx mod 2 ^ 52 =? 0)%Z in Hd.
  change (ulp_f (b64_abs hi)) with (binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 ex false) in Hd.
  destruct (pow2_f ex ltac:(lia)) as [Bu Fu].
  set (u := binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 ex false) in *.
  set (gF := if (Zpos mx mod 2 ^ 52 =? 0)%Z then fmul u half else u) in Hd.
  assert (G : exists eg, (ex - 1 <= eg <= ex)%Z /\ finite gF /\ B gF = bpow radix2 eg /\
    bpow radix2 eg <= ulp radix2 fexp64 h /\ bpow radix2 eg <= h - pred radix2 fexp64 h).
  { unfold gF. destruct (Z.eqb_spec (Zpos mx mod 2 ^ 52) 0) as [Z0 | Z1].
    - destruct (half_f u ex Fu Bu ltac:(lia)) as [F1 B1]. exists (ex - 1)%Z.
      rewrite Ulp. repeat split; try lia; try assumption.
      + apply bpow_le. lia.
      + apply Rle_trans with (2 := Gb1). rewrite Ulp. unfold Zminus. rewrite bpow_plus. simpl. lra.
    - exists ex. rewrite Ulp. repeat split; try lia; try assumption; try apply Rle_refl.
      rewrite Gb2; [rewrite Ulp; apply Rle_refl | ].
      intros Pw. apply Z1. 
      assert (Mg : mag radix2 h = (ex + 53)%Z :> BinNums.Z).
      { apply mag_unique. rewrite Rabs_pos_eq by lra. rewrite Hm.
        replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring. replace (ex + 53)%Z with (53 + ex)%Z by ring.
        rewrite !bpow_plus. pose proof (bpow_gt_0 radix2 ex).
        split; [apply Rmult_le_compat_r; [lra | ] | apply Rmult_lt_compat_r; [lra | ]].
        - replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia.
        - replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
      rewrite Mg in Pw. rewrite Hm in Pw. replace (ex + 53 - 1)%Z with (52 + ex)%Z in Pw by ring.
      rewrite bpow_plus in Pw. apply Rmult_eq_reg_r in Pw; [ | apply Rgt_not_eq, bpow_gt_0].
      replace (bpow radix2 52) with (IZR (2 ^ 52)) in Pw by reflexivity. apply eq_IZR in Pw.
      rewrite Pw. reflexivity. }
  destruct G as [eg [Eg [FgF [BgF [Gu Gp]]]]].
  destruct (half_f gF eg FgF BgF ltac:(lia)) as [Fc Bc].
  (* the product and the sum *)
  assert (Ep : 0 < B eps).
  { destruct He1 as [A _]. destruct Heps as [C _].
    pose proof (bpow_gt_0 radix2 (-80)). pose proof (bpow_gt_0 radix2 (-50)). nra. }
  assert (Bp : bnd 1 1020 (B eps * B (b64_abs hi))).
  { unfold bnd. rewrite Bm. fold h. rewrite Rabs_pos_eq by nra. rewrite Rmult_1_l. exact Hprod. }
  destruct (fmul_ok 1 1020 eps (b64_abs hi) Feps Fm ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bp) as [Fp BpV].
  pose proof (lo_bound_a (B hi) (B lo) Hlo Hdw) as Lb. fold h in Lb.
  assert (Ba : bnd 2 1020 (B (b64_abs lo) + B (fmul eps (b64_abs hi)))).
  { replace 2%Z with (1 + 1)%Z by reflexivity. apply bnd_plus.
    - unfold bnd. rewrite B_abs, Rabs_Rabsolu, Rmult_1_l. apply Rle_trans with (1 := Lb).
      apply Rle_trans with (bpow radix2 (-52)*bpow radix2 1024).
      + apply Rmult_le_compat_l; [apply bpow_ge_0 | lra].
      + rewrite <- bpow_plus. apply bpow_le; lia.
    - rewrite BpV. apply bnd_round; [lia | lia | exact Bp]. }
  destruct (fadd_ok 2 1020 (b64_abs lo) (fmul eps (b64_abs hi)) ltac:(reflexivity || (unfold b64_abs; destruct lo; simpl in *; congruence)) Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ba) as [Fa BaV].
  destruct (Bcompare 53 1024 _ _) eqn:Cmp in Hd; [ | discriminate].
  destruct c; try discriminate. injection Hd as <-.
  rewrite Bcompare_correct in Cmp by assumption. injection Cmp as Cmp.
  apply Rcompare_Lt_inv in Cmp. change (B754_finite 53 1024 false mx ex Hx) with (b64_abs hi) in Cmp.
  rewrite BaV, Bc in Cmp.
  rewrite B_abs, BpV, Bm in Cmp. fold h in Cmp.
  (* the exact inequality: g/2 is representable and rounding is monotone *)
  assert (Ex2 : Rabs (B lo) + rndF (B eps * h) < bpow radix2 eg / 2).
  { assert (Hh : bpow radix2 (eg - 1) = bpow radix2 eg / 2).
    { replace (eg - 1)%Z with (eg + -1)%Z by ring. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2)%R. field. }
    rewrite <- Hh.
    apply Rnot_le_lt. intros Ge. apply (Rlt_not_le _ _ Cmp).
    apply round_ge_generic; auto with typeclass_instances.
    apply generic_format_FLT_bpow; [reflexivity | unfold emin; lia]. }
  split; [reflexivity | ].
  destruct s.
  - (* a negative leading word: negate everything *)
    assert (Hn : B hi = - h) by (unfold h; rewrite Rabs_left; [ring | unfold hi; simpl; apply F2R_lt_0; simpl; lia]).
    assert (Hdw' : h = RNE (h + - B lo)).
    { assert (E : h + - B lo = - (B hi + B lo)) by (rewrite Hn; ring).
      rewrite E. change (RNE (- (B hi + B lo))) with (round radix2 fexp64 ZnearestE (- (B hi + B lo))).
      rewrite round_NE_opp. change (round radix2 fexp64 ZnearestE (B hi + B lo)) with (rndF (B hi + B lo)).
      rewrite <- Hdw, Hn. ring. }
    pose proof (ziv_pos_a h (- B lo) (B eps) e1 (- Z) (bpow radix2 eg) Fh Hlo Hdw' Gu Gp He1 Heps
                  ltac:(rewrite Rabs_Ropp; replace (- Z - (h + - B lo)) with (- (Z - (B hi + B lo))) by (rewrite Hn; ring); rewrite Rabs_Ropp; exact HZ)
                  ltac:(rewrite Rabs_Ropp; rewrite <- RNE_rndF in Ex2; exact Ex2)) as R.
    rewrite Hn. change rndF with (round radix2 fexp64 ZnearestE).
    replace Z with (- - Z) by ring. rewrite round_NE_opp. f_equal. exact R.
  - assert (Hp : B hi = h) by (unfold h; rewrite Rabs_pos_eq; [reflexivity | unfold hi; simpl; apply F2R_ge_0; simpl; lia]).
    rewrite Hp in Hdw, HZ |- *. rewrite <- RNE_rndF in Hdw, Ex2 |- *.
    apply (ziv_pos_a h (B lo) (B eps) e1 Z (bpow radix2 eg)); assumption.
Qed.

Theorem decide_with_ok_a hi lo eps (Z e1 : R) v :
  finite hi -> finite lo -> finite eps ->
  bpow radix2 (-905) <= Rabs (B hi) <= bpow radix2 1000 ->
  B hi = rndF (B hi + B lo) ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) ->
  e1 * (1 + bpow radix2 (-50)) <= B eps <= 1 ->
  Rabs (Z - (B hi + B lo)) <= e1 * Rabs Z ->
  decide_with hi lo eps = Some v ->
  v = hi /\ rndF Z = B hi.
Proof.
 intros Fh Fl Fe [Lo Hi] Dw E Ep Err D.
 apply (decide_with_bounded_ok_a hi lo eps Z e1 v); try assumption.
 - split; [exact Lo | apply Rle_lt_trans with (1 := Hi); apply bpow_lt; lia].
 - apply Rle_trans with (1 * Rabs (B hi)).
   + apply Rmult_le_compat_r; [apply Rabs_pos | exact (proj2 Ep)].
   + rewrite Rmult_1_l. apply Rle_trans with (1 := Hi). apply bpow_le; lia.
Qed.
