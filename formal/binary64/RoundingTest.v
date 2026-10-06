(** ln/mod.rs's [decide_with] and exp/mod.rs's [decide_scaled], transcribed on binary64,
    and proved: when the test passes, the returned word is the correctly rounded
    value of every real within [ε₁] of the double-word, scaled exactly by [2^k]
    for [decide_scaled] (docs/exp.md §5). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Binary64 Require Import RoundingGaps RoundingCore.

Open Scope R_scope.

(** ulp.rs's [ulp] of a finite binary64, on its fields: [2^ex]. *)
Definition ulp_f (x : f64) : f64 :=
  match x with
  | B754_finite _ _ ex _ => binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 ex false
  | _ => binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 (-1074) false
  end.

(** [x.to_bits() & FRACTION == 0]. *)
Definition fraction_zero (x : f64) : bool :=
  match x with B754_finite _ mx _ _ => (Zpos mx mod 2 ^ 52 =? 0)%Z | _ => true end.

Definition half : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 (-1) false.

Definition decide_with (hi lo eps : f64) : option f64 :=
  let m := b64_abs hi in
  let g := if fraction_zero m then fmul (ulp_f m) half else ulp_f m in
  match Bcompare 53 1024 (fadd (b64_abs lo) (fmul eps m)) (fmul g half) with
  | Some Lt => Some hi
  | _ => None
  end.

Lemma RNE_rndF x : RNE x = rndF x.
Proof. reflexivity. Qed.

Lemma B_abs x : B (b64_abs x) = Rabs (B x).
Proof. apply B2R_Babs. Qed.

(** A power of two from [binary_normalize 1 e]. *)
Lemma pow2_f e : (-1074 <= e <= 1023)%Z ->
  B (binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 e false) = bpow radix2 e /\
  finite (binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 e false).
Proof.
  intros He.
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE 1 e false) as C.
  assert (V : F2R (Float radix2 1 e) = bpow radix2 e) by (unfold F2R; simpl; ring).
  rewrite V in C.
  rewrite round_generic in C by first [apply generic_format_FLT_bpow; [reflexivity | lia] | auto with typeclass_instances].
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; assumption.
  - rewrite Rabs_pos_eq by apply bpow_ge_0. apply bpow_lt. lia.
Qed.

(** A power of two, halved. *)
Lemma half_f x e : finite x -> B x = bpow radix2 e -> (-1073 <= e <= 970)%Z ->
  finite (fmul x half) /\ B (fmul x half) = bpow radix2 (e - 1).
Proof.
  intros Fx Bx He. destruct (pow2_f (-1) ltac:(lia)) as [Bh Fh].
  assert (Hm : bnd 1 e (B x * B half)).
  { unfold bnd, half. rewrite Bx, Bh. rewrite Rabs_pos_eq by (apply Rmult_le_pos; apply bpow_ge_0).
    rewrite Rmult_1_l. rewrite <- bpow_plus. apply bpow_le. lia. }
  destruct (fmul_ok 1 e x half Fx Fh ltac:(lia) ltac:(lia) ltac:(apply (Z.pow_gt_1 2 (1024 - e)); lia) ltac:(lia) Hm) as [F1 B1].
  split; [exact F1 | ]. rewrite B1. unfold half. rewrite Bx, Bh, <- bpow_plus.
  apply round_generic; auto with typeclass_instances.
  apply generic_format_FLT_bpow; [reflexivity | ]. unfold emin. lia.
Qed.

(** A double-word number's trailing word is at most [2^−52] of its leading
    word, for a normal leading word. *)
Lemma lo_bound h l : bpow radix2 (-900) <= Rabs h -> h = rndF (h + l) ->
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
    rewrite <- Hdw in H. assert (bpow radix2 (-1022) < bpow radix2 (-900)) by (apply bpow_lt; lia). lra.
Qed.

Theorem decide_with_ok hi lo eps (Z e1 : R) v :
  finite hi -> finite lo -> finite eps ->
  bpow radix2 (-900) <= Rabs (B hi) <= bpow radix2 1000 ->
  B hi = rndF (B hi + B lo) ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) ->
  e1 * (1 + bpow radix2 (-50)) <= B eps <= 1 ->
  Rabs (Z - (B hi + B lo)) <= e1 * Rabs Z ->
  decide_with hi lo eps = Some v ->
  v = hi /\ rndF Z = B hi.
Proof.
  intros Fhi Flo Feps [Hlo Hhi] Hdw He1 Heps HZ Hd.
  destruct hi as [s | s | s pl Hpl | s mx ex Hx]; try discriminate.
  { exfalso. simpl in Hlo. rewrite Rabs_R0 in Hlo. pose proof (bpow_gt_0 radix2 (-900)). lra. }
  set (hi := B754_finite 53 1024 s mx ex Hx) in *.
  (* the magnitude, and its fields *)
  assert (Bm : B (b64_abs hi) = Rabs (B hi)) by (apply B2R_Babs).
  assert (Fm : finite (b64_abs hi)) by reflexivity.
  (* ex is the canonical exponent, and hi is normal *)
  pose proof Hx as Hb. unfold bounded in Hb. apply andb_prop in Hb as [Hc _].
  pose proof (canonical_canonical_mantissa 53 1024 false mx ex Hc) as Can.
  assert (Habs : Rabs (B hi) = F2R (Float radix2 (Zpos mx) ex)).
  { unfold hi. simpl B2R. rewrite <- F2R_Zabs. f_equal. simpl. destruct s; reflexivity. }
  assert (Pa : 0 < Rabs (B hi)) by (pose proof (bpow_gt_0 radix2 (-900)); lra).
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
  assert (Ex : (-953 <= ex <= 948)%Z).
  { split.
    - cut (-954 < ex)%Z; [lia | ]. apply (lt_bpow radix2). apply Rle_lt_trans with (2 := U1).
      apply Rle_trans with (bpow radix2 (-900) * bpow radix2 (-53)).
      + rewrite <- bpow_plus. apply bpow_le. lia.
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
    - apply (le_bpow radix2). apply Rle_trans with (1 := U2).
      apply Rle_trans with (bpow radix2 1000 * bpow radix2 (-52)).
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
      + rewrite <- bpow_plus. apply bpow_le. lia. }
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
  assert (Bp : bnd 1 1000 (B eps * B (b64_abs hi))).
  { unfold bnd. rewrite Bm. fold h. rewrite Rabs_mult, (Rabs_pos_eq h) by lra. rewrite (Rabs_pos_eq (B eps)) by lra.
    rewrite Rmult_1_l. apply Rle_trans with (1 * h); [apply Rmult_le_compat_r; lra | lra]. }
  destruct (fmul_ok 1 1000 eps (b64_abs hi) Feps Fm ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bp) as [Fp BpV].
  pose proof (lo_bound (B hi) (B lo) Hlo Hdw) as Lb. fold h in Lb.
  assert (Ba : bnd 2 1000 (B (b64_abs lo) + B (fmul eps (b64_abs hi)))).
  { replace 2%Z with (1 + 1)%Z by reflexivity. apply bnd_plus.
    - unfold bnd. rewrite B_abs, Rabs_Rabsolu. apply Rle_trans with (1 := Lb).
      apply Rle_trans with (1 * h); [apply Rmult_le_compat_r; [lra | ] | lra].
      change (bpow radix2 (-52) <= 1). apply Rlt_le, (bpow_lt radix2 (-52) 0); lia.
    - rewrite BpV. apply bnd_round; [lia | lia | exact Bp]. }
  destruct (fadd_ok 2 1000 (b64_abs lo) (fmul eps (b64_abs hi)) ltac:(reflexivity || (unfold b64_abs; destruct lo; simpl in *; congruence)) Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ba) as [Fa BaV].
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
    pose proof (ziv_pos h (- B lo) (B eps) e1 (- Z) (bpow radix2 eg) Fh Hlo Hhi Hdw' Gu Gp He1 Heps
                  ltac:(rewrite Rabs_Ropp; replace (- Z - (h + - B lo)) with (- (Z - (B hi + B lo))) by (rewrite Hn; ring); rewrite Rabs_Ropp; exact HZ)
                  ltac:(rewrite Rabs_Ropp; rewrite <- RNE_rndF in Ex2; exact Ex2)) as R.
    rewrite Hn. change rndF with (round radix2 fexp64 ZnearestE).
    replace Z with (- - Z) by ring. rewrite round_NE_opp. f_equal. exact R.
  - assert (Hp : B hi = h) by (unfold h; rewrite Rabs_pos_eq; [reflexivity | unfold hi; simpl; apply F2R_ge_0; simpl; lia]).
    rewrite Hp in Hdw, HZ |- *. rewrite <- RNE_rndF in Hdw, Ex2 |- *.
    apply (ziv_pos h (B lo) (B eps) e1 Z (bpow radix2 eg)); assumption.
Qed.
(** Rounding commutes with a power-of-two scaling while both sides are
    normal. *)
Lemma round_scale x k : x <> 0 -> (-1021 <= mag radix2 x)%Z -> (-1021 <= mag radix2 x + k)%Z ->
  rndF (x * bpow radix2 k) = rndF x * bpow radix2 k.
Proof.
  intros Nz H1 H2. unfold round, scaled_mantissa, cexp.
  rewrite mag_mult_bpow by exact Nz.
  unfold FLT_exp, emin, prec.
  rewrite Z.max_l by lia. rewrite Z.max_l by lia.
  replace (x * bpow radix2 k * bpow radix2 (- (mag radix2 x + k - 53)))
    with (x * bpow radix2 (- (mag radix2 x - 53))).
  - unfold F2R. simpl. replace (mag radix2 x + k - 53)%Z with ((mag radix2 x - 53) + k)%Z by ring.
    rewrite bpow_plus. ring.
  - rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

Definition pow2f (k : Z) : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 k false.

(** exp/mod.rs's [scale]: [y·2^k], the last step taken in two for [k = 1024]. *)
Definition scale (y : f64) (k : Z) : f64 :=
  if (k =? 1024)%Z then fmul (fmul y (pow2f 1023)) (pow2f 1) else fmul y (pow2f k).

(** exp/mod.rs's [decide_scaled], for a positive leading word. *)
Definition decide_scaled (hi lo eps : f64) (k : Z) : option f64 :=
  let g := if fraction_zero hi then fmul (ulp_f hi) half else ulp_f hi in
  match Bcompare 53 1024 (fadd (b64_abs lo) (fmul eps hi)) (fmul g half) with
  | Some Lt => Some (scale hi k)
  | _ => None
  end.

(** An exact product of finite binary64 numbers below the overflow threshold. *)
Lemma fmul_exact x y : finite x -> finite y -> F64 (B x * B y) -> Rabs (B x * B y) < bpow radix2 1024 ->
  finite (fmul x y) /\ B (fmul x y) = B x * B y.
Proof.
  intros Fx Fy Fm Lt.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y) as C.
  change (FLT_exp (3 - 1024 - 53) 53) with fexp64 in C.
  assert (R : round radix2 fexp64 (round_mode mode_NE) (B x * B y) = B x * B y)
    by (apply round_generic; auto with typeclass_instances).
  rewrite R in C. rewrite Rlt_bool_true in C by exact Lt.
  destruct C as [C1 [C2 _]]. split; [ | exact C1].
  unfold fmul, b64_mult. rewrite C2, Fx, Fy. reflexivity.
Qed.

Theorem decide_scaled_ok hi lo eps k (Z e1 : R) v :
  finite hi -> finite lo -> finite eps ->
  3 / 4 <= B hi <= 4 ->
  B hi = rndF (B hi + B lo) ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) ->
  e1 * (1 + bpow radix2 (-50)) <= B eps <= 1 ->
  Rabs (Z - (B hi + B lo)) <= e1 * Rabs Z ->
  (-1021 <= k <= 1024)%Z -> B hi * bpow radix2 k < bpow radix2 1024 ->
  decide_scaled hi lo eps k = Some v ->
  finite v /\ B v = rndF (Z * bpow radix2 k).
Proof.
  intros Fhi Flo Feps [H34 H4] Hdw He1 Heps HZ Hk Hov Hd.
  destruct hi as [s | s | s pl Hpl | s mx ex Hx]; try discriminate.
  { simpl in H34. lra. }
  destruct s.
  { exfalso. simpl in H34. assert (F2R (Float radix2 (Z.neg mx) ex) < 0) by (apply F2R_lt_0; simpl; lia). lra. }
  set (hi := B754_finite 53 1024 false mx ex Hx) in *.
  assert (Hw : decide_with hi lo eps = Some hi).
  { unfold decide_scaled in Hd. unfold decide_with.
    change (b64_abs hi) with hi.
    destruct (Bcompare 53 1024 _ _) as [[ | | ] | ]; try discriminate; reflexivity. }
  assert (Bnd : bpow radix2 (-900) <= Rabs (B hi) <= bpow radix2 1000).
  { rewrite Rabs_pos_eq by lra. split.
    - apply Rle_trans with (3 / 4); [ | lra]. apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2)%R; lra].
    - apply Rle_trans with (bpow radix2 2); [change (bpow radix2 2) with 4%R; lra | apply bpow_le; lia]. }
  destruct (decide_with_ok hi lo eps Z e1 hi Fhi Flo Feps Bnd Hdw He1 Heps HZ Hw) as [_ RZ].
  assert (Hv : v = scale hi k).
  { unfold decide_scaled in Hd. destruct (Bcompare 53 1024 _ _) as [[ | | ] | ]; try discriminate.
    injection Hd. auto. }
  subst v.
  (* Z is near B hi, so above 1/2 *)
  assert (Zh : 1 / 2 <= Z).
  { assert (Lh : bpow radix2 (-900) <= Rabs (B hi)) by (destruct Bnd; assumption).
    pose proof (lo_bound (B hi) (B lo) Lh Hdw) as Lb. rewrite (Rabs_pos_eq (B hi)) in Lb by lra.
    assert (P52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
    assert (P60 : bpow radix2 (-60) = / 1152921504606846976) by reflexivity.
    rewrite P52 in Lb. rewrite P60 in He1.
    apply Rabs_le_inv in Lb.
    destruct He1 as [E80 E60].
    destruct (Rle_or_lt 0 Z) as [Zp | Zn].
    - rewrite (Rabs_pos_eq Z) in HZ by lra. apply Rabs_le_inv in HZ.
      assert (e1 * Z <= / 1152921504606846976 * Z) by (apply Rmult_le_compat_r; lra). lra.
    - rewrite (Rabs_left Z) in HZ by lra. apply Rabs_le_inv in HZ.
      assert (e1 * - Z <= / 1152921504606846976 * - Z) by (apply Rmult_le_compat_r; lra). lra. }
  assert (Mz : (0 <= mag radix2 Z)%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. change (bpow radix2 (0 - 1)) with (/ 2)%R. lra. }
  rewrite round_scale by (lra || lia).
  rewrite RZ.
  (* scaling B hi by 2^j stays representable *)
  assert (Mh : (0 <= mag radix2 (B hi))%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. change (bpow radix2 (0 - 1)) with (/ 2)%R. lra. }
  assert (Fsc : forall j, (-1021 <= j)%Z -> F64 (B hi * bpow radix2 j)).
  { intros j Hj. replace (B hi * bpow radix2 j) with (rndF (B hi * bpow radix2 j)).
    - apply generic_format_round; auto with typeclass_instances.
    - rewrite round_scale by (lra || lia). f_equal. apply round_generic; auto with typeclass_instances.
      apply generic_format_B2R. }
  assert (Pk : 0 < bpow radix2 k) by apply bpow_gt_0.
  unfold scale. destruct (Z.eqb_spec k 1024) as [K | K].
  - subst k. destruct (pow2_f 1023 ltac:(lia)) as [B1 F1]. destruct (pow2_f 1 ltac:(lia)) as [B2 F2].
    unfold pow2f.
    assert (Hlt : B hi < 1).
    { apply Rmult_lt_reg_r with (bpow radix2 1024); [apply bpow_gt_0 | ]. rewrite Rmult_1_l. exact Hov. }
    destruct (fmul_exact hi _ Fhi F1 ltac:(rewrite B1; apply Fsc; lia)
                ltac:(rewrite B1, Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]);
                      apply Rlt_le_trans with (1 * bpow radix2 1023); [apply Rmult_lt_compat_r; [apply bpow_gt_0 | lra] | rewrite Rmult_1_l; apply bpow_le; lia]))
      as [Fa Ba].
    rewrite B1 in Ba.
    assert (E : B hi * bpow radix2 1023 * bpow radix2 1 = B hi * bpow radix2 1024)
      by (rewrite Rmult_assoc, <- bpow_plus; reflexivity).
    destruct (fmul_exact _ _ Fa F2 ltac:(rewrite Ba, B2, E; apply Fsc; lia)
                ltac:(rewrite Ba, B2, E, Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]); exact Hov))
      as [Fr Br].
    split; [exact Fr | ]. rewrite Br, Ba, B2. exact E.
  - destruct (pow2_f k ltac:(lia)) as [B1 F1]. unfold pow2f.
    destruct (fmul_exact hi _ Fhi F1 ltac:(rewrite B1; apply Fsc; lia)
                ltac:(rewrite B1, Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]); exact Hov))
      as [Fr Br].
    split; [exact Fr | ]. rewrite Br, B1. reflexivity.
Qed.
