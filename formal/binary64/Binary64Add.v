(** Double-word addition in binary64, with gradual underflow, meets the bounds
    Muller and Rideau prove in the unbounded-exponent model.

    Every rounding in 2Sum, Fast2Sum, DWPlusFP and AccurateDWPlusDW rounds a sum
    or difference of two binary64 numbers. Such a value rounds identically in
    binary64 (Flocq's FLT model: radix 2, precision 53, minimum exponent -1074)
    and in the unbounded model (FLX): above 2^-1022 the two roundings coincide
    (Flocq's [round_FLT_FLX]), and below it the exact sum is itself a binary64
    number ([FLT_format_plus_small]) and so is returned unchanged by both. So the
    binary64 computation equals the unbounded one step by step, and the vendored
    theorems apply. Overflow is outside both models; the library states input
    magnitudes that exclude it (docs/double-word.md). *)

From Coq Require Import Reals ZArith Lia.
From Flocq Require Import Core Plus_error.
From Double Require Import DWPlus F2Sum F2SumFLX.

Open Scope R_scope.

Definition prec : Z := 53.
Definition emin : Z := -1074.
Definition ne (n : Z) : bool := negb (Z.even n).

#[export] Instance prec_gt_0 : Prec_gt_0 prec.
Proof. unfold Prec_gt_0, prec; lia. Qed.

Notation fmtF := (generic_format radix2 (FLT_exp emin prec)).
Notation fmtX := (generic_format radix2 (FLX_exp prec)).
Notation rndF := (round radix2 (FLT_exp emin prec) (Znearest ne)).
Notation rndX := (round radix2 (FLX_exp prec) (Znearest ne)).

Lemma fmtF_rnd x : fmtF (rndF x).
Proof. apply generic_format_round; auto with typeclass_instances. Qed.

Lemma fmtF_fmtX x : fmtF x -> fmtX x.
Proof. apply generic_format_FLX_FLT. Qed.

(** A sum of two binary64 numbers rounds alike in both models. *)
Lemma sum_round a b : fmtF a -> fmtF b -> rndF (a + b) = rndX (a + b).
Proof.
  intros Fa Fb.
  destruct (Rle_or_lt (bpow radix2 (emin + prec - 1)) (Rabs (a + b))) as [H | H].
  - now apply round_FLT_FLX.
  - assert (Fs : fmtF (a + b)).
    { apply FLT_format_plus_small; auto with typeclass_instances.
      apply Rlt_le, Rlt_le_trans with (1 := H).
      apply bpow_le; unfold emin, prec; lia. }
    rewrite round_generic by auto with typeclass_instances.
    rewrite round_generic; auto with typeclass_instances.
    now apply fmtF_fmtX.
Qed.

Lemma diff_round a b : fmtF a -> fmtF b -> rndF (a - b) = rndX (a - b).
Proof.
  intros Fa Fb. unfold Rminus.
  apply sum_round; [exact Fa | now apply generic_format_opp].
Qed.

(** The binary64 algorithms, as the Rust functions compute them. *)
Definition two_sum (a b : R) : R * R :=
  let s := rndF (a + b) in
  let a' := rndF (s - b) in
  let b' := rndF (s - a') in
  let da := rndF (a - a') in
  let db := rndF (b - b') in
  (s, rndF (da + db)).

Definition fast_two_sum (a b : R) : R * R :=
  let s := rndF (a + b) in
  (s, rndF (b - rndF (s - a))).

Definition add_f64 (xh xl y : R) : R * R :=
  let '(sh, sl) := two_sum xh y in
  fast_two_sum sh (rndF (xl + sl)).

Definition add (xh xl yh yl : R) : R * R :=
  let '(sh, sl) := two_sum xh yh in
  let '(th, tl) := two_sum xl yl in
  let '(vh, vl) := fast_two_sum sh (rndF (sl + th)) in
  fast_two_sum vh (rndF (tl + vl)).

(** Each equals its unbounded-model counterpart on binary64 inputs. *)
Lemma two_sum_eq a b : fmtF a -> fmtF b ->
  two_sum a b = (TwoSum_sum prec ne a b, TwoSum_err prec ne a b).
Proof.
  intros Fa Fb. unfold two_sum, TwoSum_sum, TwoSum_err, TwoSum; simpl.
  rewrite (sum_round a b Fa Fb).
  assert (Fs : fmtF (rndX (a + b))) by (rewrite <- (sum_round a b Fa Fb); apply fmtF_rnd).
  rewrite (diff_round _ b Fs Fb).
  assert (Fa' : fmtF (rndX (rndX (a + b) - b))) by (rewrite <- (diff_round _ b Fs Fb); apply fmtF_rnd).
  rewrite (diff_round _ _ Fs Fa').
  rewrite (diff_round a _ Fa Fa').
  assert (Fb' : fmtF (rndX (rndX (a + b) - rndX (rndX (a + b) - b))))
    by (rewrite <- (diff_round _ _ Fs Fa'); apply fmtF_rnd).
  rewrite (diff_round b _ Fb Fb').
  rewrite sum_round; [reflexivity | | ].
  - rewrite <- (diff_round a _ Fa Fa'); apply fmtF_rnd.
  - rewrite <- (diff_round b _ Fb Fb'); apply fmtF_rnd.
Qed.

Lemma fast_two_sum_eq a b : fmtF a -> fmtF b ->
  fast_two_sum a b = F2Sum.Fast2Sum prec ne a b.
Proof.
  intros Fa Fb. unfold fast_two_sum, F2Sum.Fast2Sum, F2SumFLX.Fast2Sum; simpl.
  rewrite (sum_round a b Fa Fb).
  assert (Fs : fmtF (rndX (a + b))) by (rewrite <- (sum_round a b Fa Fb); apply fmtF_rnd).
  rewrite (diff_round _ a Fs Fa).
  rewrite diff_round; [reflexivity | exact Fb | ].
  rewrite <- (diff_round _ a Fs Fa); apply fmtF_rnd.
Qed.

Lemma two_sum_fmt a b : fmtF a -> fmtF b ->
  fmtF (TwoSum_sum prec ne a b) /\ fmtF (TwoSum_err prec ne a b).
Proof.
  intros Fa Fb. pose proof (two_sum_eq a b Fa Fb) as E.
  unfold two_sum in E. injection E; intros E2 E1.
  rewrite <- E1, <- E2. split; apply fmtF_rnd.
Qed.

Lemma fast_two_sum_fmt a b : fmtF a -> fmtF b ->
  fmtF (fst (F2Sum.Fast2Sum prec ne a b)) /\ fmtF (snd (F2Sum.Fast2Sum prec ne a b)).
Proof.
  intros Fa Fb. rewrite <- (fast_two_sum_eq a b Fa Fb).
  unfold fast_two_sum; simpl. split; apply fmtF_rnd.
Qed.

(** A binary64 double-word number is a double-word number of the unbounded model. *)
Lemma dw_of_binary64 xh xl : fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  double_word prec ne xh xl.
Proof.
  intros Fh Fl E. split; [split; now apply fmtF_fmtX | ].
  rewrite <- (sum_round xh xl Fh Fl). exact E.
Qed.

Theorem add_f64_bound xh xl y : fmtF xh -> fmtF xl -> fmtF y -> xh = rndF (xh + xl) ->
  let '(zh, zl) := add_f64 xh xl y in
  Rabs ((zh + zl - (xh + xl + y)) / (xh + xl + y)) <= 2 * bpow radix2 (- prec) ^ 2.
Proof.
  intros Fh Fl Fy E.
  pose proof (@DWPlusFP_bound prec (ltac:(unfold prec; lia)) ne eq_refl
                (ltac:(unfold prec; lia)) xh xl y (fmtF_fmtX y Fy) (dw_of_binary64 xh xl Fh Fl E)) as B.
  unfold relative_errorDWFP in B. unfold add_f64.
  rewrite (two_sum_eq xh y Fh Fy).
  destruct (two_sum_fmt xh y Fh Fy) as [Fsh Fsl].
  rewrite (sum_round xl _ Fl Fsl).
  assert (Fv : fmtF (rndX (xl + TwoSum_err prec ne xh y)))
    by (rewrite <- (sum_round xl _ Fl Fsl); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fsh Fv).
  destruct (F2Sum.Fast2Sum prec ne _ _) eqn:Z; simpl in B. exact B.
Qed.

Theorem add_bound xh xl yh yl :
  fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  fmtF yh -> fmtF yl -> yh = rndF (yh + yl) ->
  xh + xl + (yh + yl) <> 0 ->
  let '(zh, zl) := add xh xl yh yl in
  Rabs ((zh + zl - (xh + xl + (yh + yl))) / (xh + xl + (yh + yl)))
    <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Hn.
  pose proof (@DWPlusDW_relerr_bound prec (ltac:(unfold prec; lia)) ne eq_refl
                (ltac:(unfold prec; lia)) xh xl yh yl
                (dw_of_binary64 xh xl Fxh Fxl Ex) (dw_of_binary64 yh yl Fyh Fyl Ey) Hn) as B.
  unfold relative_errorDWDW in B. unfold add.
  rewrite (two_sum_eq xh yh Fxh Fyh), (two_sum_eq xl yl Fxl Fyl).
  destruct (two_sum_fmt xh yh Fxh Fyh) as [Fsh Fsl].
  destruct (two_sum_fmt xl yl Fxl Fyl) as [Fth Ftl].
  rewrite (sum_round _ _ Fsl Fth).
  assert (Fc : fmtF (rndX (TwoSum_err prec ne xh yh + TwoSum_sum prec ne xl yl)))
    by (rewrite <- (sum_round _ _ Fsl Fth); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fsh Fc).
  destruct (fast_two_sum_fmt _ _ Fsh Fc) as [Fvh Fvl].
  set (V := F2Sum.Fast2Sum prec ne (TwoSum_sum prec ne xh yh)
              (rndX (TwoSum_err prec ne xh yh + TwoSum_sum prec ne xl yl))) in *.
  destruct V as [vh vl]. cbn [fst snd] in Fvh, Fvl, B. cbv beta iota.
  rewrite (sum_round _ _ Ftl Fvl).
  assert (Fw : fmtF (rndX (TwoSum_err prec ne xl yl + vl)))
    by (rewrite <- (sum_round _ _ Ftl Fvl); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fvh Fw).
  set (Z := F2Sum.Fast2Sum prec ne vh (rndX (TwoSum_err prec ne xl yl + vl))) in *.
  destruct Z as [zh zl]. exact B.
Qed.

Lemma round_NE_opp_ne x : rndF (- x) = - rndF x.
Proof.
  assert (Hne : ne = fun n => negb (Z.even n)) by reflexivity.
  rewrite Hne. apply round_NE_opp.
Qed.

(** [sub] is [add] of the exact negation. Negating both words keeps a binary64
    double-word number one, since round-to-nearest-even is symmetric. *)
Definition sub (xh xl yh yl : R) : R * R := add xh xl (- yh) (- yl).

Lemma dw_opp yh yl : yh = rndF (yh + yl) -> - yh = rndF (- yh + - yl).
Proof.
  intros E.
  replace (- yh + - yl) with (- (yh + yl)) by ring.
  rewrite round_NE_opp_ne. now rewrite <- E.
Qed.

Theorem sub_bound xh xl yh yl :
  fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  fmtF yh -> fmtF yl -> yh = rndF (yh + yl) ->
  xh + xl - (yh + yl) <> 0 ->
  let '(zh, zl) := sub xh xl yh yl in
  Rabs ((zh + zl - (xh + xl - (yh + yl))) / (xh + xl - (yh + yl)))
    <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Hn.
  replace (xh + xl - (yh + yl)) with (xh + xl + (- yh + - yl)) in * by ring.
  apply add_bound; auto using generic_format_opp, dw_opp.
Qed.
