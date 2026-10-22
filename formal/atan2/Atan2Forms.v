(** atan2's four forms of the angle (docs/atan2.md section 3): [phi], [pi/2 - phi],
    [pi/2 + phi] and [pi - phi] from the double-word [phi = (ph, pl)] and
    the double-word [pi/2], each a normalized double-word within [2^-62] of
    the exact angle. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinNormal AsinDouble AsinPath
  Atan2Tables Atan2Kernel Atan2Ratio.
Open Scope R_scope.

(** The double-word [pi/2] the forms use. *)
Lemma half_pi_dw : exists hh hl,
  two_sum64 (aw (fst atan2_half_pi)) (aw (snd atan2_half_pi)) = (hh, hl) /\ finite hh /\ finite hl /\
  B hh = rndF (B hh + B hl) /\ Rabs (B hh + B hl - PI / 2) <= / 500000000000000000000000000000000 /\
  1 <= B hh <= 2 /\ Rabs (B hl) <= bpow radix2 (-52) * B hh.
Proof.
  assert (W : finite (aw (fst atan2_half_pi)) /\ finite (aw (snd atan2_half_pi)) /\
    B (aw (fst atan2_half_pi)) = IZR 884279719003555 * bpow radix2 (-49) /\
    B (aw (snd atan2_half_pi)) = IZR 4967757600021511 * bpow radix2 (-106)).
  { unfold atan2_half_pi. cbn [fst snd].
    destruct (word_ok_intro (0x3ff921fb54442d18)%Z false 7074237752028440%positive 52%nat (884279719003555)%Z 3%Z (-49)%Z
      eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
    destruct (word_ok_intro (0x3c91a62633145c07)%Z false 4967757600021511%positive 106%nat (4967757600021511)%Z 0%Z (-106)%Z
      eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
    repeat split; assumption. }
  destruct W as [Fhi [Flo [Vhi Vlo]]].
  set (hi := aw (fst atan2_half_pi)) in *. set (lo := aw (snd atan2_half_pi)) in *.
  assert (Hhi2 : Rabs (B hi) <= 2) by (rewrite Vhi; bpow_num; rewrite Rabs_pos_eq by (interval with (i_prec 60)); interval with (i_prec 60)).
  assert (Hlo2 : Rabs (B lo) <= 2) by (rewrite Vlo; bpow_num; rewrite Rabs_pos_eq by (interval with (i_prec 60)); interval with (i_prec 60)).
  assert (H2big : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1020).
  { intros v Hv. apply Rle_trans with 2; [exact Hv | apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]]. }
  pose proof (two_sum_ieee hi lo Fhi Flo (H2big _ Hhi2) (H2big _ Hlo2)) as TSH.
  destruct (two_sum64 hi lo) as [hh hl] eqn:Eth. destruct TSH as [Fhh [Fhl [Ehh Esh]]].
  exists hh, hl. split; [reflexivity | ]. split; [exact Fhh | ]. split; [exact Fhl | ].
  assert (Hhhdw : B hh = rndF (B hh + B hl)) by (rewrite Esh; exact Ehh).
  split; [exact Hhhdw | ].
  assert (Hpi : Rabs (B hh + B hl - PI / 2) <= / 500000000000000000000000000000000).
  { rewrite Esh, Vhi, Vlo. exact half_pi_close. }
  split; [exact Hpi | ].
  pose proof pi_bounds as [Pi1 Pi2]. apply Rabs_le_inv in Hpi as [Hp1 Hp2].
  assert (Hhhge : 1 <= B hh).
  { rewrite Ehh. apply round_ge_generic with (x := bpow radix2 0); [exact _ | exact _ | apply fmt_bpow; lia | ].
    change (bpow radix2 0) with 1. rewrite Vhi, Vlo. bpow_num. interval with (i_prec 60). }
  assert (Hhhn : bpow radix2 (-1022) <= Rabs (B hh + B hl)).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | lra]. }
  pose proof (dw_low hh hl Hhhn Hhhdw) as Hhl.
  rewrite (Rabs_pos_eq (B hh)) in Hhl by lra.
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  pose proof Hhl as Hhl'. rewrite P52 in Hhl'. apply Rabs_le_inv in Hhl' as [Hh1 Hh2].
  split; [split; [exact Hhhge | lra] | ].
  exact Hhl.
Qed.

(** The sum of two normalized double-words, one at most 99% of the other's size. *)
Lemma dw_add_ok xh xl yh yl : finite xh -> finite xl -> finite yh -> finite yl ->
  B xh = rndF (B xh + B xl) -> B yh = rndF (B yh + B yl) ->
  1 <= B xh <= 4 -> Rabs (B xl) <= bpow radix2 (-52) * B xh ->
  Rabs (B yh) <= 99 / 100 * B xh -> Rabs (B yl) <= bpow radix2 (-52) * B xh ->
  exists zh zl, add64 xh xl yh yl = (zh, zl) /\ finite zh /\ finite zl /\ B zh = rndF (B zh + B zl) /\
    Rabs (B zh + B zl - (B xh + B xl + (B yh + B yl))) <= bpow radix2 (-104) * (B xh + B xl + (B yh + B yl)) /\
    (B xh + B xl + (B yh + B yl)) >= 0.009 * B xh.
Proof.
  intros Fxh Fxl Fyh Fyl Dx Dy [X1 X2] Hxl Hyh Hyl.
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  rewrite P52 in Hxl, Hyl. apply Rabs_le_inv in Hxl as [Hxl1 Hxl2]. apply Rabs_le_inv in Hyl as [Hyl1 Hyl2].
  apply Rabs_le_inv in Hyh as [Hyh1 Hyh2].
  assert (Hyl' : Rabs (B yl) <= bpow radix2 (-52) * B xh) by (rewrite P52; apply Rabs_le; split; lra).
  assert (Hyl'' : Rabs (B yl) <= B xh * 1) by (rewrite P52 in Hyl'; nra).
  (* the sum is positive: yh may be negative *)
  assert (Hsum : B xh + B xl + (B yh + B yl) >= 0.009 * B xh).
  { assert (B yl >= - (B xh * / 4503599627370496)) by lra. nra. }
  assert (Hne : B xh + B xl + (B yh + B yl) <> 0) by lra.
  assert (Hbig : forall v, Rabs v <= 5 -> Rabs v <= bpow radix2 1016).
  { intros v Hv. apply Rle_trans with 5; [exact Hv | apply Rle_trans with (bpow radix2 3); [change (bpow radix2 3) with 8; lra | apply bpow_le; lia]]. }
  assert (R1 : Rabs (B xh) <= bpow radix2 1016) by (apply Hbig; rewrite Rabs_pos_eq by lra; lra).
  assert (R2 : Rabs (B xl) <= bpow radix2 1016) by (apply Hbig; apply Rabs_le; split; lra).
  assert (R3 : Rabs (B yh) <= bpow radix2 1016) by (apply Hbig; apply Rabs_le; split; lra).
  assert (R4 : Rabs (B yl) <= bpow radix2 1016) by (apply Hbig; apply Rabs_le; split; lra).
  pose proof (add_ieee xh xl yh yl Fxh Fxl Dx Fyh Fyl Dy R1 R2 R3 R4 Hne) as AD.
  assert (Hlx : bpow radix2 (-900) <= B xh) by (apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | exact X1]).
  assert (Hux : B xh <= bpow radix2 900) by (apply Rle_trans with 4; [exact X2 | apply Rle_trans with (bpow radix2 3); [change (bpow radix2 3) with 8; lra | apply bpow_le; lia]]).
  pose proof (add64_normalized xh xl yh yl Fxh Fxl Fyh Fyl Hlx Hux
    ltac:(rewrite P52; apply Rabs_le; split; lra) ltac:(rewrite P52; apply Rabs_le; split; lra)
    ltac:(apply Rabs_le; split; lra)) as NORM.
  destruct (add64 xh xl yh yl) as [zh zl] eqn:Ea. destruct AD as [Fzh [Fzl Err]].
  try cbv iota in NORM. destruct NORM as [_ [_ Nrm]].
  exists zh, zl. split; [reflexivity | ]. split; [exact Fzh | ]. split; [exact Fzl | ]. split; [exact Nrm | ]. split; [ | exact Hsum].
  set (S := B xh + B xl + (B yh + B yl)) in *.
  assert (Spos : 0 < S) by lra.
  assert (EA : 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) <= bpow radix2 (-104)).
  { replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. interval with (i_prec 200). }
  replace (B zh + B zl - S) with (((B zh + B zl - S) / S) * S) by (field; lra).
  rewrite Rabs_mult, (Rabs_pos_eq S) by lra.
  apply Rmult_le_compat_r; [lra | apply Rle_trans with (2 := EA); exact Err].
Qed.
