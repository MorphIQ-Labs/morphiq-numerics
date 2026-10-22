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

(** The exact angle of each form. *)
Definition form_value (f : form) (phi : R) : R :=
  match f with
  | Phi => phi
  | HalfPiMinus => PI / 2 - phi
  | HalfPiPlus => PI / 2 + phi
  | PiMinus => PI - phi
  end.

(** The numeric core of one form: [y] within [2^-104] of [C +- phihat], [C] within [1e-32] of
    the constant [K], [phihat] within [eF] of [phi]. *)
Lemma form_num K s C phi phihat y eF : (s = 1 \/ s = -1) -> 1.5707 <= K -> 0 < phi <= 0.7854 ->
  Rabs (C - K) <= / 100000000000000000000000000000000 -> Rabs (phihat - phi) <= eF * phi ->
  0 <= eF <= / 9223372036854775808 * 1.0001 -> 0 < C + s * phihat ->
  Rabs (y - (C + s * phihat)) <= bpow radix2 (-104) * (C + s * phihat) ->
  0.78 <= K + s * phi ->
  Rabs (y - (K + s * phi)) <= bpow radix2 (-62) * (K + s * phi).
Proof.
  intros Hs HK Hphi HC Hph HeF HS Hy HZ.
  assert (b104 : bpow radix2 (-104) = / 20282409603651670423947251286016) by (bpow_num; reflexivity).
  assert (b62 : bpow radix2 (-62) = / 4611686018427387904) by (bpow_num; reflexivity).
  rewrite b104 in Hy. rewrite b62.
  assert (Hsd : Rabs ((C + s * phihat) - (K + s * phi)) <= / 100000000000000000000000000000000 + eF * phi).
  { replace ((C + s * phihat) - (K + s * phi)) with ((C - K) + s * (phihat - phi)) by ring.
    apply Rle_trans with (Rabs (C - K) + Rabs (s * (phihat - phi))); [apply Rabs_triang | ].
    rewrite Rabs_mult. assert (Rabs s = 1) by (destruct Hs as [E | E]; rewrite E; [apply Rabs_R1 | rewrite Rabs_left by lra; ring]).
    rewrite H. lra. }
  set (Z := K + s * phi) in *. set (S := C + s * phihat) in *.
  apply Rabs_le_inv in Hy as [Hy1 Hy2]. apply Rabs_le_inv in Hsd as [Hd1 Hd2].
  assert (Hphi_le : phi <= 1.01 * Z) by lra.
  assert (HeFphi : eF * phi <= eF * (1.01 * Z)) by (apply Rmult_le_compat_l; lra).
  assert (HeF2 : eF * (1.01 * Z) <= / 4611686018427387904 * 0.51 * Z).
  { assert (eF * 1.01 <= / 4611686018427387904 * 0.51) by lra. nra. }
  assert (HSZ : S <= Z + / 100000000000000000000000000000000 + eF * phi) by lra.
  assert (HyS : / 20282409603651670423947251286016 * S <= / 20282409603651670423947251286016 * 1.0001 * Z).
  { assert (/ 100000000000000000000000000000000 + eF * phi <= 0.0001 * Z) by nra.
    assert (S <= 1.0001 * Z) by lra. nra. }
  assert (Hc0 : / 100000000000000000000000000000000 <= / 4611686018427387904 * 0.01 * Z) by nra.
  apply Rabs_le. split; nra.
Qed.

Lemma rndF_le_pow e v : v <= bpow radix2 e -> (-1074 <= e)%Z -> rndF v <= bpow radix2 e.
Proof. intros H He. apply round_le_generic; [exact _ | exact _ | apply fmt_bpow; exact He | exact H]. Qed.

Lemma neg_dw ph pl : finite ph -> finite pl -> B ph = rndF (B ph + B pl) ->
  finite (fneg ph) /\ finite (fneg pl) /\ B (fneg ph) = rndF (B (fneg ph) + B (fneg pl)).
Proof.
  intros Fh Fl D. destruct (fneg_val ph Fh) as [F1 V1]. destruct (fneg_val pl Fl) as [F2 V2].
  split; [exact F1 | split; [exact F2 | ]]. rewrite V1, V2.
  replace (- B ph + - B pl) with (- (B ph + B pl)) by ring. rewrite round_NE_opp_ne, <- D. reflexivity.
Qed.

(** One form: a normalized double-word [x] near the constant [K], plus or minus [phi]. *)
Lemma form_step s xh xl yh yl phi phihat K eF : (s = 1 \/ s = -1) ->
  finite xh -> finite xl -> finite yh -> finite yl ->
  B xh = rndF (B xh + B xl) -> B yh = rndF (B yh + B yl) ->
  1 <= B xh <= 4 -> Rabs (B xl) <= bpow radix2 (-52) * B xh ->
  Rabs (B yh) <= 99 / 100 * B xh -> Rabs (B yl) <= bpow radix2 (-52) * B xh ->
  B yh + B yl = s * phihat ->
  1.5707 <= K -> 0 < phi <= 0.7854 -> Rabs (B xh + B xl - K) <= / 100000000000000000000000000000000 ->
  Rabs (phihat - phi) <= eF * phi -> 0 <= eF <= / 9223372036854775808 * 1.0001 ->
  0.78 <= K + s * phi -> K + s * phi <= 3.15 ->
  exists zh zl, add64 xh xl yh yl = (zh, zl) /\ finite zh /\ finite zl /\ B zh = rndF (B zh + B zl) /\
    bpow radix2 (-905) <= B zh /\ B zh <= 4 /\
    Rabs (B zh + B zl - (K + s * phi)) <= bpow radix2 (-62) * (K + s * phi).
Proof.
  intros Hs Fxh Fxl Fyh Fyl Dx Dy Hx Hxl Hyh Hyl Hy HK Hphi HC Hph HeF HZ1 HZ2.
  destruct (dw_add_ok xh xl yh yl Fxh Fxl Fyh Fyl Dx Dy Hx Hxl Hyh Hyl) as [zh [zl [Ea [Fzh [Fzl [Dz [Err Hsum]]]]]]].
  exists zh, zl. split; [exact Ea | ]. split; [exact Fzh | ]. split; [exact Fzl | ]. split; [exact Dz | ].
  set (C := B xh + B xl) in *.
  assert (HS : C + (B yh + B yl) = C + s * phihat) by (rewrite Hy; reflexivity).
  rewrite HS in Err, Hsum.
  assert (Spos : 0 < C + s * phihat) by (destruct Hx as [X1 X2]; lra).
  assert (HN : Rabs (B zh + B zl - (K + s * phi)) <= bpow radix2 (-62) * (K + s * phi)).
  { apply (form_num K s C phi phihat (B zh + B zl) eF); try assumption. }
  split; [ | split; [ | exact HN]].
  - rewrite Dz. apply rndF_bpow_le with (e := (-905)%Z); [lia | ].
    apply Rle_trans with (bpow radix2 (-10)); [apply bpow_le; lia | ].
    apply Rabs_le_inv in HN as [N1 N2]. assert (bpow radix2 (-10) <= 0.01) by (bpow_num; interval with (i_prec 60)). 
    assert (b62 : bpow radix2 (-62) <= 1 / 1000) by (apply Rle_trans with (bpow radix2 (-10)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]).
    nra.
  - rewrite Dz. replace 4 with (bpow radix2 2) by (change (bpow radix2 2) with 4; reflexivity).
    apply rndF_le_pow; [ | lia]. apply Rabs_le_inv in HN as [N1 N2].
    assert (b62 : bpow radix2 (-62) <= 1 / 1000) by (apply Rle_trans with (bpow radix2 (-10)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]).
    change (bpow radix2 2) with 4. nra.
Qed.

(** The post stage: the form's double-word and the start for the accurate path. *)
Theorem post_ok th tl f ph pl phi :
  atan2_series th tl = (ph, pl) -> finite ph -> finite pl -> B ph = rndF (B ph + B pl) ->
  bpow radix2 (-902) <= phi -> phi <= PI / 4 ->
  Rabs (B ph + B pl - phi) <= bpow radix2 (-63) * (1 + bpow radix2 (-40)) * phi ->
  exists yh yl, atan2_post th tl f = ((yh, yl), (ph, pl)) /\ finite yh /\ finite yl /\
    B yh = rndF (B yh + B yl) /\ bpow radix2 (-905) <= B yh /\ B yh <= 4 /\
    Rabs (B yh + B yl - form_value f phi) <= bpow radix2 (-62) * form_value f phi.
Proof.
  intros Hs Fph Fpl Dw Hlo Hhi Hsr.
  pose proof pi_bounds as [Pi1 Pi2]. pose proof (bpow_gt_0 radix2 (-902)) as P902.
  assert (HeF : 0 <= bpow radix2 (-63) * (1 + bpow radix2 (-40)) <= / 9223372036854775808 * 1.0001).
  { split; [apply Rmult_le_pos; [apply bpow_ge_0 | pose proof (bpow_ge_0 radix2 (-40)); lra] | ].
    bpow_num. interval with (i_prec 100). }
  set (eF := bpow radix2 (-63) * (1 + bpow radix2 (-40))) in *.
  set (phihat := B ph + B pl) in *.
  assert (Hphi_hi : phi <= 0.7854) by lra.
  assert (Hpos : 0 < phi) by lra.
  apply Rabs_le_inv in Hsr as [Hs1 Hs2]. destruct HeF as [HeF0 HeF1].
  assert (Hph_lo : 0.99 * phi <= phihat) by nra.
  assert (Hph_hi : phihat <= 0.78541) by nra.
  assert (Hpn : bpow radix2 (-1022) <= Rabs phihat).
  { assert (Hb : bpow radix2 (-902) = 2 * bpow radix2 (-903)) by (replace (-902)%Z with (-903 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-903)) as P903.
    rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-903)); [apply bpow_le; lia | lra]. }
  pose proof (dw_low ph pl Hpn Dw) as Hlow.
  assert (Hphpos : 0 < B ph).
  { rewrite Dw. apply Rlt_le_trans with (bpow radix2 (-903)); [apply bpow_gt_0 | apply rndF_bpow_le; [lia | ]].
    assert (Hb : bpow radix2 (-902) = 2 * bpow radix2 (-903)) by (replace (-902)%Z with (-903 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-903)). nra. }
  rewrite (Rabs_pos_eq (B ph)) in Hlow by lra.
  assert (Hphle : B ph <= 0.79).
  { pose proof (rnd_rel phihat Hpn) as R. change (RNE phihat) with (rndF phihat) in R. rewrite <- Dw in R.
    pose proof (bpow_gt_0 radix2 (-53)) as P53. assert (bpow radix2 (-53) <= / 1000000) by (bpow_num; interval with (i_prec 60)).
    rewrite (Rabs_pos_eq phihat) in R by lra. apply Rabs_le_inv in R as [R1 R2]. nra. }
  assert (Hlow2 : Rabs (B pl) <= bpow radix2 (-52) * 1) by (apply Rle_trans with (bpow radix2 (-52) * B ph); [exact Hlow | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]]).
  destruct half_pi_dw as [hh [hl [Ehh [Fhh [Fhl [Dhh [Hpi [[Hh1 Hh2] Hhl]]]]]]]].
  unfold atan2_post. rewrite Hs. cbv iota. rewrite Ehh. cbv iota.
  assert (HK : 1.5707 <= PI / 2) by lra.
  assert (HC : Rabs (B hh + B hl - PI / 2) <= / 100000000000000000000000000000000).
  { apply Rle_trans with (1 := Hpi). apply Rinv_le_contravar; lra. }
  destruct (neg_dw ph pl Fph Fpl Dw) as [Fnh [Fnl Dn]].
  destruct (fneg_val ph Fph) as [_ Vnh]. destruct (fneg_val pl Fpl) as [_ Vnl].
  assert (Hyh : Rabs (B (fneg ph)) <= 99 / 100 * B hh) by (rewrite Vnh, Rabs_Ropp, Rabs_pos_eq by lra; lra).
  assert (Hyl : Rabs (B (fneg pl)) <= bpow radix2 (-52) * B hh).
  { rewrite Vnl, Rabs_Ropp. apply Rle_trans with (bpow radix2 (-52) * 1); [exact Hlow2 | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]]. }
  assert (Hnn : B (fneg ph) + B (fneg pl) = (-1) * phihat) by (rewrite Vnh, Vnl; unfold phihat; ring).
  assert (Hphat : Rabs (phihat - phi) <= eF * phi) by (apply Rabs_le; split; lra).
  destruct f.
  - (* Phi *)
    exists ph, pl. split; [reflexivity | ]. split; [exact Fph | ]. split; [exact Fpl | ]. split; [exact Dw | ].
    split.
    + apply Rle_trans with (bpow radix2 (-903)); [apply bpow_le; lia | ]. rewrite Dw. apply rndF_bpow_le; [lia | ].
      assert (Hb : bpow radix2 (-902) = 2 * bpow radix2 (-903)) by (replace (-902)%Z with (-903 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      pose proof (bpow_gt_0 radix2 (-903)). nra.
    + split; [lra | ]. cbn [form_value]. apply Rabs_le. assert (b62 : bpow radix2 (-62) = / 4611686018427387904) by (bpow_num; reflexivity). rewrite b62.
      split; nra.
  - (* HalfPiMinus *)
    destruct (form_step (-1) hh hl (fneg ph) (fneg pl) phi phihat (PI / 2) eF ltac:(right; reflexivity) Fhh Fhl Fnh Fnl Dhh Dn
      ltac:(split; [exact Hh1 | lra]) Hhl Hyh Hyl Hnn HK ltac:(split; assumption) HC Hphat ltac:(split; assumption) ltac:(lra) ltac:(lra))
      as [zh [zl [Ea [Fz1 [Fz2 [Dz [Lz [Uz Ez]]]]]]]].
    exists zh, zl. unfold sub64. rewrite Ea. split; [reflexivity | ]. repeat split; try assumption.
    cbn [form_value]. replace (PI / 2 + -1 * phi) with (PI / 2 - phi) in Ez by ring. exact Ez.
  - (* PiMinus *)
    assert (Hhl2 : Rabs (B hl) <= B hh / 2) by (apply Rle_trans with (bpow radix2 (-52) * B hh); [exact Hhl | assert (bpow radix2 (-52) <= / 2) by (bpow_num; interval with (i_prec 60)); nra]).
    assert (Hl900 : bpow radix2 (-900) <= B hh) by (apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | exact Hh1]).
    assert (Hu900 : B hh <= bpow radix2 900) by (apply Rle_trans with 2; [exact Hh2 | apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]]).
    pose proof (mul_f64_two_exact hh hl Fhh Fhl Dhh Hl900 Hu900 Hhl2) as M2.
    destruct (mul_f64_64 hh hl asin_two) as [mh ml] eqn:Emul. destruct M2 as [Fmh [Fml [Bmh Bml]]].
    assert (Dm : B mh = rndF (B mh + B ml)).
    { rewrite Bmh, Bml. apply dw_double_norm; [exact Dhh | ].
      assert (P52b : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
      pose proof Hhl as Hl'. rewrite P52b in Hl'. apply Rabs_le_inv in Hl' as [L1 L2].
      apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | assert (bpow radix2 (-1) = / 2) by (bpow_num; reflexivity); lra]. }
    destruct (form_step (-1) mh ml (fneg ph) (fneg pl) phi phihat PI eF ltac:(right; reflexivity) Fmh Fml Fnh Fnl Dm Dn
      ltac:(rewrite Bmh; split; lra) ltac:(rewrite Bml, Bmh; apply Rle_trans with (2 * (bpow radix2 (-52) * B hh)); [rewrite Rabs_mult, (Rabs_pos_eq 2) by lra; apply Rmult_le_compat_l; [lra | exact Hhl] | lra])
      ltac:(rewrite Bmh; lra) ltac:(rewrite Bmh; apply Rle_trans with (bpow radix2 (-52) * B hh); [exact Hyl | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]])
      Hnn ltac:(lra) ltac:(split; assumption) ltac:(rewrite Bmh, Bml; replace (2 * B hh + 2 * B hl - PI) with (2 * (B hh + B hl - PI / 2)) by field; rewrite Rabs_mult, (Rabs_pos_eq 2) by lra; apply Rle_trans with (2 * / 500000000000000000000000000000000); [apply Rmult_le_compat_l; [lra | exact Hpi] | interval with (i_prec 100)])
      Hphat ltac:(split; assumption) ltac:(lra) ltac:(lra))
      as [zh [zl [Ea [Fz1 [Fz2 [Dz [Lz [Uz Ez]]]]]]]].
    exists zh, zl. cbv iota. unfold sub64. rewrite Ea. split; [reflexivity | ]. repeat split; try assumption.
    cbn [form_value]. replace (PI + -1 * phi) with (PI - phi) in Ez by ring. exact Ez.
  - (* HalfPiPlus *)
    destruct (form_step 1 hh hl ph pl phi phihat (PI / 2) eF ltac:(left; reflexivity) Fhh Fhl Fph Fpl Dhh Dw
      ltac:(split; [exact Hh1 | lra]) Hhl ltac:(rewrite Rabs_pos_eq by lra; lra) ltac:(apply Rle_trans with (bpow radix2 (-52) * 1); [exact Hlow2 | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]])
      ltac:(unfold phihat; ring) HK ltac:(split; assumption) HC Hphat ltac:(split; assumption) ltac:(lra) ltac:(lra))
      as [zh [zl [Ea [Fz1 [Fz2 [Dz [Lz [Uz Ez]]]]]]]].
    exists zh, zl. rewrite Ea. split; [reflexivity | ]. repeat split; try assumption.
    cbn [form_value]. replace (PI / 2 + 1 * phi) with (PI / 2 + phi) in Ez by ring. exact Ez.
Qed.
