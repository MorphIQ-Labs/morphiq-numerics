(** asinh's logarithmic form, [2^-7 <= x < 2^28]: the transcription's fast value
    against [arcsinh], relatively within [2^-63]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft IEEE64Sqrt Grid Encodings RoundingCore RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinNormal AsinRecip AsinPath
  LnFastValue AsinhTables AsinhKernel AsinhConst AsinhWithin AsinhOps AsinhRoot.
Open Scope R_scope.

Lemma rabs_sub a b : Rabs (a - b) <= Rabs a + Rabs b.
Proof. unfold Rminus. apply Rle_trans with (Rabs a + Rabs (- b)); [apply Rabs_triang | rewrite Rabs_Ropp; lra]. Qed.

Lemma rabs_sub_r a b : Rabs a <= Rabs (a - b) + Rabs b.
Proof. apply Rle_trans with (Rabs ((a - b) + b)); [right; f_equal; ring | apply Rabs_triang]. Qed.

Lemma rnd_le_pow e v : (-1074 <= e)%Z -> v <= bpow radix2 e -> rndF v <= bpow radix2 e.
Proof. intros He H. apply round_le_generic; [exact _ | exact _ | apply fmt_bpow; exact He | exact H]. Qed.

Lemma bp_m7 : bpow radix2 (-7) = / 128. Proof. bpow_num. reflexivity. Qed.
Lemma bp_m14 : bpow radix2 (-14) = / 16384. Proof. bpow_num. reflexivity. Qed.
Lemma bp28 : bpow radix2 28 = 268435456. Proof. bpow_num. reflexivity. Qed.
Lemma bp_m52 : bpow radix2 (-52) = / 4503599627370496. Proof. bpow_num. reflexivity. Qed.
Lemma bp_m53 : bpow radix2 (-53) = / 9007199254740992. Proof. bpow_num. reflexivity. Qed.

(** Stage U: [u = 1 + x^2] as a double-word. *)
Lemma stage_u x : finite x -> bpow radix2 (-7) <= B x -> B x < bpow radix2 28 ->
  let '(sq, sqe) := two_prod64 x x in
  let '(h1, l1) := two_sum64 asin_one sq in
  let '(uh, ul) := add_f64_64 h1 l1 sqe in
  finite uh /\ finite ul /\ B uh = rndF (B uh + B ul) /\ 1 <= B uh /\ B uh <= bpow radix2 57 /\
  exists eu, Rabs eu <= bpow radix2 (-105) /\ B uh + B ul = (1 + B x * B x) * (1 + eu).
Proof.
  intros Fx L U.
  destruct one_val as [V1 F1].
  assert (HX : Rabs (B x) <= bpow radix2 28).
  { rewrite Rabs_pos_eq; [lra | pose proof (bpow_gt_0 radix2 (-7)); lra]. }
  assert (Hxx : bpow radix2 (-14) <= B x * B x < bpow radix2 56).
  { rewrite bp_m7 in L. rewrite bp28 in U. change (bpow radix2 56) with 72057594037927936.
    rewrite bp_m14. split.
    - assert (/ 128 * / 128 <= B x * B x) by (apply Rmult_le_compat; lra). lra.
    - assert (B x * B x <= B x * 268435456) by (apply Rmult_le_compat_l; lra). lra. }
  destruct Hxx as [Hxx1 Hxx2]. pose proof (bpow_gt_0 radix2 (-14)) as Pb14.
  assert (Dom : bpow radix2 (-969) <= Rabs (B x * B x)).
  { apply Rle_trans with (bpow radix2 (-14)); [apply bpow_le; lia | ]. pose proof (bpow_gt_0 radix2 (-14)). rewrite Rabs_pos_eq by lra. lra. }
  assert (TP := two_prod_ieee 28 28 x x Fx Fx HX HX ltac:(lia) ltac:(lia) ltac:(lia) (or_intror Dom)).
  destruct (two_prod64 x x) as [sq sqe] eqn:Ep. cbv beta iota in TP.
  destruct TP as [Fsq [Fsqe [Esq Esum]]].
  assert (Hsq1 : bpow radix2 (-14) <= B sq).
  { rewrite Esq. apply rndF_ge_bpow; [lia | lra]. }
  assert (Hsq2 : B sq <= bpow radix2 56).
  { rewrite Esq. apply rnd_le_pow; [lia | lra]. }
  assert (Hsqe : Rabs (B sqe) <= bpow radix2 4).
  { assert (E : B sqe = B x * B x - B sq) by lra.
    pose proof (rnd_err (B x * B x)) as R. rewrite <- Esq in R.
    rewrite Rabs_minus_sym in R. rewrite <- E in R.
    rewrite (Rabs_pos_eq (B x * B x)) in R by lra.
    assert (Hb : bpow radix2 (-53) = / 9007199254740992) by (bpow_num; reflexivity).
    assert (Hb2 : bpow radix2 (-1075) <= 1) by (apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra]).
    assert (Hb3 : bpow radix2 4 = 16) by (bpow_num; reflexivity).
    rewrite Hb in R. rewrite Hb3. change (bpow radix2 56) with 72057594037927936 in Hsq2.
    apply Rabs_le_inv in R. apply Rabs_le. split; nra. }
  (* 1 + sq *)
  assert (Hone : Rabs (B asin_one) <= bpow radix2 1020).
  { rewrite V1, Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply bpow_le; lia]. }
  assert (Hsqa : Rabs (B sq) <= bpow radix2 1020).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 56); [exact Hsq2 | apply bpow_le; lia]. }
  pose proof (two_sum_ieee asin_one sq F1 Fsq Hone Hsqa) as TS.
  destruct (two_sum64 asin_one sq) as [h1 l1] eqn:E2. cbv beta iota in TS.
  destruct TS as [Fh1 [Fl1 [Eh1 Es1]]].
  rewrite V1 in Eh1, Es1.
  assert (Hh1a : 1 <= B h1).
  { rewrite Eh1. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply rndF_ge_bpow; [lia | simpl; lra]]. }
  assert (Hh1b : B h1 <= bpow radix2 57).
  { rewrite Eh1. apply rnd_le_pow; [lia | ]. apply Rle_trans with (bpow radix2 56 + 1); [lra | ].
    change (bpow radix2 57) with (2 * bpow radix2 56). assert (1 <= bpow radix2 56) by (apply Rle_trans with (bpow radix2 0); [simpl; lra | apply bpow_le; lia]). lra. }
  assert (Dw1 : B h1 = rndF (B h1 + B l1)) by (rewrite Es1; exact Eh1).
  assert (Hl1 : Rabs (B l1) <= bpow radix2 (-52) * Rabs (B h1)).
  { apply lo_bound; [ | exact Dw1]. rewrite Rabs_pos_eq by lra.
    apply Rle_trans with 1; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra] | exact Hh1a]. }
  assert (Hl1b : Rabs (B l1) <= bpow radix2 6).
  { rewrite (Rabs_pos_eq (B h1)) in Hl1 by lra. rewrite bp_m52 in Hl1. 
    assert (Hb57 : B h1 <= bpow radix2 57) by exact Hh1b.
    change (bpow radix2 57) with 144115188075855872 in Hb57. change (bpow radix2 6) with 64.
    assert (/ 4503599627370496 * B h1 <= / 4503599627370496 * 144115188075855872) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hh1c : Rabs (B h1) <= bpow radix2 1018).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 57); [exact Hh1b | apply bpow_le; lia]. }
  assert (Hl1c : Rabs (B l1) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 6); [exact Hl1b | apply bpow_le; lia]. }
  assert (Hsqec : Rabs (B sqe) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 4); [exact Hsqe | apply bpow_le; lia]. }
  pose proof (add_f64_ieee h1 l1 sqe Fh1 Fl1 Fsqe Dw1 Hh1c Hl1c Hsqec) as AF.
  pose proof (add_f64_normalized_ieee h1 l1 sqe Fh1 Fl1 Fsqe Dw1 Hh1c Hl1c Hsqec) as AFN.
  destruct (add_f64_64 h1 l1 sqe) as [uh ul] eqn:E3. cbv beta iota in AF, AFN.
  destruct AF as [Fuh [Ful Bd]]. destruct AFN as [_ [_ Nrm]].
  assert (S0 : B h1 + B l1 + B sqe = 1 + B x * B x) by lra.
  assert (S0p : 0 < 1 + B x * B x) by lra.
  rewrite S0 in Bd.
  set (eu := (B uh + B ul - (1 + B x * B x)) / (1 + B x * B x)) in *.
  assert (Hq105 : 2 * bpow radix2 (- prec) ^ 2 = bpow radix2 (-105)).
  { replace (- prec)%Z with (-53)%Z by reflexivity. rewrite bp_m53. bpow_num. simpl. field. }
  rewrite Hq105 in Bd.
  assert (Heu : B uh + B ul = (1 + B x * B x) * (1 + eu)) by (unfold eu; field; lra).
  assert (Heu1 : Rabs eu <= bpow radix2 (-105)) by exact Bd.
  assert (Hsmall : bpow radix2 (-105) <= / 1000000).
  { apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; apply Rinv_le_contravar; lra]. }
  assert (Heu2 : Rabs eu <= / 1000000) by lra.
  apply Rabs_le_inv in Heu2. destruct Heu2 as [He1 He2].
  split; [exact Fuh | split; [exact Ful | split; [exact Nrm | ]]].
  assert (Hp1 : (1 + B x * B x) * (- / 1000000) <= (1 + B x * B x) * eu) by (apply Rmult_le_compat_l; lra).
  assert (Hp2 : (1 + B x * B x) * eu <= (1 + B x * B x) * / 1000000) by (apply Rmult_le_compat_l; lra).
  assert (Hlo : 1 <= B uh + B ul).
  { rewrite Heu. rewrite bp_m14 in Hxx1. lra. }
  assert (Hhi : B uh + B ul <= bpow radix2 57).
  { rewrite Heu. change (bpow radix2 57) with 144115188075855872. change (bpow radix2 56) with 72057594037927936 in Hxx2. lra. }
  split; [ | split].
  - rewrite Nrm. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply rndF_ge_bpow; [lia | simpl; lra]].
  - rewrite Nrm. apply rnd_le_pow; [lia | exact Hhi].
  - exists eu. split; [exact Heu1 | exact Heu].
Qed.

(** [2 s] is exact for a binary64 [s] in [[1, 2^500]]. *)
Lemma two_exact s : finite s -> 1 <= B s -> B s <= bpow radix2 500 ->
  finite (fmul asin_two s) /\ B (fmul asin_two s) = 2 * B s.
Proof.
  intros Fs L U. destruct two_val as [V2 F2].
  assert (Gs : fmtF (B s * bpow radix2 1)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (1 <= mag radix2 (B s))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. change (bpow radix2 (1 - 1)) with 1. exact L. }
    unfold emin, prec. lia. }
  assert (E2 : B asin_two * B s = B s * bpow radix2 1) by (rewrite V2; change (bpow radix2 1) with 2; ring).
  assert (Hb : Rabs (B asin_two * B s) <= bpow radix2 501).
  { rewrite E2. change (bpow radix2 1) with 2. rewrite Rabs_pos_eq by lra.
    change (bpow radix2 501) with (2 * bpow radix2 500). lra. }
  destruct (mul_abs2 asin_two s 501 F2 Fs Hb ltac:(lia)) as [F [E _]].
  split; [exact F | ].
  rewrite E, E2, round_generic by (try exact _; exact Gs).
  change (bpow radix2 1) with 2. ring.
Qed.

(** Stage root: [s = sh + sl] is [sqrt (uh + ul)] to a relative [2^-90]. *)
Lemma stage_root uh ul : finite uh -> finite ul -> B uh = rndF (B uh + B ul) ->
  1 <= B uh -> B uh <= bpow radix2 57 -> 1 <= B uh + B ul -> B uh + B ul <= bpow radix2 58 ->
  let root := fsqrt uh in
  let '(rs, rse) := two_prod64 root root in
  let residual := fadd (fsub (fsub uh rs) rse) ul in
  let '(sh, sl) := two_sum64 root (fdiv residual (fmul asin_two root)) in
  finite sh /\ finite sl /\ B sh = rndF (B sh + B sl) /\ Rabs (B sh) <= bpow radix2 30 /\
  exists w, w * w = B uh + B ul /\ 1 <= w /\ w <= bpow radix2 29 /\
    Rabs (B sh + B sl - w) <= / 1237940039285380274899124224 * w.
Proof.
  intros Fuh Ful Dw L1 L2 U1 U2. cbv zeta.
  set (U := B uh + B ul) in *.
  (* the root *)
  destruct (sqrt_ieee uh) as [Es Fs'].
  set (root := fsqrt uh) in *.
  assert (Froot : finite root) by (apply (proj2 Fs'); split; [exact Fuh | lra]).
  set (r0 := sqrt (B uh)).
  assert (Hr0sq : r0 * r0 = B uh) by (unfold r0; apply sqrt_sqrt; lra).
  assert (Hr01 : 1 <= r0) by (unfold r0; apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; lra]).
  assert (Hr02 : r0 <= bpow radix2 29).
  { apply Rnot_lt_le; intros H. change (bpow radix2 29) with 536870912 in H.
    assert (536870912 * 536870912 <= r0 * r0) by (apply Rmult_le_compat; lra).
    change (bpow radix2 57) with 144115188075855872 in L2. lra. }
  assert (Hroot1 : 1 <= B root).
  { rewrite Es. change (sqrt (B uh)) with r0. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply rndF_ge_bpow; [lia | simpl; lra]]. }
  assert (Hroot2 : B root <= bpow radix2 29).
  { rewrite Es. change (sqrt (B uh)) with r0. apply rnd_le_pow; [lia | exact Hr02]. }
  (* w *)
  set (w := sqrt U).
  assert (Hww : w * w = U) by (unfold w; apply sqrt_sqrt; lra).
  assert (Hw1 : 1 <= w) by (unfold w; apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; lra]).
  assert (Hw2 : w <= bpow radix2 29).
  { apply Rnot_lt_le; intros H. change (bpow radix2 29) with 536870912 in H.
    assert (536870912 * 536870912 < w * w) by (apply Rmult_le_0_lt_compat; lra).
    change (bpow radix2 58) with 288230376151711744 in U2. lra. }
  (* |ul| <= 2^-52 uh *)
  assert (Hul : Rabs (B ul) <= / 4503599627370496 * B uh).
  { pose proof (lo_bound (B uh) (B ul) ltac:(rewrite Rabs_pos_eq by lra; apply Rle_trans with 1; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra] | exact L1]) Dw) as H.
    rewrite bp_m52, (Rabs_pos_eq (B uh)) in H by lra. exact H. }
  (* w - r0 = ul / (w + r0) *)
  assert (Hwr : Rabs (w - r0) <= / 4503599627370496 * r0).
  { assert (E : (w - r0) * (w + r0) = B ul) by (unfold U in Hww; nra).
    assert (Hs : r0 <= w + r0) by lra.
    assert (Habs : Rabs (w - r0) * (w + r0) <= / 4503599627370496 * B uh).
    { rewrite <- (Rabs_pos_eq (w + r0)) at 1 by lra. rewrite <- Rabs_mult, E. exact Hul. }
    rewrite <- Hr0sq in Habs.
    apply Rmult_le_reg_r with (w + r0); [lra | ].
    apply Rle_trans with (/ 4503599627370496 * (r0 * r0)); [exact Habs | ].
    assert (0 <= r0) by lra. nra. }
  (* |root - r0| *)
  assert (Hrr : Rabs (B root - r0) <= / 9007199254740992 * r0 + bpow radix2 (-1075)).
  { rewrite Es. change (sqrt (B uh)) with r0.
    pose proof (rnd_err r0) as R. rewrite bp_m53, (Rabs_pos_eq r0) in R by lra. exact R. }
  assert (Heta : 0 < bpow radix2 (-1075) <= 1e-30).
  { split; [apply bpow_gt_0 | ].
    assert (bpow radix2 (-1075) <= bpow radix2 (-100)) by (apply bpow_le; lia).
    assert (bpow radix2 (-100) <= 1e-30) by (bpow_num; apply Rle_trans with (/ 1000000000000000000000000000000); [apply Rinv_le_contravar; [lra | ]; simpl; lra | lra]).
    lra. }
  assert (Hroot : Rabs (B root - w) <= / 2251799813685248 * w).
  { apply Rabs_le_inv in Hrr. apply Rabs_le_inv in Hwr. apply Rabs_le.
    destruct Heta as [Hta Htb].
    assert (Hn : bpow radix2 (-1075) <= 1e-30 * r0) by nra.
    split; nra. }
  (* root * root *)
  set (rt := B root) in *.
  assert (HRa : Rabs rt <= bpow radix2 29) by (rewrite Rabs_pos_eq by lra; exact Hroot2).
  assert (Hrr1 : bpow radix2 0 <= rt * rt) by (simpl; nra).
  assert (Dom : bpow radix2 (-969) <= Rabs (rt * rt)).
  { apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | ]. rewrite Rabs_pos_eq by nra. exact Hrr1. }
  assert (TP := two_prod_ieee 29 29 root root Froot Froot HRa HRa ltac:(lia) ltac:(lia) ltac:(lia) (or_intror Dom)).
  destruct (two_prod64 root root) as [rs rse] eqn:Ep. cbv beta iota in TP.
  destruct TP as [Frs [Frse [Ers Esum]]].
  change (B root) with rt in Ers, Esum.
  assert (Hrr2 : rt * rt <= bpow radix2 58).
  { change (bpow radix2 58) with 288230376151711744. change (bpow radix2 29) with 536870912 in Hroot2. nra. }
  assert (Hrs1 : 1 <= B rs).
  { rewrite Ers. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply rndF_ge_bpow; [lia | exact Hrr1]]. }
  assert (Hrs2 : B rs <= bpow radix2 58).
  { rewrite Ers. apply rnd_le_pow; [lia | exact Hrr2]. }
  assert (Hrse : Rabs (B rse) <= / 4503599627370496 * B rs).
  { assert (E : B rse = rt * rt - B rs) by lra.
    pose proof (rnd_rel_f (rt * rt) ltac:(apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | rewrite Rabs_pos_eq by nra; exact Hrr1])) as H.
    rewrite <- Ers, Rabs_minus_sym, <- E in H.
    rewrite bp_m53, (Rabs_pos_eq (rt * rt)) in H by nra.
    assert (Hb : B rs >= 1) by lra.
    assert (rt * rt <= B rs + Rabs (B rse)) by (pose proof (Rle_abs (B rse)); lra).
    pose proof (Rabs_pos (B rse)). nra. }
  (* the residual *)
  assert (Hp58 : 1 <= bpow radix2 58) by (apply Rle_trans with (bpow radix2 0); [simpl; lra | apply bpow_le; lia]).
  assert (Hp57 : bpow radix2 57 <= bpow radix2 58) by (apply bpow_le; lia).
  destruct (sub_abs2 uh rs 58 Fuh Frs ltac:(apply Rabs_le; lra) ltac:(lia)) as [Fr1 [Er1 Br1]].
  assert (Hrse58 : Rabs (B rse) <= bpow radix2 6).
  { change (bpow radix2 6) with 64. change (bpow radix2 58) with 288230376151711744 in Hrs2.
    assert (/ 4503599627370496 * B rs <= / 4503599627370496 * 288230376151711744) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hp6 : bpow radix2 6 <= bpow radix2 58) by (apply bpow_le; lia).
  destruct (sub_abs2 (fsub uh rs) rse 59 Fr1 Frse ltac:(apply Rle_trans with (Rabs (B (fsub uh rs)) + Rabs (B rse)); [apply rabs_sub | ]; change (bpow radix2 59) with (2 * bpow radix2 58); lra) ltac:(lia)) as [Fr2 [Er2 Br2]].
  assert (Hul6 : Rabs (B ul) <= bpow radix2 6).
  { change (bpow radix2 6) with 64. change (bpow radix2 57) with 144115188075855872 in L2.
    assert (/ 4503599627370496 * B uh <= / 4503599627370496 * 144115188075855872) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hr3s : Rabs (B (fsub (fsub uh rs) rse) + B ul) <= bpow radix2 60).
  { apply Rle_trans with (Rabs (B (fsub (fsub uh rs) rse)) + Rabs (B ul)); [apply Rabs_triang | ].
    change (bpow radix2 60) with 1152921504606846976. change (bpow radix2 59) with 576460752303423488 in Br2.
    change (bpow radix2 6) with 64 in Hul6. lra. }
  destruct (add_abs2 (fsub (fsub uh rs) rse) ul 60 Fr2 Ful Hr3s ltac:(lia)) as [Fr3 [Er3 Br3]].
  set (residual := fadd (fsub (fsub uh rs) rse) ul) in *.
  destruct (two_exact root Froot Hroot1 ltac:(apply Rle_trans with (bpow radix2 29); [exact Hroot2 | apply bpow_le; lia])) as [Fden Eden].
  change (B root) with rt in Eden.
  assert (Hden0 : B (fmul asin_two root) <> 0) by (rewrite Eden; lra).
  assert (Hqd : Rabs (B residual / B (fmul asin_two root)) <= bpow radix2 60).
  { rewrite Eden, Rabs_div' by lra. rewrite (Rabs_pos_eq (2 * rt)) by lra.
    apply Rmult_le_reg_r with (2 * rt); [lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
    change (bpow radix2 60) with 1152921504606846976 in Br3 |- *. nra. }
  destruct (div_abs2 residual (fmul asin_two root) 60 Fr3 Hden0 Hqd ltac:(lia)) as [Fc [Ec Bc]].
  set (c := fdiv residual (fmul asin_two root)) in *.
  assert (Hrta : Rabs (B root) <= bpow radix2 1020) by (apply Rle_trans with (bpow radix2 29); [exact HRa | apply bpow_le; lia]).
  assert (Hca : Rabs (B c) <= bpow radix2 1020) by (apply Rle_trans with (bpow radix2 60); [exact Bc | apply bpow_le; lia]).
  pose proof (two_sum_ieee root c Froot Fc Hrta Hca) as TS.
  destruct (two_sum64 root c) as [sh sl] eqn:Esh. cbv beta iota in TS. destruct TS as [Fsh [Fsl [Esh1 Esh2]]].
  assert (Hw1b : 1 <= w <= 1073741824).
  { split; [exact Hw1 | ]. apply Rle_trans with (bpow radix2 29); [exact Hw2 | change (bpow radix2 29) with 536870912; lra]. }
  change (B root) with rt in Esh2.
  assert (Hmain : Rabs (rt + B c - w) <= / 1237940039285380274899124224 * w).
  { assert (H1 : Rabs (B (fsub uh rs) - (B uh - B rs)) <= / 9007199254740992 * Rabs (B uh - B rs) + bpow radix2 (-1075)).
    { rewrite Er1. pose proof (rnd_err (B uh - B rs)) as H. rewrite bp_m53 in H. exact H. }
    assert (H2 : Rabs (B (fsub (fsub uh rs) rse) - (B (fsub uh rs) - B rse)) <= / 9007199254740992 * Rabs (B (fsub uh rs) - B rse) + bpow radix2 (-1075)).
    { rewrite Er2. pose proof (rnd_err (B (fsub uh rs) - B rse)) as H. rewrite bp_m53 in H. exact H. }
    assert (H3 : Rabs (B residual - (B (fsub (fsub uh rs) rse) + B ul)) <= / 9007199254740992 * Rabs (B (fsub (fsub uh rs) rse) + B ul) + bpow radix2 (-1075)).
    { rewrite Er3. pose proof (rnd_err (B (fsub (fsub uh rs) rse) + B ul)) as H. rewrite bp_m53 in H. exact H. }
    assert (H4 : Rabs (B c - B residual / (2 * rt)) <= / 9007199254740992 * Rabs (B residual / (2 * rt)) + bpow radix2 (-1075)).
    { rewrite Ec, Eden. pose proof (rnd_err (B residual / (2 * rt))) as H. rewrite bp_m53 in H. exact H. }
    exact (root_real w rt (B uh) (B ul) (B rs) (B rse) (B (fsub uh rs)) (B (fsub (fsub uh rs) rse)) (B residual) (B c)
      (bpow radix2 (-1075)) Hw1b Hww Esum Hroot ltac:(lra) Hul ltac:(lra) Hrse Heta H1 H2 H3 H4). }
  assert (Hshw : Rabs (B sh + B sl - w) <= / 1237940039285380274899124224 * w) by (rewrite Esh2; exact Hmain).
  repeat split; try assumption.
  - rewrite Esh2. exact Esh1.
  - rewrite Esh1. change (B root) with rt.
    apply rnd_bound; [apply fmt_pow; lia | ].
    apply Rabs_le_inv in Hmain. apply Rabs_le.
    change (bpow radix2 29) with 536870912 in Hw2. change (bpow radix2 30) with 1073741824.
    assert (/ 1237940039285380274899124224 * w <= 1) by (apply Rle_trans with (/ 1237940039285380274899124224 * 536870912); [apply Rmult_le_compat_l; lra | lra]).
    split; lra.
  - exists w. split; [exact Hww | split; [exact Hw1 | split; [exact Hw2 | exact Hshw]]].
Qed.

(** The pure-real composition of the logarithmic form's error. *)
Lemma log_final (A V0 vh vl eps L q Y ea eta : R) :
  0.0077 <= A -> A = ln V0 -> 0 < V0 ->
  1 <= vh -> Rabs vl <= / 4503599627370496 * vh -> vh + vl = V0 * (1 + eps) -> Rabs eps <= 3.3e-27 ->
  Rabs (L - ln vh) <= / 18446744073709551616 * Rabs (ln vh) ->
  Rabs (q - vl / vh) <= / 9007199254740992 * Rabs (vl / vh) + eta -> 0 <= eta <= 1e-30 ->
  Y = (L + q) * (1 + ea) -> Rabs ea <= 2.5e-32 ->
  Rabs (Y - A) <= / 9223372036854775808 * A.
Proof.
  intros HA EA HV0 Hvh Hvl Hsum Heps HL Hq Heta HY Hea.
  assert (Hvh0 : 0 < vh) by lra.
  set (t := vl / vh).
  assert (Ht : Rabs t <= / 4503599627370496).
  { unfold t. rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq vh) by lra.
    apply Rmult_le_reg_r with vh; [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Ht2 : -1 / 2 <= t <= 1 / 2) by (apply Rabs_le_inv in Ht; split; lra).
  assert (Hvv : vh + vl = vh * (1 + t)) by (unfold t; field; lra).
  assert (H1t : 0 < 1 + t) by lra.
  assert (Hln1 : ln (vh + vl) = ln vh + ln (1 + t)) by (rewrite Hvv; apply ln_mult; lra).
  assert (Hz : Rabs (ln (1 + t) - t) <= t * t) by (apply ln1p_abs; exact Ht2).
  assert (He2 : -1 / 2 <= eps <= 1 / 2) by (apply Rabs_le_inv in Heps; split; lra).
  assert (Hln2 : ln (vh + vl) = A + ln (1 + eps)).
  { rewrite Hsum, EA. rewrite ln_mult; [ring | lra | lra]. }
  assert (Hz2 : Rabs (ln (1 + eps) - eps) <= eps * eps) by (apply ln1p_abs; exact He2).
  assert (Htt : t * t <= 1e-31).
  { assert (Rabs t * Rabs t <= / 4503599627370496 * / 4503599627370496) by (apply Rmult_le_compat; try apply Rabs_pos; exact Ht).
    rewrite <- Rabs_mult in H. rewrite Rabs_pos_eq in H by exact (Rle_0_sqr _). lra. }
  assert (Hee : eps * eps <= 1.1e-53).
  { assert (Rabs eps * Rabs eps <= 3.3e-27 * 3.3e-27) by (apply Rmult_le_compat; try apply Rabs_pos; exact Heps).
    rewrite <- Rabs_mult in H. rewrite Rabs_pos_eq in H by exact (Rle_0_sqr _). lra. }
  apply Rabs_le_inv in Hz. apply Rabs_le_inv in Hz2. pose proof Ht as Ht_abs. apply Rabs_le_inv in Heps. apply Rabs_le_inv in Ht.
  assert (Hlnvh : Rabs (ln vh - A) <= 1e-15).
  { apply Rabs_le. split; lra. }
  assert (Hlnvh_pos : A - 1e-15 <= ln vh <= A + 1e-15) by (apply Rabs_le_inv in Hlnvh; lra).
  assert (HLa : Rabs (L - ln vh) <= 5.5e-20 * A + 1e-33).
  { apply Rle_trans with (1 := HL). rewrite Rabs_pos_eq by lra.
    assert (/ 18446744073709551616 * ln vh <= / 18446744073709551616 * (A + 1e-15)) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hq1 : Rabs (q - t) <= 1e-31 + eta).
  { apply Rle_trans with (1 := Hq). fold t.
    assert (/ 9007199254740992 * Rabs t <= / 9007199254740992 * / 4503599627370496) by (apply Rmult_le_compat_l; [lra | exact Ht_abs]). lra. }
  apply Rabs_le_inv in HLa. apply Rabs_le_inv in Hq1.
  set (E := ln (1 + eps) - (ln (1 + t) - t) + (L - ln vh) + (q - t)).
  assert (Hid : L + q = A + E) by (unfold E; lra).
  assert (HE : Rabs E <= 5.5e-20 * A + 3.4e-27).
  { apply Rabs_le. unfold E. split; lra. }
  assert (Hy : Y - A = E + (L + q) * ea) by (rewrite HY, Hid; ring).
  rewrite Hy.
  assert (HLq : Rabs (L + q) <= 1.001 * A).
  { rewrite Hid. apply Rabs_le_inv in HE. apply Rabs_le. split; lra. }
  assert (Hpr : Rabs ((L + q) * ea) <= (1.001 * A) * 2.5e-32).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  apply Rle_trans with (Rabs E + Rabs ((L + q) * ea)); [apply Rabs_triang | ].
  lra.
Qed.

(** [X + s] against [X + sqrt (X^2 + 1)] when [s] approximates [w], [w^2 = (1 + X^2)(1 + eu)]. *)
Lemma v_near (X eu s w ev vsum : R) :
  0 <= X -> 1 <= w -> w * w = (1 + X * X) * (1 + eu) -> Rabs eu <= 2.5e-32 ->
  Rabs (s - w) <= 8.1e-28 * w -> vsum = (X + s) * (1 + ev) -> Rabs ev <= 2.5e-32 ->
  exists eps, vsum = (X + sqrt (X ^ 2 + 1)) * (1 + eps) /\ Rabs eps <= 1e-27.
Proof.
  intros HX Hw1 Hww Heu Hs Hv Hev.
  assert (Hq : X ^ 2 + 1 = 1 + X * X) by ring.
  set (w0 := sqrt (X ^ 2 + 1)).
  assert (Hw0sq : w0 * w0 = 1 + X * X) by (unfold w0; rewrite Hq; apply sqrt_sqrt; nra).
  assert (Hw01 : 1 <= w0).
  { unfold w0. rewrite Hq. apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; nra]. }
  apply Rabs_le_inv in Heu. destruct Heu as [Heu1 Heu2].
  assert (Hdiff : (w - w0) * (w + w0) = w0 * w0 * eu) by (rewrite Hw0sq; nra).
  assert (Hww0 : Rabs (w - w0) <= 2.5e-32 * w0).
  { assert (Habs : Rabs (w - w0) * (w + w0) <= 2.5e-32 * (w0 * w0)).
    { rewrite <- (Rabs_pos_eq (w + w0)) at 1 by lra. rewrite <- Rabs_mult, Hdiff.
      rewrite Rabs_mult, (Rabs_pos_eq (w0 * w0)) by nra.
      apply Rabs_le_inv in Hev. 
      assert (Rabs eu <= 2.5e-32) by (apply Rabs_le; split; lra).
      nra. }
    apply Rmult_le_reg_r with (w + w0); [lra | ].
    apply Rle_trans with (2.5e-32 * (w0 * w0)); [exact Habs | ].
    assert (0 <= 2.5e-32 * w0) by lra. nra. }
  apply Rabs_le_inv in Hww0. destruct Hww0 as [Hw01' Hw02'].
  apply Rabs_le_inv in Hs. destruct Hs as [Hs1 Hs2].
  assert (Hwle : w <= 1.0000001 * w0) by lra.
  assert (Hsw0 : Rabs (s - w0) <= 8.2e-28 * w0).
  { apply Rabs_le. split; nra. }
  apply Rabs_le_inv in Hsw0. destruct Hsw0 as [Hsw1 Hsw2].
  set (V0 := X + w0).
  assert (HV0 : w0 <= V0) by (unfold V0; lra).
  assert (HV0p : 0 < V0) by lra.
  set (delta := (X + s - V0) / V0).
  assert (Hd : X + s = V0 * (1 + delta)) by (unfold delta; field; lra).
  assert (Hdb : Rabs delta <= 8.2e-28).
  { unfold delta. rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq V0) by lra.
    apply Rmult_le_reg_r with V0; [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
    apply Rabs_le. unfold V0. split; nra. }
  exists (delta + ev + delta * ev). split.
  - rewrite Hv, Hd. ring.
  - apply Rabs_le_inv in Hdb. apply Rabs_le_inv in Hev.
    assert (Rabs (delta * ev) <= 8.2e-28 * 2.5e-32).
    { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; apply Rabs_le; lra. }
    apply Rabs_le_inv in H. apply Rabs_le. split; nra.
Qed.

Lemma bp105 : bpow radix2 (-105) <= 2.5e-32.
Proof. bpow_num. apply Rle_trans with (/ 40000000000000000000000000000000); [apply Rinv_le_contravar; [lra | simpl; lra] | lra]. Qed.

(** The logarithmic form: the double-word is [arcsinh x] to a relative [2^-63]. *)
Theorem asinh_logarithm_fast x : finite x -> bpow radix2 (-7) <= B x -> B x < bpow radix2 28 ->
  exists h l, asinh_logarithm x = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    bpow radix2 (-8) <= B h /\ B h <= bpow radix2 10 /\
    Rabs (B h + B l - arcsinh (B x)) <= bpow radix2 (-63) * arcsinh (B x).
Proof.
  intros Fx L U.
  pose proof (stage_u x Fx L U) as SU.
  unfold asinh_logarithm.
  destruct (two_prod64 x x) as [sq sqe] eqn:E1.
  destruct (two_sum64 asin_one sq) as [h1 l1] eqn:E2.
  destruct (add_f64_64 h1 l1 sqe) as [uh ul] eqn:E3.
  destruct SU as [Fuh [Ful [Dwu [Hu1 [Hu2 [eu [Heu Hsum]]]]]]].
  pose proof bp105 as Hb105.
  assert (Hxx : / 16384 <= B x * B x < 72057594037927936).
  { rewrite bp_m7 in L. rewrite bp28 in U. split.
    - assert (/ 128 * / 128 <= B x * B x) by (apply Rmult_le_compat; lra). lra.
    - assert (B x * B x <= B x * 268435456) by (apply Rmult_le_compat_l; lra). lra. }
  destruct Hxx as [Hxx1 Hxx2].
  apply Rabs_le_inv in Heu. destruct Heu as [Heu1 Heu2].
  assert (Hp1 : (1 + B x * B x) * (- 2.5e-32) <= (1 + B x * B x) * eu) by (apply Rmult_le_compat_l; lra).
  assert (Hp2 : (1 + B x * B x) * eu <= (1 + B x * B x) * 2.5e-32) by (apply Rmult_le_compat_l; lra).
  assert (Hu_lo : 1 <= B uh + B ul) by (rewrite Hsum; lra).
  assert (Hu_hi : B uh + B ul <= bpow radix2 58) by (rewrite Hsum; change (bpow radix2 58) with 288230376151711744; lra).
  pose proof (stage_root uh ul Fuh Ful Dwu Hu1 Hu2 Hu_lo Hu_hi) as SR. cbv zeta in SR.
  destruct (two_prod64 (fsqrt uh) (fsqrt uh)) as [rs rse] eqn:E4.
  match goal with |- context [two_sum64 ?a ?b] => destruct (two_sum64 a b) as [sh sl] eqn:E5 end.
  destruct SR as [Fsh [Fsl [Dws [Hsh30 [w [Hww [Hw1 [Hw2 Hs]]]]]]]].
  (* sh, sl *)
  set (sv := B sh + B sl) in *.
  apply Rabs_le_inv in Hs. destruct Hs as [Hs1 Hs2].
  change (bpow radix2 29) with 536870912 in Hw2.
  assert (Hsvw : sv <= 1.0001 * w /\ 0.9999 * w <= sv).
  { split; [ | ]; lra. }
  destruct Hsvw as [Hsv1 Hsv2].
  assert (Hsl : Rabs (B sl) <= bpow radix2 31).
  { apply Rabs_le_inv in Hsh30. destruct Hsh30 as [Hsh1 Hsh2]. change (bpow radix2 31) with 2147483648. change (bpow radix2 30) with 1073741824 in Hsh1, Hsh2. apply Rabs_le. split; unfold sv in *; lra. }
  assert (Hx1020 : Rabs (B x) <= bpow radix2 1020).
  { rewrite Rabs_pos_eq by (rewrite bp_m7 in L; lra). apply Rle_trans with (bpow radix2 28); [lra | apply bpow_le; lia]. }
  assert (Hsh1020 : Rabs (B sh) <= bpow radix2 1020) by (apply Rle_trans with (bpow radix2 30); [exact Hsh30 | apply bpow_le; lia]).
  pose proof (two_sum_ieee x sh Fx Fsh Hx1020 Hsh1020) as TS2.
  destruct (two_sum64 x sh) as [a b] eqn:E6. cbv beta iota in TS2.
  destruct TS2 as [Fa [Fb [Ea Esab]]].
  assert (Hsh_pos : 1 / 2 <= B sh).
  { rewrite Dws. apply Rle_trans with (bpow radix2 (-1)); [rewrite bp1; lra | apply rndF_ge_bpow; [lia | rewrite bp1; unfold sv in *; lra]]. }
  assert (Ha_lo : 1 / 2 <= B a).
  { rewrite Ea. apply Rle_trans with (bpow radix2 (-1)); [rewrite bp1; lra | apply rndF_ge_bpow; [lia | rewrite bp1; rewrite bp_m7 in L; lra]]. }
  assert (Ha_hi : B a <= bpow radix2 31).
  { rewrite Ea. apply rnd_le_pow; [lia | ]. apply Rabs_le_inv in Hsh30. destruct Hsh30 as [_ Hsh2].
    change (bpow radix2 31) with 2147483648. change (bpow radix2 30) with 1073741824 in Hsh2. rewrite bp28 in U. lra. }
  assert (Dwa : B a = rndF (B a + B b)) by (rewrite Esab; exact Ea).
  assert (Hb_a : Rabs (B b) <= bpow radix2(-52) * Rabs (B a)).
  { apply lo_bound; [ | exact Dwa]. rewrite Rabs_pos_eq by lra.
    apply Rle_trans with (1 / 2); [apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | rewrite bp1; lra] | exact Ha_lo]. }
  assert (Hb_b : Rabs (B b) <= 1).
  { rewrite (Rabs_pos_eq (B a)) in Hb_a by lra. rewrite bp_m52 in Hb_a. change (bpow radix2 31) with 2147483648 in Ha_hi.
    assert (/ 4503599627370496 * B a <= / 4503599627370496 * 2147483648) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Ha1018 : Rabs (B a) <= bpow radix2 1018) by (rewrite Rabs_pos_eq by lra; apply Rle_trans with (bpow radix2 31); [exact Ha_hi | apply bpow_le; lia]).
  assert (Hb1018 : Rabs (B b) <= bpow radix2 1018) by (apply Rle_trans with 1; [exact Hb_b | apply Rle_trans with (bpow radix2 0); [simpl; lra | apply bpow_le; lia]]).
  assert (Hsl1018 : Rabs (B sl) <= bpow radix2 1018) by (apply Rle_trans with (bpow radix2 31); [exact Hsl | apply bpow_le; lia]).
  pose proof (add_f64_ieee a b sl Fa Fb Fsl Dwa Ha1018 Hb1018 Hsl1018) as AF2.
  pose proof (add_f64_normalized_ieee a b sl Fa Fb Fsl Dwa Ha1018 Hb1018 Hsl1018) as AFN2.
  destruct (add_f64_64 a b sl) as [vh vl] eqn:E7. cbv beta iota in AF2, AFN2.
  destruct AF2 as [Fvh [Fvl Bd2]]. destruct AFN2 as [_ [_ Dwv]].
  assert (Hq105 : 2 * bpow radix2 (- prec) ^ 2 = bpow radix2 (-105)).
  { replace (- prec)%Z with (-53)%Z by reflexivity. rewrite bp_m53. bpow_num. simpl. field. }
  rewrite Hq105 in Bd2.
  assert (HP : B a + B b + B sl = B x + sv) by (rewrite Esab; unfold sv; lra).
  assert (HXs : 0 < B x + sv) by (rewrite bp_m7 in L; lra).
  set (P := B a + B b + B sl) in *.
  set (ev := (B vh + B vl - P) / P) in *.
  assert (HP0 : P <> 0) by lra.
  assert (Hev : B vh + B vl = (B x + sv) * (1 + ev)) by (rewrite <- HP; unfold ev; field; exact HP0).
  assert (Hevb : Rabs ev <= 2.5e-32) by (apply Rle_trans with (bpow radix2 (-105)); [exact Bd2 | exact Hb105]).
  assert (Heub : Rabs eu <= 2.5e-32) by (apply Rabs_le; split; lra).
  assert (Hwu : w * w = (1 + B x * B x) * (1 + eu)) by (rewrite Hww, Hsum; reflexivity).
  assert (Hsw : Rabs (sv - w) <= 8.1e-28 * w).
  { apply Rabs_le. split; lra. }
  assert (HX0 : 0 <= B x) by (rewrite bp_m7 in L; lra).
  destruct (v_near (B x) eu sv w ev (B vh + B vl) HX0 Hw1 Hwu Heub Hsw Hev Hevb) as [eps [Hveps Hepsb]].
  set (V0 := B x + sqrt (B x ^ 2 + 1)) in *.
  assert (Hsq1 : 1 <= sqrt (B x ^ 2 + 1)).
  { apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; pose proof (pow2_ge_0 (B x)); lra]. }
  assert (HV0 : 1.0078 <= V0) by (unfold V0; rewrite bp_m7 in L; lra).
  apply Rabs_le_inv in Hepsb. destruct Hepsb as [He1 He2].
  assert (Hp3 : V0 * (- 1e-27) <= V0 * eps) by (apply Rmult_le_compat_l; lra).
  assert (Hvsum : 1 <= B vh + B vl) by (rewrite Hveps; lra).
  assert (Hvh1 : 1 <= B vh).
  { rewrite Dwv. apply Rle_trans with (bpow radix2 0); [simpl; lra | apply rndF_ge_bpow; [lia | simpl; lra]]. }
  assert (Hvl : Rabs (B vl) <= / 4503599627370496 * B vh).
  { pose proof (lo_bound (B vh) (B vl) ltac:(rewrite Rabs_pos_eq by lra; apply Rle_trans with 1; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra] | exact Hvh1]) Dwv) as H.
    rewrite bp_m52, (Rabs_pos_eq (B vh)) in H by lra. exact H. }
  pose proof (lf_ln_fast_value_ok vh Fvh ltac:(lra)) as LF.
  destruct (lf_ln_fast_value vh) as [lh ll] eqn:E8.
  destruct LF as [Flh [Fll [Dwl [Hlh [Hll Hlnerr]]]]].
  (* q = vl / vh *)
  assert (Hvh0 : B vh <> 0) by lra.
  assert (Hqb : Rabs (B vl / B vh) <= bpow radix2 0).
  { rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq (B vh)) by lra.
    apply Rmult_le_reg_r with (B vh); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
    simpl. assert (/ 4503599627370496 * B vh <= 1 * B vh) by (apply Rmult_le_compat_r; lra). lra. }
  destruct (div_abs2 vl vh 0 Fvl Hvh0 Hqb ltac:(lia)) as [Fq [Eq' Bq]].
  set (q := fdiv vl vh) in *.
  assert (Hq1 : Rabs (B q) <= bpow radix2 1018) by (apply Rle_trans with (bpow radix2 0); [exact Bq | apply bpow_le; lia]).
  assert (Hlh1018 : Rabs (B lh) <= bpow radix2 1018) by (apply Rle_trans with 1024; [exact Hlh | change 1024 with (bpow radix2 10); apply bpow_le; lia]).
  assert (Hll1018 : Rabs (B ll) <= bpow radix2 1018) by (apply Rle_trans with 2048; [exact Hll | change 2048 with (bpow radix2 11); apply bpow_le; lia]).
  pose proof (add_f64_ieee lh ll q Flh Fll Fq Dwl Hlh1018 Hll1018 Hq1) as AF3.
  pose proof (add_f64_normalized_ieee lh ll q Flh Fll Fq Dwl Hlh1018 Hll1018 Hq1) as AFN3.
  destruct (add_f64_64 lh ll q) as [yh yl] eqn:E9. cbv beta iota in AF3, AFN3.
  destruct AF3 as [Fyh [Fyl Bd3]]. destruct AFN3 as [_ [_ Dwy]].
  exists yh, yl. split; [reflexivity | ]. split; [exact Fyh | ]. split; [exact Fyl | ]. split; [exact Dwy | ].
  rewrite Hq105 in Bd3.
  (* the true value *)
  set (A := arcsinh (B x)).
  assert (HAeq : A = ln V0) by (unfold A, arcsinh, V0; reflexivity).
  assert (HAlo : 0.0077 <= A).
  { unfold A. rewrite bp_m7 in L.
    apply Rle_trans with (arcsinh (/ 128)).
    - pose proof (arcsinh_ge_cubic (/ 128) ltac:(split; lra)). lra.
    - apply arcsinh_le. lra. }
  assert (HV0hi : V0 <= 536870913).
  { unfold V0. rewrite bp28 in U.
    assert (sqrt (B x ^ 2 + 1) <= 268435457).
    { apply Rle_trans with (sqrt (268435457 * 268435457)); [apply sqrt_le_1_alt; nra | rewrite sqrt_square by lra; lra]. }
    lra. }
  assert (HAhi : A <= 21).
  { rewrite HAeq. apply Rle_trans with (ln 536870913).
    - apply ln_mono; lra.
    - interval with (i_prec 60). }
  set (LL := B lh + B ll) in *.
  assert (Hvh_lo : 1.007 <= B vh).
  { apply Rabs_le_inv in Hvl. destruct Hvl as [Hvl1 Hvl2]. lra. }
  assert (Hlnvh : 0.0069 <= ln (B vh)).
  { apply Rle_trans with (ln (1 + 0.007)); [pose proof (ln1p_ge 0.007 ltac:(split; lra)); lra | apply ln_mono; lra]. }
  assert (Hq0 : Rabs (B q) <= 3e-16).
  { rewrite Eq'. pose proof (rnd_err (B vl / B vh)) as R. rewrite bp_m53 in R.
    assert (Hvv : Rabs (B vl / B vh) <= / 4503599627370496).
    { rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq (B vh)) by lra.
      apply Rmult_le_reg_r with (B vh); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r. lra. }
    assert (Heta : bpow radix2 (-1075) <= 1e-30).
    { apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | bpow_num; apply Rle_trans with (/ 1000000000000000000000000000000); [apply Rinv_le_contravar; [lra | simpl; lra] | lra]]. }
    assert (/ 9007199254740992 * Rabs (B vl / B vh) <= / 9007199254740992 * / 4503599627370496) by (apply Rmult_le_compat_l; lra).
    apply Rle_trans with (Rabs (rndF (B vl / B vh) - B vl / B vh) + Rabs (B vl / B vh)); [apply rabs_sub_r | ]. lra. }
  assert (HLL : Rabs (LL - ln (B vh)) <= / 18446744073709551616 * Rabs (ln (B vh))).
  { assert (H264 : 2 ^ 64 = 18446744073709551616) by (simpl; ring).
    rewrite H264 in Hlnerr. exact Hlnerr. }
  assert (Hvh_hi : B vh <= 1073741824).
  { apply Rabs_le_inv in Hvl. destruct Hvl as [Hvl1 Hvl2]. assert (Hp4 : V0 * eps <= V0 * 1e-27) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hlnhi : ln (B vh) <= 21).
  { apply Rle_trans with (ln 1073741824); [apply ln_mono; lra | interval with (i_prec 60)]. }
  assert (HLLp : 0.006 <= LL <= 21.001).
  { rewrite (Rabs_pos_eq (ln (B vh))) in HLL by lra. apply Rabs_le_inv in HLL. destruct HLL as [HL1 HL2].
    assert (/ 18446744073709551616 * ln (B vh) <= / 18446744073709551616 * 21) by (apply Rmult_le_compat_l; lra). lra. }
  destruct HLLp as [HLL1 HLL2].
  apply Rabs_le_inv in Hq0. destruct Hq0 as [Hq01 Hq02].
  assert (HS : 0.0059 <= LL + B q) by lra.
  set (S := LL + B q) in *.
  set (ea := (B yh + B yl - S) / S).
  assert (HY : B yh + B yl = S * (1 + ea)) by (unfold ea; field; lra).
  assert (Heab : Rabs ea <= 2.5e-32).
  { unfold ea. apply Rle_trans with (bpow radix2 (-105)); [ | exact Hb105]. exact Bd3. }
  assert (Hepsabs : Rabs eps <= 3.3e-27) by (apply Rabs_le; split; lra).
  assert (Hq : Rabs (B q - B vl / B vh) <= / 9007199254740992 * Rabs (B vl / B vh) + bpow radix2 (-1075)).
  { rewrite Eq'. pose proof (rnd_err (B vl / B vh)) as R. rewrite bp_m53 in R. exact R. }
  assert (Heta : 0 <= bpow radix2 (-1075) <= 1e-30).
  { split; [apply bpow_ge_0 | ]. apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | bpow_num; apply Rle_trans with (/ 1000000000000000000000000000000); [apply Rinv_le_contravar; [lra | simpl; lra] | lra]]. }
  pose proof (log_final A V0 (B vh) (B vl) eps LL (B q) (B yh + B yl) ea (bpow radix2 (-1075)) HAlo HAeq ltac:(lra) Hvh1 Hvl Hveps Hepsabs HLL Hq Heta HY Heab) as FIN.
  assert (Hb63 : bpow radix2 (-63) = / 9223372036854775808) by (bpow_num; reflexivity).
  split; [ | split; [ | rewrite Hb63; exact FIN]].
  - rewrite Dwy. apply rndF_ge_bpow; [lia | ].
    apply Rabs_le_inv in FIN. destruct FIN as [F1 F2].
    assert (bpow radix2 (-8) = / 256) by (bpow_num; reflexivity). 
    assert (/ 9223372036854775808 * A <= / 9223372036854775808 * 21) by (apply Rmult_le_compat_l; lra). lra.
  - rewrite Dwy. apply rnd_le_pow; [lia | ].
    apply Rabs_le_inv in FIN. destruct FIN as [F1 F2].
    assert (bpow radix2 10 = 1024) by (bpow_num; reflexivity).
    assert (/ 9223372036854775808 * A <= / 9223372036854775808 * 21) by (apply Rmult_le_compat_l; lra). lra.
Qed.
