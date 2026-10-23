(** asin's complement reduction: the double-word [z = s + s_lo] is [sqrt ((1 - x)/2)]
    to [2^-103] relatively. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Flocq Require Import Mult_error.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft IEEE64Sqrt Grid Encodings.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel.
Require asin_sqrt.
Open Scope R_scope.

(** The certificate [formal/asin/sqrt.g], at its real variable [w]. *)
Lemma sqrt_certificate w : /2^27 <= w <= 0.3827 ->
  let s := rn w in
  let ph := rn (s * s) in
  let pl := s * s - ph in
  let rr1 := rn (w * w - ph) in
  let r2 := rn (rr1 - pl) in
  let sl := rn (r2 / (Float1 2 * s)) in
  Rabs ((s + sl - w) / w) <= /2^103.
Proof.
  intros W s ph pl rr1 r2 sl.
  assert (G : BND ((s + sl - w) / w) (makepairF (Float2 (-1) (-103)) (Float2 1 (-103)))).
  { subst s ph pl rr1 r2 sl. gappa_goal (asin_sqrt.l1 w). }
  apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all.
  apply Rabs_le. lra.
Qed.


(** The constants. *)
Lemma one_val : B asin_one = 1 /\ finite asin_one.
Proof.
  split.
  - unfold asin_one, aw. rewrite (bits_val 0x3ff0000000000000 false 4503599627370496%positive 52 eq_refl).
    simpl. field.
  - exact (bits_finite 0x3ff0000000000000 false 4503599627370496%positive (-52) eq_refl).
Qed.

Lemma half_val : B asin_half = / 2 /\ finite asin_half.
Proof.
  split.
  - unfold asin_half, aw. rewrite (bits_val 0x3fe0000000000000 false 4503599627370496%positive 53 eq_refl).
    simpl. field.
  - exact (bits_finite 0x3fe0000000000000 false 4503599627370496%positive (-53) eq_refl).
Qed.

Lemma two_val : B asin_two = 2 /\ finite asin_two.
Proof.
  split.
  - unfold asin_two, aw. rewrite (bits_val 0x4000000000000000 false 4503599627370496%positive 51 eq_refl).
    simpl. field.
  - exact (bits_finite 0x4000000000000000 false 4503599627370496%positive (-51) eq_refl).
Qed.

Lemma p53 : 2 ^ 53 = 9007199254740992.
Proof. simpl. ring. Qed.
Definition SPLIT_R : R := 6369051672525772 / 2 ^ 53.
Definition SPLIT_UP_R : R := 6369051672525773 / 2 ^ 53.

Lemma split_val : B asin_split = SPLIT_R /\ finite asin_split.
Proof.
  split.
  - unfold asin_split, aw. rewrite (bits_val 0x3fe6a09e667f3bcc false 6369051672525772%positive 53 eq_refl).
    unfold SPLIT_R. simpl. reflexivity.
  - exact (bits_finite 0x3fe6a09e667f3bcc false 6369051672525772%positive (-53) eq_refl).
Qed.

(** An argument above [SPLIT] takes the complement branch. *)
Lemma complement_branch x : finite x -> SPLIT_UP_R <= B x -> asin_le x asin_split = false.
Proof.
  intros Fx H. destruct split_val as [V F].
  unfold asin_le, asin_cmp. rewrite (Bcompare_correct 53 1024 x asin_split Fx F), V.
  rewrite Rcompare_Gt; [reflexivity | ].
  unfold SPLIT_R, SPLIT_UP_R in *. rewrite p53 in *. lra.
Qed.

Lemma bp53 : bpow radix2 (-53) = / 9007199254740992.
Proof.
  change (-53)%Z with (Zneg 53). rewrite bpow_neg. f_equal.
Qed.

Lemma bp54 : bpow radix2 (-54) = / 18014398509481984.
Proof.
  change (-54)%Z with (Zneg 54). rewrite bpow_neg. f_equal.
Qed.

(** An argument in [[1/2, 1 - 2^-53]] is [k 2^-53] for an integer [k]. *)
Lemma grid53 x : finite x -> / 2 <= B x -> B x <= 1 - / 9007199254740992 ->
  exists k : Z, B x = IZR k * bpow radix2 (-53) /\ (4503599627370496 <= k <= 9007199254740991)%Z.
Proof.
  intros Fx L U.
  assert (H1 : bpow radix2 (-1) = / 2).
  { change (-1)%Z with (Zneg 1). rewrite bpow_neg. reflexivity. }
  assert (Hr : bpow radix2 (-1) <= Rabs (B x)) by (rewrite Rabs_pos_eq by lra; rewrite H1; exact L).
  destruct (grid_fmt_bound (FLT_exp emin prec) (-1) (B x)
    ltac:(intros e; unfold FLT_exp, emin, prec; lia) (B_fmt x) (or_intror Hr)) as [k Hk].
  replace (-1 - 52)%Z with (-53)%Z in Hk by reflexivity.
  exists k. split; [exact Hk | ].
  rewrite Hk, bp53 in L, U.
  split; apply le_IZR.
  - change (IZR 4503599627370496) with 4503599627370496. lra.
  - change (IZR 9007199254740991) with 9007199254740991. lra.
Qed.

Lemma bnd_one v : Rabs v <= 1 -> bnd 1 0 v.
Proof. intros H. unfold bnd. replace (IZR 1 * bpow radix2 0) with 1 by (simpl; ring). exact H. Qed.

(** [u = (1 - x)/2] is computed exactly. *)
Lemma u_exact x : finite x -> / 2 <= B x -> B x <= 1 - / 9007199254740992 ->
  finite (fmul (fsub asin_one x) asin_half) /\
  B (fmul (fsub asin_one x) asin_half) = (1 - B x) / 2.
Proof.
  intros Fx L U.
  destruct one_val as [V1 F1]. destruct half_val as [VH FH].
  destruct (grid53 x Fx L U) as [k [Hk [K1 K2]]].
  rewrite bp53 in Hk.
  (* 1 - x = (2^53 - k) 2^-53, exactly representable. *)
  assert (Hd : 1 - B x = IZR (9007199254740992 - k) * bpow radix2 (-53)).
  { rewrite bp53, minus_IZR. change (IZR 9007199254740992) with 9007199254740992. rewrite Hk. field. }
  assert (Gd : fmtF (1 - B x)).
  { rewrite Hd. apply bnd_fmt; lia. }
  assert (Bd : bnd 1 0 (B asin_one - B x)).
  { apply bnd_one. rewrite V1. apply Rabs_le. rewrite Hk. lra. }
  destruct (fsub_bnd 1 0 asin_one x F1 Fx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [Fd [Ed Bd']].
  assert (Ed' : B (fsub asin_one x) = 1 - B x).
  { rewrite Ed, V1. apply round_generic; [exact _ | ]. exact Gd. }
  (* halving *)
  assert (Gh : fmtF ((1 - B x) / 2)).
  { replace ((1 - B x) / 2) with (IZR (9007199254740992 - k) * bpow radix2 (-54)).
    - apply bnd_fmt; lia.
    - rewrite bp54, Hd, bp53. field. }
  assert (Bh : bnd 1 0 (B (fsub asin_one x) * B asin_half)).
  { apply bnd_one. rewrite Ed', VH. apply Rabs_le. rewrite Hk. lra. }
  destruct (fmul_bnd 1 0 (fsub asin_one x) asin_half Fd FH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bh) as [Fu [Eu _]].
  split; [exact Fu | ].
  rewrite Eu, Ed', VH. replace ((1 - B x) * / 2) with ((1 - B x) / 2) by field.
  apply round_generic; [exact _ | exact Gh].
Qed.

Lemma bnd0 k v : Rabs v <= IZR k -> bnd k 0 v.
Proof. intros H. unfold bnd. replace (bpow radix2 0) with 1 by reflexivity. rewrite Rmult_1_r. exact H. Qed.

Lemma bnd_p k e v : Rabs v <= IZR k * bpow radix2 e -> bnd k e v.
Proof. intros H. exact H. Qed.

Lemma f12 : Float1 2 = 2.
Proof. unfold Float1. simpl. ring. Qed.

(** [w = sqrt ((1 - x)/2)] and its range. *)
Lemma w_facts x : SPLIT_UP_R <= B x -> B x <= 1 - / 9007199254740992 ->
  let w := sqrt ((1 - B x) / 2) in
  / 134217728 <= w <= 0.3827 /\ w * w = (1 - B x) / 2 /\ 0 < w.
Proof.
  intros L U w. unfold SPLIT_UP_R in L. rewrite p53 in L.
  assert (Hu : 0 <= (1 - B x) / 2) by lra.
  assert (Hww : w * w = (1 - B x) / 2) by (unfold w; apply sqrt_sqrt; exact Hu).
  assert (Hw0 : 0 <= w) by apply sqrt_pos.
  assert (Hlo : / 134217728 <= w).
  { apply Rnot_lt_le; intros H. nra. }
  assert (Hhi : w <= 0.3827).
  { apply Rnot_lt_le; intros H. nra. }
  repeat split; try assumption. lra.
Qed.

Lemma div_small a b c : 0 < b -> Rabs a <= c * b -> Rabs (a / b) <= c.
Proof.
  intros Hb H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra.
  rewrite (Rabs_pos_eq b) by lra.
  apply Rmult_le_reg_r with b; [exact Hb | ]. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma fmt_bpow e : (-1074 <= e)%Z -> fmtF (bpow radix2 e).
Proof. intros H. apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. Qed.

Lemma rnd_bpow e : (-1074 <= e)%Z -> rndF (bpow radix2 e) = bpow radix2 e.
Proof. intros H. apply round_generic; [exact _ | apply fmt_bpow; exact H]. Qed.

(** A binary64 in [[2^-27, 1/2]], doubled: exact. *)
Lemma double_exact s : finite s -> bpow radix2 (-27) <= B s -> B s <= bpow radix2 (-1) ->
  finite (fmul asin_two s) /\ B (fmul asin_two s) = 2 * B s.
Proof.
  intros Fs L U. destruct two_val as [V2 F2].
  assert (Gs : fmtF (B s * bpow radix2 1)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (-26 <= mag radix2 (B s))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq.
      - replace (-26 - 1)%Z with (-27)%Z by reflexivity. exact L.
      - pose proof (bpow_gt_0 radix2 (-27)). lra. }
    unfold emin, prec. lia. }
  assert (E2 : B asin_two * B s = B s * bpow radix2 1).
  { rewrite V2. change (bpow radix2 1) with 2. ring. }
  assert (Pb : bpow radix2 (-1) = / 2) by (change (-1)%Z with (Zneg 1); rewrite bpow_neg; reflexivity).
  assert (Pc : 0 < bpow radix2 (-27)) by apply bpow_gt_0.
  assert (Bd : bnd 1 0 (B asin_two * B s)).
  { apply bnd0. rewrite V2. apply Rabs_le. change (IZR 1) with 1. rewrite Pb in U. lra. }
  destruct (fmul_bnd 1 0 asin_two s F2 Fs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [F [E _]].
  split; [exact F | ].
  rewrite E, E2, round_generic by (try exact _; exact Gs).
  change (bpow radix2 1) with 2. ring.
Qed.

Lemma bp27 : bpow radix2 (-27) = / 134217728.
Proof. change (-27)%Z with (Zneg 27). rewrite bpow_neg. f_equal. Qed.

Lemma bp27p : bpow radix2 27 = 134217728.
Proof. change 27%Z with (Zpos 27). rewrite bpow_pos. vm_compute. reflexivity. Qed.

Lemma bp1 : bpow radix2 (-1) = / 2.
Proof. change (-1)%Z with (Zneg 1). rewrite bpow_neg. reflexivity. Qed.

Lemma bp2 : bpow radix2 (-2) = / 4.
Proof. change (-2)%Z with (Zneg 2). rewrite bpow_neg. reflexivity. Qed.

(** The complement's reduction: the double-word [z] is [sqrt ((1 - x)/2)] to
    [2^-103] relatively. *)
Theorem reduced_complement x : finite x -> SPLIT_UP_R <= B x -> B x <= 1 - / 9007199254740992 ->
  exists zh zl, asin_reduced x = (false, (zh, zl)) /\ finite zh /\ finite zl /\
    B zh = rndF (B zh + B zl) /\ on_grid (-211) (B zl) /\
    Rabs (B zh + B zl - sqrt ((1 - B x) / 2)) <= / 2 ^ 103 * sqrt ((1 - B x) / 2).
Proof.
  intros Fx L U.
  assert (Lh : / 2 <= B x) by (unfold SPLIT_UP_R in L; rewrite p53 in L; lra).
  destruct (u_exact x Fx Lh U) as [Fu Eu].
  destruct (w_facts x L U) as [[W1 W2] [Ww W0]]. set (w := sqrt ((1 - B x) / 2)) in *.
  set (u := fmul (fsub asin_one x) asin_half) in *.
  unfold asin_reduced. rewrite (complement_branch x Fx L). fold u.
  destruct (sqrt_ieee u) as [Es Fs'].
  set (s := fsqrt u) in *.
  assert (Fs : finite s) by (apply (proj2 Fs'); split; [exact Fu | rewrite Eu; lra]).
  assert (Esw : B s = rn w).
  { rewrite Es, Eu. replace ((1 - B x) / 2) with (w * w) by (symmetry; exact Ww).
    rewrite sqrt_square by lra. reflexivity. }
  set (S := B s) in *.
  (* S in [2^-27, 1/2] *)
  assert (SL : bpow radix2 (-27) <= S).
  { rewrite Esw. change (rn w) with (rndF w). apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | ].
    rewrite bp27. lra. }
  assert (SU : S <= bpow radix2 (-1)).
  { rewrite Esw. change (rn w) with (rndF w). apply round_le_generic; [exact _ | exact _ | apply fmt_bpow; lia | ].
    rewrite bp1. lra. }
  rewrite bp27 in SL. rewrite bp1 in SU.
  assert (SA : Rabs S <= bpow radix2 (-1)) by (rewrite Rabs_pos_eq by lra; rewrite bp1; exact SU).
  (* s * s *)
  assert (Hss : bpow radix2 (-54) <= S * S).
  { rewrite bp54. assert (Hc : / 134217728 * / 134217728 <= S * S) by (apply Rmult_le_compat; lra).
    assert (Hn : / 134217728 * / 134217728 = / 18014398509481984) by (field). lra. }
  assert (Dom : bpow radix2 (-969) <= Rabs (B s * B s)).
  { apply Rle_trans with (bpow radix2 (-54)); [apply bpow_le; lia | ].
    rewrite Rabs_pos_eq; [exact Hss | change (B s) with S; nra]. }
  assert (TP := two_prod_ieee (-1) (-1) s s Fs Fs SA SA ltac:(lia) ltac:(lia) ltac:(lia) (or_intror Dom)).
  destruct (two_prod64 s s) as [sq se] eqn:Ep. cbv beta iota in TP.
  destruct TP as [Fsq [Fse [Esq Esum]]].
  assert (SSnn : 0 <= S * S) by (apply Rmult_le_pos; lra).
  assert (SSle : S * S <= / 4).
  { assert (S * S <= / 2 * / 2) by (apply Rmult_le_compat; lra). lra. }
  assert (Hsq0 : 0 <= B sq).
  { rewrite Esq. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ].
    change (B s) with S. exact SSnn. }
  assert (Hsq1 : B sq <= / 4).
  { rewrite Esq. apply round_le_generic; [exact _ | exact _ | | ].
    - rewrite <- bp2. apply fmt_bpow. lia.
    - change (B s) with S. exact SSle. }
  assert (Hse : Rabs (B se) <= 1).
  { apply Rabs_le. change (B s) with S in Esum. lra. }
  (* u - sq *)
  assert (L2 : 0.7071 <= B x) by (unfold SPLIT_UP_R in L; rewrite p53 in L; lra).
  assert (Bu : B u = w * w) by (rewrite Eu; lra).
  assert (Hb1 : bnd 1 0 (B u - B sq)).
  { apply bnd0. apply Rabs_le. change (IZR 1) with 1. rewrite Eu. lra. }
  destruct (fsub_bnd 1 0 u sq Fu Fsq ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb1) as [Frr1 [Err1 Brr1]].
  assert (Brr1' : Rabs (B (fsub u sq)) <= 1).
  { unfold bnd in Brr1. replace (IZR 1 * bpow radix2 0) with 1 in Brr1 by (simpl; ring). exact Brr1. }
  (* rr1 - se *)
  assert (Hb2 : bnd 2 0 (B (fsub u sq) - B se)).
  { apply bnd0. apply Rabs_le. change (IZR 2) with 2.
    apply Rabs_le_inv in Brr1'. apply Rabs_le_inv in Hse. lra. }
  destruct (fsub_bnd 2 0 (fsub u sq) se Frr1 Fse ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb2) as [Fr2 [Er2 Br2]].
  assert (Br2' : Rabs (B (fsub (fsub u sq) se)) <= 2).
  { unfold bnd in Br2. replace (IZR 2 * bpow radix2 0) with 2 in Br2 by (simpl; ring). exact Br2. }
  (* 2 s *)
  destruct (double_exact s Fs ltac:(change (B s) with S; rewrite bp27; lra) ltac:(change (B s) with S; rewrite bp1; lra)) as [Fs2 Es2].
  change (B s) with S in Es2.
  (* r2 / (2 s) *)
  assert (Hs2 : / 67108864 <= B (fmul asin_two s)) by (rewrite Es2; lra).
  assert (Hq : bnd 1 27 (B (fsub (fsub u sq) se) / B (fmul asin_two s))).
  { apply bnd_p. rewrite bp27p. change (IZR 1) with 1.
    apply div_small; [lra | ]. lra. }
  destruct (fdiv_bnd 1 27 (fsub (fsub u sq) se) (fmul asin_two s) Fr2 ltac:(lra) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hq) as [Fsl [Esl Bsl]].
  (* z = s + sl *)
  assert (SLa : Rabs (B (fdiv (fsub (fsub u sq) se) (fmul asin_two s))) <= bpow radix2 1020).
  { unfold bnd in Bsl. apply Rle_trans with (IZR 1 * bpow radix2 27); [exact Bsl | ].
    change (IZR 1) with 1. rewrite Rmult_1_l. apply bpow_le. lia. }
  assert (SB : Rabs S <= bpow radix2 1020).
  { apply Rle_trans with (bpow radix2 (-1)); [exact SA | apply bpow_le; lia]. }
  assert (TS := two_sum_ieee s (fdiv (fsub (fsub u sq) se) (fmul asin_two s)) Fs Fsl SB SLa).
  destruct (two_sum64 s (fdiv (fsub (fsub u sq) se) (fmul asin_two s))) as [zh zl] eqn:Ez.
  cbv beta iota in TS. destruct TS as [Fzh [Fzl [Ezh Ezsum]]].
  (* [zl] is a multiple of [2^-211]: [s] is a multiple of [2^-79], [u - s^2] of
     [2^-158], and a nonzero [s_lo] is at least [2^-158] in magnitude. *)
  assert (Hgrid : on_grid (-211) (B zl)).
  { pose proof Esq as Esq2. pose proof Esum as Esum2. change (B s) with S in Esq2, Esum2.
    assert (Gs : on_grid (-79) S).
    { assert (Hr : bpow radix2 (-27) <= Rabs (B s)) by (change (B s) with S; rewrite Rabs_pos_eq by lra; rewrite bp27; exact SL).
      destruct (grid_fmt_bound (FLT_exp emin prec) (-27) (B s) ltac:(intros e; unfold FLT_exp, emin, prec; lia) (B_fmt s)
        (or_intror Hr)) as [k Hk].
      exists k. replace (-79)%Z with (-27 - 52)%Z by reflexivity. exact Hk. }
    assert (Gu : on_grid (-106) (B u)).
    { assert (Hr : bpow radix2 (-54) <= Rabs (B u)) by (rewrite Eu, Rabs_pos_eq by lra; rewrite bp54; lra).
      destruct (grid_fmt_bound (FLT_exp emin prec) (-54) (B u) ltac:(intros e; unfold FLT_exp, emin, prec; lia) (B_fmt u)
        (or_intror Hr)) as [k Hk].
      exists k. replace (-106)%Z with (-54 - 52)%Z by reflexivity. exact Hk. }
    assert (Gss : on_grid (-158) (S * S)).
    { replace (-158)%Z with (-79 + -79)%Z by reflexivity. exact (grid_mult _ _ _ _ Gs Gs). }
    assert (Gsq : on_grid (-158) (B sq)) by (rewrite Esq2; exact (grid_round _ _ _ _ Gss)).
    assert (Gse : on_grid (-158) (B se)).
    { replace (B se) with (S * S - B sq) by lra. exact (grid_minus _ _ _ Gss Gsq). }
    assert (Gu' : on_grid (-158) (B u)) by (apply (grid_le (-106)); [lia | exact Gu]).
    assert (Gr1 : on_grid (-158) (B (fsub u sq))).
    { rewrite Err1. exact (grid_round _ _ _ _ (grid_minus _ _ _ Gu' Gsq)). }
    assert (Gr2 : on_grid (-158) (B (fsub (fsub u sq) se))).
    { rewrite Er2. exact (grid_round _ _ _ _ (grid_minus _ _ _ Gr1 Gse)). }
    assert (Gsl : on_grid (-210) (B (fdiv (fsub (fsub u sq) se) (fmul asin_two s)))).
    { rewrite Esl. rewrite Es2.
      destruct (Req_dec (B (fsub (fsub u sq) se)) 0) as [Z0 | NZ].
      - rewrite Z0. unfold Rdiv. rewrite Rmult_0_l. rewrite round_0 by exact _. apply grid_0.
      - pose proof (grid_nonzero _ _ Gr2 NZ) as Hr.
        assert (Hqq : bpow radix2 (-158) <= Rabs (B (fsub (fsub u sq) se) / (2 * S))).
        { unfold Rdiv. rewrite Rabs_mult, (Rabs_Rinv (2 * S)) by lra. rewrite (Rabs_pos_eq (2 * S)) by lra.
          assert (Hi : / 1 <= / (2 * S)) by (apply Rinv_le_contravar; lra). rewrite Rinv_1 in Hi.
          pose proof (Rabs_pos (B (fsub (fsub u sq) se))). nra. }
        assert (Hr2 : bpow radix2 (-158) <= Rabs (rn (B (fsub (fsub u sq) se) / (2 * S)))).
        { rewrite <- round_NE_abs by exact _. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | exact Hqq]. }
        destruct (grid_fmt_bound (FLT_exp emin prec) (-158)
          (rn (B (fsub (fsub u sq) se) / (2 * S)))
          ltac:(intros e; unfold FLT_exp, emin, prec; lia) (generic_format_round _ _ _ _)
          (or_intror Hr2)) as [k Hk].
        exists k. replace (-210)%Z with (-158 - 52)%Z by reflexivity. exact Hk. }
    assert (Gsum : on_grid (-210) (B s + B (fdiv (fsub (fsub u sq) se) (fmul asin_two s)))).
    { apply grid_plus; [apply (grid_le (-79)); [lia | exact Gs] | exact Gsl]. }
    assert (Gzh : on_grid (-210) (B zh)) by (rewrite Ezh; exact (grid_round _ _ _ _ Gsum)).
    assert (Hzl : B zl = (B s + B (fdiv (fsub (fsub u sq) se) (fmul asin_two s))) - B zh) by lra.
    apply (grid_le (-210)); [lia | ]. rewrite Hzl. exact (grid_minus _ _ _ Gsum Gzh). }
  assert (Hround : B zh = rndF (B zh + B zl)) by (rewrite Ezsum; exact Ezh).
  exists zh, zl. cbv beta iota zeta. repeat split; try reflexivity; try assumption.
  (* the certificate *)
  assert (W1' : / 2 ^ 27 <= w) by (assert (2 ^ 27 = 134217728) by (simpl; ring); rewrite H; exact W1).
  pose proof (sqrt_certificate w (conj W1' W2)) as C. cbv zeta in C. rewrite f12 in C.
  change (B s) with S in Esq, Esum. rewrite Esw in Esq, Esum, Es2.
  assert (Hse' : B se = rn w * rn w - B sq) by lra.
  assert (Hx : B zh + B zl = rn w + rn (rn (rn (w * w - rn (rn w * rn w)) - (rn w * rn w - rn (rn w * rn w))) / (2 * rn w))).
  { rewrite Ezsum. change (B s) with S. rewrite Esw, Esl, Er2, Err1, Es2, Bu, Hse', Esq. reflexivity. }
  assert (Hy : B zh + B zl - w = ((B zh + B zl - w) / w) * w) by (field; lra).
  rewrite Hy. rewrite Rabs_mult, (Rabs_pos_eq w) by lra.
  apply Rmult_le_compat_r; [lra | ].
  rewrite Hx. exact C.
Qed.
