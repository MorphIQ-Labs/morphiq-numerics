(** The double-word additions' results are double-word numbers: the leading
    word is the rounded sum of the two. [add_f64] by the library's
    [add_f64_dw]; [add64] when the second operand's leading word stays below
    [99/100] of the first's and both low words are below [2^-52] of it, by
    following the algorithm's magnitudes, since its last step is a [Fast2Sum]
    with [|w| <= |vh|], hence exact. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingCore.
Require Import Ln1pLemmas.
Open Scope R_scope.

Theorem add_f64_normalized_ieee xh xl y :
  finite xh -> finite xl -> finite y -> B xh = rndF (B xh + B xl) ->
  Rabs (B xh) <= bpow radix2 1018 -> Rabs (B xl) <= bpow radix2 1018 -> Rabs (B y) <= bpow radix2 1018 ->
  let '(zh, zl) := add_f64_64 xh xl y in
  finite zh /\ finite zl /\ B zh = rndF (B zh + B zl).
Proof.
  intros Fh Fl Fy E Bh Bl By.
  assert (U : forall v, Rabs v <= bpow radix2 1018 -> bnd 1 1018 v) by (intros v Hv; unfold bnd; lra).
  destruct (add_f64_64_ok 1 1018 xh xl y Fh Fl Fy (U _ Bh) (U _ Bl) (U _ By)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl Ez]].
  pose proof (add_f64_dw (B xh) (B xl) (B y) (B_fmt xh) (B_fmt xl) (B_fmt y) E) as D.
  rewrite <- Ez in D.
  destruct (add_f64_64 xh xl y) as [zh zl]. cbn [fst snd] in *.
  repeat split; try assumption.
Qed.

Lemma pow_room (k n : Z) : (0 <= k <= 8)%Z -> (4 <= n)%Z -> (k < 2 ^ n)%Z.
Proof.
  intros Hk Hn. apply Z.lt_le_trans with (2 ^ 4)%Z; [simpl; lia | apply Z.pow_le_mono_r; lia].
Qed.

Lemma bnd_sum k1 k2 e x y : bnd k1 e x -> bnd k2 e y -> bnd (k1 + k2) e (x + y).
Proof. exact (bnd_plus k1 k2 e x y). Qed.

Lemma bnd_lift k k' e e' v : bnd k e v -> (e' <= e)%Z -> (IZR k * bpow radix2 e <= IZR k' * bpow radix2 e') ->
  bnd k' e' v.
Proof. unfold bnd. intros H _ L. lra. Qed.

Lemma rnd_rel_f x : bpow radix2 (-1022) <= Rabs x -> Rabs (rndF x - x) <= bpow radix2 (-53) * Rabs x.
Proof. intros H. exact (rnd_rel x H). Qed.

Theorem add64_normalized xh xl yh yl :
  finite xh -> finite xl -> finite yh -> finite yl ->
  bpow radix2 (-900) <= B xh -> B xh <= bpow radix2 900 ->
  Rabs (B xl) <= bpow radix2 (-52) * B xh -> Rabs (B yl) <= bpow radix2 (-52) * B xh ->
  Rabs (B yh) <= 99 / 100 * B xh ->
  let '(zh, zl) := add64 xh xl yh yl in
  finite zh /\ finite zl /\ B zh = rndF (B zh + B zl).
Proof.
  intros Fxh Fxl Fyh Fyl L U Hxl Hyl Hy.
  assert (Hx0 : 0 < B xh) by (apply Rlt_le_trans with (bpow radix2 (-900)); [apply bpow_gt_0 | exact L]).
  destruct (mag radix2 (B xh)) as [e0 He].
  specialize (He (Rgt_not_eq _ _ Hx0)). rewrite (Rabs_pos_eq (B xh)) in He by lra. destruct He as [He1 He2].
  assert (E1 : (e0 - 1 <= 900)%Z).
  { destruct (Z_le_gt_dec (e0 - 1) 900) as [c | c]; [exact c | exfalso].
    assert (bpow radix2 900 < bpow radix2 (e0 - 1)) by (apply bpow_lt; lia). lra. }
  assert (E2 : (-899 <= e0)%Z).
  { destruct (Z_le_gt_dec (-899) e0) as [c | c]; [exact c | exfalso].
    assert (bpow radix2 e0 <= bpow radix2 (-900)) by (apply bpow_le; lia). lra. }
  set (X := bpow radix2 e0) in *.
  assert (HX : X = 2 * bpow radix2 (e0 - 1)).
  { unfold X. replace e0 with ((e0 - 1) + 1)%Z at 1 by ring. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (HXp : 0 < bpow radix2 (e0 - 1)) by apply bpow_gt_0.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by (bpow_num; reflexivity).
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  assert (Hxl' : Rabs (B xl) <= bpow radix2 (-52) * X).
  { apply Rle_trans with (bpow radix2 (-52) * B xh); [exact Hxl | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]]. }
  assert (Hyl' : Rabs (B yl) <= bpow radix2 (-52) * X).
  { apply Rle_trans with (bpow radix2 (-52) * B xh); [exact Hyl | apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]]. }
  assert (Hyh : Rabs (B yh) <= X) by lra.
  assert (HXb : X <= bpow radix2 901) by (unfold X; apply bpow_le; lia).
  assert (H901 : bpow radix2 901 <= bpow radix2 1020) by (apply bpow_le; lia).
  assert (H900 : bpow radix2 900 <= bpow radix2 1020) by (apply bpow_le; lia).
  assert (H901e : bpow radix2 901 = 2 * bpow radix2 900).
  { replace 901%Z with (900 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (A1 : Rabs (B xh) <= bpow radix2 1020) by (rewrite Rabs_pos_eq by lra; lra).
  assert (A2 : Rabs (B yh) <= bpow radix2 1020) by lra.
  pose proof (two_sum_ieee xh yh Fxh Fyh A1 A2) as TS1.
  destruct (two_sum64 xh yh) as [sh sl] eqn:Ets1. destruct TS1 as [Fsh [Fsl [Esh Esum1]]].
  set (e1 := (e0 - 52)%Z).
  assert (Hb1 : bpow radix2 e1 = bpow radix2 (-52) * X).
  { unfold e1, X. replace (e0 - 52)%Z with (-52 + e0)%Z by ring. rewrite bpow_plus. ring. }
  assert (Hpos1 : 0 < bpow radix2 e1) by apply bpow_gt_0.
  assert (Bnd : forall k v, Rabs v <= IZR k * (bpow radix2 (-52) * X) -> bnd k e1 v) by (intros k v H; unfold bnd; rewrite Hb1; exact H).
  assert (Hnorm : forall v, 0.009 * bpow radix2 (-900) <= Rabs v -> bpow radix2 (-1022) <= Rabs v).
  { intros v Hv.
    assert (bpow radix2 (-1022) <= bpow radix2 (-907)) by (apply bpow_le; lia).
    assert (bpow radix2 (-907) = bpow radix2 (-900) / 128).
    { replace (-907)%Z with (-900 + -7)%Z by reflexivity. rewrite bpow_plus. bpow_num. field. }
    pose proof (bpow_gt_0 radix2 (-900)). lra. }
  pose proof Hy as Hy0. apply Rabs_le_inv in Hy0.
  assert (Hs0 : 0.01 * B xh <= B xh + B yh <= 1.99 * B xh) by lra.
  assert (Hs0n : bpow radix2 (-1022) <= Rabs (B xh + B yh)).
  { apply Hnorm. rewrite Rabs_pos_eq by lra. lra. }
  pose proof (rnd_rel_f _ Hs0n) as R1. rewrite <- Esh in R1. rewrite (Rabs_pos_eq (B xh + B yh)) in R1 by lra.
  rewrite P53 in R1. pose proof R1 as R1'. apply Rabs_le_inv in R1'.
  assert (Hsl : Rabs (B sl) <= / 9007199254740992 * (B xh + B yh)).
  { replace (B sl) with ((B xh + B yh) - B sh) by lra. rewrite Rabs_minus_sym. exact R1. }
  assert (Hsh : 0.0099 * B xh <= B sh <= 1.9901 * B xh) by lra.
  rewrite P52 in Bnd. rewrite P52 in Hxl'. rewrite P52 in Hyl'.
  assert (Bxl : bnd 1 e1 (B xl)) by (apply Bnd; change (IZR 1) with 1; lra).
  assert (Byl : bnd 1 e1 (B yl)) by (apply Bnd; change (IZR 1) with 1; lra).
  assert (Bsl : bnd 1 e1 (B sl)) by (apply Bnd; change (IZR 1) with 1; lra).
  assert (He1c : (e1 <= 849)%Z) by (unfold e1; lia).
  assert (He1' : (-1074 <= e1)%Z) by (unfold e1; lia).
  assert (Hroom : bpow radix2 e1 <= bpow radix2 1020) by (apply bpow_le; lia).
  assert (Hroom2 : forall v, bnd 1 e1 v -> Rabs v <= bpow radix2 1020).
  { intros v H. unfold bnd in H. change (IZR 1) with 1 in H. lra. }
  pose proof (two_sum_ieee xl yl Fxl Fyl (Hroom2 _ Bxl) (Hroom2 _ Byl)) as TS2.
  destruct (two_sum64 xl yl) as [th tl] eqn:Ets2. destruct TS2 as [Fth [Ftl [Eth Esum2]]].
  assert (Bxy : bnd 2 e1 (B xl + B yl)) by exact (bnd_plus 1 1 e1 _ _ Bxl Byl).
  assert (Bth : bnd 2 e1 (B th)).
  { rewrite Eth. apply bnd_round; [lia | lia | exact Bxy]. }
  assert (Btl : bnd 4 e1 (B tl)).
  { replace (B tl) with ((B xl + B yl) - B th) by lra. exact (bnd_minus 2 2 e1 _ _ Bxy Bth). }
  destruct (fadd_bnd 3 e1 sl th Fsl Fth ltac:(lia) He1' (pow_room 3 (1024 - e1) ltac:(lia) ltac:(lia)) ltac:(lia)
    (bnd_plus 1 2 e1 _ _ Bsl Bth)) as [Fc [Ec Bc]].
  assert (Hcsh : Rabs (B (fadd sl th)) <= Rabs (B sh)).
  { unfold bnd in Bc. rewrite Hb1, P52 in Bc. rewrite (Rabs_pos_eq (B sh)) by lra. change (IZR 3) with 3 in Bc. lra. }
  assert (A3 : Rabs (B sh) <= bpow radix2 1021).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 901); [lra | apply bpow_le; lia]. }
  assert (A4 : Rabs (B (fadd sl th)) <= bpow radix2 1021).
  { apply Rle_trans with (Rabs (B sh)); [exact Hcsh | exact A3]. }
  pose proof (fast_two_sum_ieee sh (fadd sl th) Fsh Fc A3 A4 (or_intror (or_introl Hcsh))) as FTS1.
  destruct (fast_two_sum64 sh (fadd sl th)) as [vh vl] eqn:Efs1.
  destruct FTS1 as [Fvh [Fvl [Evh Esum3]]].
  assert (Hc6 : Rabs (B (fadd sl th)) <= 3 * (/ 4503599627370496 * X)).
  { unfold bnd in Bc. rewrite Hb1, P52 in Bc. change (IZR 3) with 3 in Bc. exact Bc. }
  assert (Hs1 : 0.0098 * B xh <= B sh + B (fadd sl th) <= 1.9902 * B xh).
  { apply Rabs_le_inv in Hc6. lra. }
  assert (Hs1n : bpow radix2 (-1022) <= Rabs (B sh + B (fadd sl th))).
  { apply Hnorm. rewrite Rabs_pos_eq by lra. lra. }
  pose proof (rnd_rel_f _ Hs1n) as R2. rewrite <- Evh in R2. rewrite (Rabs_pos_eq (B sh + B (fadd sl th))) in R2 by lra.
  rewrite P53 in R2. pose proof R2 as R2'. apply Rabs_le_inv in R2'.
  assert (Hvh : 0.0097 * B xh <= B vh) by lra.
  assert (Hvl : Rabs (B vl) <= / 9007199254740992 * (B sh + B (fadd sl th))).
  { replace (B vl) with ((B sh + B (fadd sl th)) - B vh) by lra. rewrite Rabs_minus_sym. exact R2. }
  assert (Bvl : bnd 1 e1 (B vl)) by (apply Bnd; change (IZR 1) with 1; lra).
  destruct (fadd_bnd 5 e1 tl vl Ftl Fvl ltac:(lia) He1' (pow_room 5 (1024 - e1) ltac:(lia) ltac:(lia)) ltac:(lia)
    (bnd_plus 4 1 e1 _ _ Btl Bvl)) as [Fw [Ew Bw]].
  assert (Hwv : Rabs (B (fadd tl vl)) <= Rabs (B vh)).
  { unfold bnd in Bw. rewrite Hb1, P52 in Bw. change (IZR 5) with 5 in Bw. rewrite (Rabs_pos_eq (B vh)) by lra. lra. }
  assert (A5 : Rabs (B vh) <= bpow radix2 1021).
  { assert (Hvhhi : B vh <= 1.9903 * B xh) by lra. rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 901); [lra | apply bpow_le; lia]. }
  assert (A6 : Rabs (B (fadd tl vl)) <= bpow radix2 1021) by (apply Rle_trans with (Rabs (B vh)); [exact Hwv | exact A5]).
  pose proof (fast_two_sum_ieee vh (fadd tl vl) Fvh Fw A5 A6 (or_intror (or_introl Hwv))) as FTS2.
  unfold add64. rewrite Ets1, Ets2. cbv beta iota. rewrite Efs1. cbv beta iota.
  destruct (fast_two_sum64 vh (fadd tl vl)) as [zh zl] eqn:Efs2.
  destruct FTS2 as [Fzh [Fzl [Ezh Esum4]]].
  repeat split; try assumption.
  rewrite Esum4. exact Ezh.
Qed.

(** A rounding error is [2^-53] of the value plus half the least subnormal. *)
Lemma rnd_err_abs x : Rabs (rndF x - x) <= bpow radix2 (-53) * Rabs x + bpow radix2 (-1075).
Proof.
  destruct (error_N_FLT radix2 emin prec ltac:(unfold prec; lia) (fun n => negb (Z.even n)) x) as [eps [eta [He [Hn [_ E]]]]].
  change (round radix2 (FLT_exp emin prec) (Znearest (fun n => negb (Z.even n))) x) with (rndF x) in E.
  rewrite E.
  assert (Hu : bpow radix2 (-53) = / 2 * bpow radix2 (- prec + 1)).
  { replace (-53)%Z with (-1 + (- prec + 1))%Z by (unfold prec; reflexivity). rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). reflexivity. }
  assert (Hm : bpow radix2 (-1075) = / 2 * bpow radix2 emin).
  { replace (-1075)%Z with (-1 + emin)%Z by (unfold emin; reflexivity). rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). reflexivity. }
  rewrite Hu, Hm.
  replace (x * (1 + eps) + eta - x) with (x * eps + eta) by ring.
  apply Rle_trans with (Rabs (x * eps) + Rabs eta); [apply Rabs_triang | ].
  rewrite Rabs_mult. pose proof (Rabs_pos x). nra.
Qed.
