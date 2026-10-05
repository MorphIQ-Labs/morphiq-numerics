(** Double-word division in binary64, with gradual underflow, meets the bounds
    Muller and Rideau prove in the unbounded-exponent model, on a domain stated
    on the inputs: for some [L, H >= 0] with [2L + 2H <= 917], every nonzero word
    [w] has [2^-L <= |w| < 2^H].

    Beyond what Binary64Add.v and Binary64Mul.v bridge, a division rounds two
    quotients, [x_hi / y] and [d / y], and rounds two differences the unbounded
    algorithm leaves exact. The first quotient is at least [2^(-L-H)] unless
    zero. The remainder [d] is a sum of products and words on [2^(-2L-H-105)]'s
    grid, so it is zero or at least that ([Grid.v]), and [d / y] is zero or at
    least [2^(-2L-2H-105) >= 2^-1022]. Both quotients therefore round alike in
    both models. The differences are exact in the unbounded model
    ([xhmpih_exact], [div_error_FLX], [Algo15_P]), so rounding them changes
    nothing. Overflow is outside both models. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core Relative Mult_error Div_sqrt_error.
From Double Require Import DWPlus F2Sum DWTimesFP DWDivFP DWDivDW.
From Binary64 Require Import Binary64Add Binary64Mul Grid.
From Binary64 Require Instances.
Require TwoProdBinary64.

Open Scope R_scope.

(** [w] is zero or within [[2^-L, 2^H)] in magnitude. *)
Definition in_range (L H : Z) (w : R) : Prop :=
  w = 0 \/ (bpow radix2 (- L) <= Rabs w /\ Rabs w < bpow radix2 H).

Lemma fexpF_ge e : (e - 53 <= FLT_exp emin prec e)%Z.
Proof. unfold FLT_exp, prec, emin. lia. Qed.

Lemma fexpX_ge e : (e - 53 <= FLX_exp prec e)%Z.
Proof. unfold FLX_exp, prec. lia. Qed.

Lemma range_lower L H w : in_range L H w -> w = 0 \/ bpow radix2 (- L) <= Rabs w.
Proof. intros [-> | [H1 _]]; [now left | now right]. Qed.

Lemma bpow_half e : bpow radix2 (e - 1) = bpow radix2 e / 2.
Proof.
  replace e with ((e - 1) + 1)%Z at 2 by ring.
  rewrite bpow_plus, bpow_1. simpl. field.
Qed.

(** A quotient's magnitude, bounded below. *)
Lemma quot_lower a b m n :
  bpow radix2 m <= Rabs a -> b <> 0 -> Rabs b < bpow radix2 n ->
  bpow radix2 (m - n) <= Rabs (a / b).
Proof.
  intros Ha Hb0 Hb. unfold Rdiv. rewrite Rabs_mult, (Rabs_Rinv b Hb0).
  assert (Pb : 0 < Rabs b) by now apply Rabs_pos_lt.
  apply Rmult_le_reg_r with (Rabs b); [exact Pb | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  unfold Zminus. rewrite bpow_plus, bpow_opp.
  apply Rle_trans with (bpow radix2 m * / bpow radix2 n * bpow radix2 n).
  - apply Rmult_le_compat_l; [ | lra].
    apply Rmult_le_pos; [apply bpow_ge_0 | apply Rlt_le, Rinv_0_lt_compat, bpow_gt_0].
  - rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rgt_not_eq, bpow_gt_0). exact Ha.
Qed.

(** A rounded value keeps at least half its argument's magnitude. *)
Lemma round_half q : Rabs q / 2 <= Rabs (rndX q).
Proof.
  pose proof (relative_error_N_FLX radix2 prec (ltac:(unfold prec; lia)) ne q) as E.
  assert (U : / 2 * bpow radix2 (- prec + 1) <= / 2)
    by (assert (bpow radix2 (- prec + 1) <= 1) by (apply (bpow_le radix2 _ 0); unfold prec; lia); lra).
  pose proof (Rabs_triang_inv q (q - rndX q)) as T.
  replace (q - (q - rndX q)) with (rndX q) in T by ring.
  rewrite Rabs_minus_sym in T.
  pose proof (Rabs_pos q).
  assert (Rabs (rndX q - q) <= / 2 * Rabs q) by nra.
  lra.
Qed.

Definition div_f64 (xh xl y : R) : R * R :=
  let th := rndF (xh / y) in
  let '(pih, pil) := two_prod th y in
  let dh := rndF (xh - pih) in
  let dt := rndF (dh - pil) in
  let d := rndF (dt + xl) in
  let tl := rndF (d / y) in
  fast_two_sum th tl.

Theorem div_f64_bound L H xh xl y :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  fmtF xh -> fmtF xl -> fmtF y -> xh = rndF (xh + xl) -> y <> 0 ->
  in_range L H xh -> in_range L H xl -> in_range L H y ->
  let '(zh, zl) := div_f64 xh xl y in
  let xy := (xh + xl) / y in
  Rabs ((zh + zl - xy) / xy) <= 3 * (bpow radix2 (- prec) * bpow radix2 (- prec)).
Proof.
  intros HL HH HLH Fxh Fxl Fy Ex Hy Rxh Rxl Ry.
  assert (Ylt : Rabs y < bpow radix2 H) by (destruct Ry as [-> | [_ Hy']]; [now elim Hy | exact Hy']).
  assert (Yge : bpow radix2 (- L) <= Rabs y) by (destruct Ry as [-> | [Hy' _]]; [now elim Hy | exact Hy']).
  pose proof (Instances.div_f64_bound xh xl y (dw_of_binary64 xh xl Fxh Fxl Ex) (fmtF_fmtX y Fy) Hy) as B.
  unfold DWDivFP3 in B. rewrite TwoProd_Fast2Mult in B. cbv zeta in B.
  unfold div_f64.
  (* The first quotient. *)
  assert (Q : normal_or_zero (xh / y)).
  { unfold normal_or_zero. destruct (range_lower _ _ _ Rxh) as [-> | Hx].
    - left. unfold Rdiv. ring.
    - right. apply Rle_trans with (bpow radix2 (- L - H)).
      + apply bpow_le. lia.
      + now apply quot_lower. }
  rewrite (normal_round _ Q).
  set (th := rndX (xh / y)) in *.
  assert (Fth : fmtF th) by (unfold th; rewrite <- (normal_round _ Q); apply fmtF_rnd).
  (* two_prod th y is in its domain: |th y| >= |xh| / 2. *)
  assert (D : in_two_prod_domain th y).
  { unfold in_two_prod_domain. destruct (range_lower _ _ _ Rxh) as [Hx0 | Hx].
    - left. unfold th. rewrite Hx0. unfold Rdiv. rewrite Rmult_0_l, (round_0 radix2 (FLX_exp prec) (Znearest ne)). ring.
    - right. pose proof (round_half (xh / y)) as R2. fold th in R2.
      rewrite Rabs_mult.
      assert (Exh : Rabs (xh / y) * Rabs y = Rabs xh)
        by (rewrite <- Rabs_mult; f_equal; field; exact Hy).
      apply Rle_trans with (Rabs xh / 2).
      + apply Rle_trans with (bpow radix2 (- L) / 2); [ | lra].
        rewrite <- bpow_half.
        apply bpow_le. lia.
      + pose proof (Rabs_pos y). nra. }
  rewrite (two_prod_eq th y Fth Fy D).
  pose proof (Instances.fast2mult_exact th y (fmtF_fmtX th Fth) (fmtF_fmtX y Fy)) as PE.
  assert (Fpih : fmtF (fst (Fast2Mult prec ne th y)))
    by (rewrite <- (two_prod_eq th y Fth Fy D); apply two_prod_fmt).
  assert (Fpil : fmtF (snd (Fast2Mult prec ne th y)))
    by (rewrite <- (two_prod_eq th y Fth Fy D); apply two_prod_fmt).
  assert (PIH : fst (Fast2Mult prec ne th y) = rndX (th * y)) by reflexivity.
  destruct (Fast2Mult prec ne th y) as [pih pil] eqn:C. cbn [fst snd] in Fpih, Fpil, PE, PIH.
  (* dh = xh - pih exactly. *)
  rewrite (diff_round xh pih Fxh Fpih).
  assert (Edh : rndX (xh - pih) = xh - pih)
    by (rewrite PIH; unfold th; exact (@xhmpih_exact prec (ltac:(unfold prec; lia)) ne eq_refl xh y (fmtF_fmtX xh Fxh) Hy)).
  assert (Fdh : fmtF (xh - pih)) by (rewrite <- Edh, <- (diff_round xh pih Fxh Fpih); apply fmtF_rnd).
  rewrite Edh.
  (* dt = xh - th y exactly. *)
  rewrite (diff_round _ pil Fdh Fpil).
  assert (Edt : rndX (xh - pih - pil) = xh - pih - pil).
  { apply round_generic; auto with typeclass_instances.
    replace (xh - pih - pil) with (xh - th * y) by lra.
    unfold th. apply div_error_FLX; auto with typeclass_instances; now apply fmtF_fmtX. }
  assert (Fdt : fmtF (xh - pih - pil)) by (rewrite <- Edt, <- (diff_round _ pil Fdh Fpil); apply fmtF_rnd).
  rewrite Edt.
  rewrite (sum_round _ xl Fdt Fxl).
  set (d := rndX (xh - pih - pil + xl)).
  assert (Fd : fmtF d) by (unfold d; rewrite <- (sum_round _ xl Fdt Fxl); apply fmtF_rnd).
  (* The remainder's quotient: d is on the grid 2^(-2L-H-105). *)
  assert (Gd : on_grid (- 2 * L - H - 105) d).
  { assert (Gx : on_grid (- L - 52) xh)
      by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fxh | exact (range_lower _ _ _ Rxh)]).
    assert (Gl : on_grid (- L - 52) xl)
      by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fxl | exact (range_lower _ _ _ Rxl)]).
    assert (Gy : on_grid (- L - 52) y)
      by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fy | right; exact Yge]).
    assert (Gt : on_grid (- L - H - 1 - 52) th).
    { apply (grid_fmt_bound (FLT_exp emin prec) (- L - H - 1)); [exact fexpF_ge | exact Fth | ].
      destruct (range_lower _ _ _ Rxh) as [Hx0 | Hx].
      - left. unfold th. rewrite Hx0. unfold Rdiv. rewrite Rmult_0_l, (round_0 radix2 (FLX_exp prec) (Znearest ne)). reflexivity.
      - right. pose proof (round_half (xh / y)) as R2. fold th in R2.
        pose proof (quot_lower xh y (- L) H Hx Hy Ylt) as Q2.
        rewrite bpow_half.
        lra. }
    assert (Gp : on_grid (- 2 * L - H - 105) (th * y)).
    { replace (- 2 * L - H - 105)%Z with ((- L - H - 1 - 52) + (- L - 52))%Z by ring.
      now apply grid_mult. }
    assert (Gpih : on_grid (- 2 * L - H - 105) pih)
      by (rewrite PIH; exact (@grid_round (FLX_exp prec) _ (Znearest ne) _ _ _ Gp)).
    assert (Gpil : on_grid (- 2 * L - H - 105) pil)
      by (replace pil with (th * y - pih) by lra; now apply grid_minus).
    assert (Le : (- 2 * L - H - 105 <= - L - 52)%Z) by lia.
    unfold d. apply (@grid_round (FLX_exp prec) _ (Znearest ne) _).
    apply grid_plus; [apply grid_minus; [apply grid_minus | ] | ];
      try (apply (grid_le (- L - 52)); assumption); assumption. }
  assert (Q2 : normal_or_zero (d / y)).
  { unfold normal_or_zero. destruct (Req_dec d 0) as [-> | Hd].
    - left. unfold Rdiv. ring.
    - right. apply Rle_trans with (bpow radix2 (- 2 * L - H - 105 - H)).
      + apply bpow_le. lia.
      + apply quot_lower; [ | exact Hy | exact Ylt]. now apply grid_nonzero. }
  rewrite (normal_round _ Q2).
  assert (Ftl : fmtF (rndX (d / y))) by (rewrite <- (normal_round _ Q2); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fth Ftl).
  exact B.
Qed.

Lemma mul_f64_fmt a b c : fmtF (fst (mul_f64 a b c)) /\ fmtF (snd (mul_f64 a b c)).
Proof.
  unfold mul_f64. destruct (two_prod a c) as [ch cl1].
  destruct (fast_two_sum ch (rndF (b * c))) as [th tl1].
  unfold fast_two_sum. split; apply fmtF_rnd.
Qed.

(** Every component of [DWTimesFP yh yl th] stays on its operands' product grid. *)
Lemma grid_DWTimesFP a b yh yl th :
  on_grid a yh -> on_grid a yl -> on_grid b th ->
  on_grid (a + b) (fst (DWTimesFP prec ne yh yl th))
  /\ on_grid (a + b) (snd (DWTimesFP prec ne yh yl th)).
Proof.
  intros Gh Gl Gt.
  assert (G1 : on_grid (a + b) (yh * th)) by now apply grid_mult.
  assert (G2 : on_grid (a + b) (yl * th)) by now apply grid_mult.
  unfold DWTimesFP. rewrite TwoProd_Fast2Mult.
  unfold Fast2Mult, F2Sum.Fast2Sum, F2SumFLX.Fast2Sum. cbn [fst snd].
  split; repeat match goal with
    | |- on_grid _ (round _ _ _ _) => apply (@grid_round (FLX_exp prec) _ (Znearest ne) _)
    | |- on_grid _ (_ + _) => apply grid_plus
    | |- on_grid _ (_ - _) => apply grid_minus
    | _ => assumption
  end.
Qed.

Definition div (xh xl yh yl : R) : R * R :=
  let th := rndF (xh / yh) in
  let '(rh, rl) := mul_f64 yh yl th in
  let pih := rndF (xh - rh) in
  let dl := rndF (xl - rl) in
  let d := rndF (pih + dl) in
  let tl := rndF (d / yh) in
  fast_two_sum th tl.

Theorem div_bound L H xh xl yh yl :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  fmtF yh -> fmtF yl -> yh = rndF (yh + yl) -> yh <> 0 ->
  in_range L H xh -> in_range L H xl -> in_range L H yh -> in_range L H yl ->
  let '(zh, zl) := div xh xl yh yl in
  let xy := (xh + xl) / (yh + yl) in
  Rabs ((zh + zl - xy) / xy)
    <= 15 * bpow radix2 (- prec) ^ 2 + 56 * bpow radix2 (- prec) ^ 3.
Proof.
  intros HL HH HLH Fxh Fxl Ex Fyh Fyl Ey Hy Rxh Rxl Ryh Ryl.
  assert (Ylt : Rabs yh < bpow radix2 H) by (destruct Ryh as [-> | [_ Hy']]; [now elim Hy | exact Hy']).
  assert (Yge : bpow radix2 (- L) <= Rabs yh) by (destruct Ryh as [-> | [Hy' _]]; [now elim Hy | exact Hy']).
  pose proof (Instances.div_bound xh xl yh yl (dw_of_binary64 xh xl Fxh Fxl Ex)
                (dw_of_binary64 yh yl Fyh Fyl Ey) Hy) as B.
  pose proof (@Algo15_P prec (ltac:(unfold prec; lia)) ne eq_refl Instances.fast2mult_exact
                (TwoProd_Fast2Mult prec ne) xh xl yh yl (ltac:(unfold prec; lia)) Hy
                (dw_of_binary64 xh xl Fxh Fxl Ex) (dw_of_binary64 yh yl Fyh Fyl Ey)) as P.
  unfold DWDivDW2 in B. cbv zeta in B, P.
  unfold div.
  assert (Q : normal_or_zero (xh / yh)).
  { unfold normal_or_zero. destruct (range_lower _ _ _ Rxh) as [-> | Hx].
    - left. unfold Rdiv. ring.
    - right. apply Rle_trans with (bpow radix2 (- L - H)).
      + apply bpow_le. lia.
      + now apply quot_lower. }
  rewrite (normal_round _ Q).
  set (th := rndX (xh / yh)) in *.
  assert (Fth : fmtF th) by (unfold th; rewrite <- (normal_round _ Q); apply fmtF_rnd).
  (* th is zero, or at least 2^(-L-H-1), and |yh th| >= |xh| / 2. *)
  assert (Th : th = 0 \/ bpow radix2 (- L - H - 1) <= Rabs th
               /\ bpow radix2 (- L - 1) <= Rabs (yh * th)).
  { destruct (range_lower _ _ _ Rxh) as [Hx0 | Hx].
    - left. unfold th. rewrite Hx0. unfold Rdiv.
      now rewrite Rmult_0_l, (round_0 radix2 (FLX_exp prec) (Znearest ne)).
    - right. pose proof (round_half (xh / yh)) as R2. fold th in R2.
      pose proof (quot_lower xh yh (- L) H Hx Hy Ylt) as Q2.
      assert (Exh : Rabs (xh / yh) * Rabs yh = Rabs xh)
        by (rewrite <- Rabs_mult; f_equal; field; exact Hy).
      split.
      + rewrite bpow_half. lra.
      + rewrite Rabs_mult, bpow_half. pose proof (Rabs_pos yh). nra. }
  assert (Dt : in_two_prod_domain yh th).
  { unfold in_two_prod_domain. destruct Th as [-> | [_ T2]].
    - left. ring.
    - right. apply Rle_trans with (2 := T2). apply bpow_le. lia. }
  assert (Dl : normal_or_zero (yl * th)).
  { unfold normal_or_zero. destruct (range_lower _ _ _ Ryl) as [-> | Hl]; [left; ring | ].
    destruct Th as [-> | [T1 _]]; [left; ring | right].
    rewrite Rabs_mult.
    apply Rle_trans with (bpow radix2 (- L) * bpow radix2 (- L - H - 1)).
    - rewrite <- bpow_plus. apply bpow_le. lia.
    - apply Rmult_le_compat; auto using bpow_ge_0. }
  rewrite (mul_f64_eq yh yl th Fyh Fyl Fth Dt Dl).
  destruct (mul_f64_fmt yh yl th) as [Frh Frl].
  rewrite (mul_f64_eq yh yl th Fyh Fyl Fth Dt Dl) in Frh, Frl.
  assert (Gx : on_grid (- L - 52) xh)
    by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fxh | exact (range_lower _ _ _ Rxh)]).
  assert (Gl : on_grid (- L - 52) xl)
    by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fxl | exact (range_lower _ _ _ Rxl)]).
  assert (Gyh : on_grid (- L - 52) yh)
    by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fyh | right; exact Yge]).
  assert (Gyl : on_grid (- L - 52) yl)
    by (apply (grid_fmt_bound (FLT_exp emin prec) (- L)); [exact fexpF_ge | exact Fyl | exact (range_lower _ _ _ Ryl)]).
  assert (Gt : on_grid (- L - H - 1 - 52) th).
  { apply (grid_fmt_bound (FLT_exp emin prec) (- L - H - 1)); [exact fexpF_ge | exact Fth | ].
    destruct Th as [-> | [T1 _]]; [now left | now right]. }
  destruct (grid_DWTimesFP _ _ yh yl th Gyh Gyl Gt) as [Grh Grl].
  destruct (DWTimesFP prec ne yh yl th) as [rh rl] eqn:R.
  cbn [fst snd] in Frh, Frl, Grh, Grl, P.
  (* pih = xh - rh exactly. *)
  rewrite (diff_round xh rh Fxh Frh).
  assert (Epih : rndX (xh - rh) = xh - rh)
    by (apply round_generic; auto with typeclass_instances).
  assert (Fpih : fmtF (xh - rh)) by (rewrite <- Epih, <- (diff_round xh rh Fxh Frh); apply fmtF_rnd).
  rewrite Epih.
  rewrite (diff_round xl rl Fxl Frl).
  assert (Fdl : fmtF (rndX (xl - rl))) by (rewrite <- (diff_round xl rl Fxl Frl); apply fmtF_rnd).
  rewrite (sum_round _ _ Fpih Fdl).
  set (d := rndX (xh - rh + rndX (xl - rl))).
  assert (Le : (- 2 * L - H - 105 <= - L - 52)%Z) by lia.
  assert (Gd : on_grid (- 2 * L - H - 105) d).
  { replace (- 2 * L - H - 105)%Z with ((- L - 52) + (- L - H - 1 - 52))%Z in * by ring.
    unfold d. apply (@grid_round (FLX_exp prec) _ (Znearest ne) _).
    apply grid_plus.
    - apply grid_minus; [ | exact Grh]. apply (grid_le (- L - 52)); [lia | exact Gx].
    - apply (@grid_round (FLX_exp prec) _ (Znearest ne) _).
      apply grid_minus; [ | exact Grl]. apply (grid_le (- L - 52)); [lia | exact Gl]. }
  assert (Q2 : normal_or_zero (d / yh)).
  { unfold normal_or_zero. destruct (Req_dec d 0) as [-> | Hd].
    - left. unfold Rdiv. ring.
    - right. apply Rle_trans with (bpow radix2 (- 2 * L - H - 105 - H)).
      + apply bpow_le. lia.
      + apply quot_lower; [ | exact Hy | exact Ylt]. now apply grid_nonzero. }
  rewrite (normal_round _ Q2).
  assert (Ftl : fmtF (rndX (d / yh))) by (rewrite <- (normal_round _ Q2); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fth Ftl).
  exact B.
Qed.
