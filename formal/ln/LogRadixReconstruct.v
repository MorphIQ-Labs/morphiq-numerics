(** The log2 fast path's integer exponent addition. Its cancellation budget
    follows from the reduced logarithm range, including an exact zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid RoundingTest.
From Interval Require Import Tactic.
Require Import ExpFast LnTables LnReduction LnAccurate Ln1pLemmas LnFastY
  LnFastCompose LogRadixConstants LogRadixAccurate LogRadixFast LogRadixGrid
  LogRadixScale LogRadixFastBound.
Open Scope R_scope.

Lemma radix_reconstruct_fast e h l w : (Z.abs e<=1074)%Z ->
  finite h -> finite l -> B h=rndF(B h+B l) -> Rabs w<=0.51 ->
  Rabs(B h+B l-w)<=9/2^67*Rabs w ->
  let '(a,b):=if (e=?0)%Z then (h,l) else add64 (fe e) c_zero h l in
  finite a /\ finite b /\ B a=rndF(B a+B b) /\
  Rabs(B a+B b-(IZR e+w))<=/2^63*Rabs(IZR e+w).
Proof.
  intros E Fh Fl D W Error. destruct (Z.eqb_spec e 0) as [Z | N].
  - subst e. change (IZR 0) with 0. rewrite Rplus_0_l.
    split; [exact Fh | split; [exact Fl | split; [exact D | ]]].
    apply Rle_trans with (1:=Error); apply Rmult_le_compat_r; [apply Rabs_pos | interval].
  - destruct (fe_ok e ltac:(lia)) as [Fe Ve].
    assert (Ae : Rabs(IZR e)<=1074) by (rewrite <-abs_IZR; apply IZR_le; exact E).
    assert (Sum : Rabs(B h+B l)<=1).
    { pose proof (Rabs_triang_inv (B h+B l) w).
      assert (0<=9/2^67<=/100) by (split; interval). pose proof (Rabs_pos w); nra. }
    assert (H : Rabs(B h)<=1) by (rewrite D; apply rnd_bound; [apply (fmt_pow 0); lia | exact Sum]).
    assert (L : Rabs(B l)<=2).
    { replace (B l) with ((B h+B l)-B h) by ring.
      apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
    destruct (reconstruction_ratios e w N W) as [Wr _].
    assert (Size : Rabs(IZR e)+Rabs w<=7/2*Rabs(IZR e+w)).
    { pose proof (Rabs_triang (IZR e+w) (-w)) as T.
      replace (IZR e+w+-w) with (IZR e) in T by ring. rewrite Rabs_Ropp in T.
      pose proof (Rabs_pos (IZR e+w)); lra. }
    set (eps:=(9/2^67)*1.1).
    assert (Ep : 0<=eps<=/100) by (unfold eps; split; interval).
    assert (Err : Rabs(IZR e-IZR e)+Rabs(B h+B l-w)<=eps*Rabs(IZR e+w)).
    { rewrite Rminus_diag_eq,Rabs_R0,Rplus_0_l by reflexivity.
      apply Rle_trans with (1:=Error). unfold eps.
      assert (0<=9/2^67) by (left; interval). nra. }
    destruct (lf_perturbed_sum (IZR e) (B h+B l) (IZR e) w (IZR e+w) eps
      eq_refl Ep Size Err) as [Cancel Near].
    assert (De : B (fe e)=rndF(B (fe e)+B c_zero)).
    { rewrite c_zero_val,Rplus_0_r; symmetry; apply round_generic; [exact _ | apply B_fmt]. }
    assert (Big : forall v, Rabs v<=2048 -> Rabs v<=bpow radix2 100).
    { intros v V; apply Rle_trans with 2048; [exact V | interval]. }
    pose proof (lf_add_pair (fe e) c_zero h l Fe c_zero_finite Fh Fl De D
      (Big (B (fe e)) ltac:(rewrite Ve; lra))
      (Big (B c_zero) ltac:(rewrite c_zero_val,Rabs_R0; lra))
      (Big (B h) ltac:(lra)) (Big (B l) ltac:(lra))
      ltac:(rewrite Ve,c_zero_val,Rplus_0_r; exact Cancel)) as P.
    destruct (add64 (fe e) c_zero h l) as [a b].
    destruct P as [Fa [Fb [Da [d [Dd V]]]]]. rewrite Ve,c_zero_val,Rplus_0_r in V.
    pose proof (lf_rounded_sum _ _ _ eps d (proj1 Ep) Near Dd V) as Bound.
    split; [exact Fa | split; [exact Fb | split; [exact Da | ]]].
    apply Rle_trans with (1:=Bound); apply Rmult_le_compat_r; [apply Rabs_pos | ].
    unfold eps; interval with (i_prec 180).
Qed.

Theorem log2_fast_value_bounded x : finite x -> 0<B x ->
  let '(h,l):=log2_fast_value x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h+B l-ln(B x)/ln 2)<=/2^63*Rabs(ln(B x)/ln 2).
Proof.
  intros Fx Px. pose proof (reduce_ok x Fx Px) as R.
  unfold log2_fast_value. destruct (reduce x) as [[[e i] y] r].
  destruct R as [I [Er [Fy [Y [Gy [V E]]]]]].
  destruct (ln_range i I) as [Lo [Hi _]].
  assert (Value : ln(B x)/ln 2=IZR e+ln(B y)/ln 2).
  { rewrite V,ln_pow2 by lra. field. assert (0<ln 2) by interval; lra. }
  assert (W : Rabs(ln(B y)/ln 2)<=0.51).
  { assert (0.70703125<=B y<=1.4140625) by lra; interval with (i_prec 100). }
  pose proof (lf_ln_y_ok y i I Fy Y Gy) as L. pose proof (radix_ln_y_grid y i I Fy Y Gy) as G.
  pose proof inv_ln2_dw_ok as C. pose proof inv_ln2_pair_grid as CG.
  destruct (lf_ln_y y i) as [xh xl]; destruct inv_ln2_dw as [ch cl].
  destruct L as [Fxh [Fxl [Dx [Xh [Xl Error]]]]]; destruct G as [Gxh Gxl].
  destruct C as [Fch [Fcl [Dc Vc]]]; destruct CG as [Gch Gcl].
  assert (Size : Rabs(B ch+B cl)<=2) by
    (rewrite Vc,inv_ln2_hi_val,inv_ln2_lo_val; interval).
  destruct (radix_pair_size ch cl Dc Size) as [Ch Cl].
  assert (LnError : Rabs(B xh+B xl-ln(B y))<=/2^64*Rabs(ln(B y))).
  { apply Rle_trans with (1:=Error); apply Rmult_le_compat_r; [apply Rabs_pos | interval]. }
  pose proof (radix_scale_accuracy xh xl ch cl (ln(B y)) (ln 2)
    Fxh Fxl Dx Fch Fcl Dc ltac:(lra) ltac:(lra) ltac:(lra) Cl Gxh Gxl Gch Gcl
    ltac:(interval) LnError ltac:(rewrite Vc; exact inv_ln2_dw_residual)) as P.
  destruct (mul64 xh xl ch cl) as [wh wl]. destruct P as [Fwh [Fwl [Dw Ew]]].
  rewrite Value. apply radix_reconstruct_fast; try assumption; lia.
Qed.
