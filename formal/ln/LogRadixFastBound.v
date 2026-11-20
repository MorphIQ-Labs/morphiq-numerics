(** Error composition for the executable fast radix logarithms. The shared
    ln error, generated reciprocal residual and actual double-word product
    are checked together, including zero inputs to the scaling stage. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Grid RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas LnFastValue LogRadixConstants LogRadixAccurate
  LogRadixFast LogRadixGrid LogRadixScale.
Open Scope R_scope.

Lemma radix_pair_size h l : B h=rndF(B h+B l) -> Rabs(B h+B l)<=2 ->
  Rabs(B h)<=2 /\ Rabs(B l)<=4.
Proof.
  intros D S. assert (H : Rabs(B h)<=2) by
    (rewrite D; apply rnd_bound; [apply (fmt_pow 1); lia | exact S]).
  split; [exact H | replace (B l) with ((B h+B l)-B h) by ring].
  apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra.
Qed.

Theorem radix_scale_accuracy xh xl ch cl v b :
  finite xh -> finite xl -> B xh=rndF(B xh+B xl) ->
  finite ch -> finite cl -> B ch=rndF(B ch+B cl) ->
  Rabs(B xh)<=2048 -> Rabs(B xl)<=2048 -> Rabs(B ch)<=4 -> Rabs(B cl)<=4 ->
  on_grid (-623) (B xh) -> on_grid (-623) (B xl) ->
  on_grid (-109) (B ch) -> on_grid (-109) (B cl) ->
  0<b -> Rabs(B xh+B xl-v)<=/2^64*Rabs v ->
  Rabs((B ch+B cl)*b-1)<=/2^109 ->
  let '(h,l):=mul64 xh xl ch cl in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h+B l-v/b)<=9/2^67*Rabs(v/b).
Proof.
  intros Fxh Fxl Dx Fch Fcl Dc Xh Xl Ch Cl Gxh Gxl Gch Gcl Pb Es Ec.
  destruct (relative_error (B xh+B xl) v (/2^64) ltac:(left; interval) Es) as [ds [Ds Vs]].
  set (dc:=(B ch+B cl)*b-1) in *.
  assert (Vc : B ch+B cl=/b*(1+dc)) by (unfold dc; field; lra).
  pose proof (radix_scale_ieee xh xl ch cl Fxh Fxl Dx Fch Fcl Dc
    Xh Xl Ch Cl Gxh Gxl Gch Gcl) as P.
  destruct (mul64 xh xl ch cl) as [h l]. destruct P as [Fh [Fl [D [dm [Dm V]]]]].
  assert (Error : Rabs((1+ds)*(1+dc)*(1+dm)-1)<=9/2^67).
  { apply Rabs_le_inv in Ds; apply Rabs_le_inv in Ec; apply Rabs_le_inv in Dm.
    interval with (i_prec 180). }
  split; [exact Fh | split; [exact Fl | split; [exact D | ]]].
  rewrite V,Vs,Vc.
  replace (v*(1+ds)*(/b*(1+dc))*(1+dm)-v/b)
    with ((v/b)*((1+ds)*(1+dc)*(1+dm)-1)) by (unfold Rdiv; ring).
  rewrite Rabs_mult,Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact Error].
Qed.

Theorem log10_fast_value_bounded x : finite x -> 0<B x ->
  let '(h,l):=log10_fast_value x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h+B l-ln(B x)/ln 10)<=/2^63*Rabs(ln(B x)/ln 10).
Proof.
  intros Fx Px. pose proof (lf_ln_fast_value_ok x Fx Px) as L.
  pose proof (radix_ln_fast_grid x Fx Px) as G.
  pose proof inv_ln10_dw_ok as C. pose proof inv_ln10_pair_grid as CG.
  unfold log10_fast_value. destruct (lf_ln_fast_value x) as [xh xl]; destruct inv_ln10_dw as [ch cl].
  destruct L as [Fxh [Fxl [Dx [Xh [Xl E]]]]]; destruct G as [Gxh Gxl].
  destruct C as [Fch [Fcl [Dc Vc]]]; destruct CG as [Gch Gcl].
  assert (Size : Rabs(B ch+B cl)<=2) by
    (rewrite Vc,inv_ln10_hi_val,inv_ln10_lo_val; interval).
  destruct (radix_pair_size ch cl Dc Size) as [Ch Cl].
  pose proof (radix_scale_accuracy xh xl ch cl (ln(B x)) (ln 10)
    Fxh Fxl Dx Fch Fcl Dc ltac:(lra) Xl ltac:(lra) Cl Gxh Gxl Gch Gcl
    ltac:(interval) E ltac:(rewrite Vc; exact inv_ln10_dw_residual)) as P.
  destruct (mul64 xh xl ch cl) as [h l]. destruct P as [Fh [Fl [D Error]]].
  split; [exact Fh | split; [exact Fl | split; [exact D | ]]].
  apply Rle_trans with (1:=Error). apply Rmult_le_compat_r; [apply Rabs_pos | interval with (i_prec 100)].
Qed.
