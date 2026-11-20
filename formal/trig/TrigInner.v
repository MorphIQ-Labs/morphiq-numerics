(** The inner reconstruction sums: finite normalized results, bounded error
    factors, and word magnitudes for the following outer additions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import TrigAdd TrigCancellation TrigMultiply.
Open Scope R_scope.

Lemma trig_inner_word_bounds h l v a : finite h -> finite l ->
 B h=rndF(B h+B l) -> Rabs v<=0.007923 -> Rabs a<=776/2^114 ->
 B h+B l=v*(1+a) -> Rabs(B h)<=0.009 /\ Rabs(B l)<=0.009.
Proof.
 intros H L N V A Value.
 assert (Scale:Rabs(1+a)<=1.001) by (interval with (i_prec 150)).
 assert (Full:Rabs(B h+B l)<=0.008).
 { rewrite Value,Rabs_mult.
   eapply Rle_trans with (0.007923*1.001);[|lra].
   apply Rmult_le_compat;try apply Rabs_pos;assumption. }
 destruct (trig_dw_word_upper (B h) (B l) 0.008 (B_fmt h) (B_fmt l) N ltac:(lra) Full)
   as [Head Low]. unfold trig_mul_u in Low;split;lra.
Qed.

Theorem trig_sine_inner_correct a t xh xl yh yl :
 0<=a<=50/64 -> Rabs t<=0.0078126 ->
 trig_reference_contract (sin a*(cos t-1)) (xh,xl) ->
 trig_reference_contract (cos a*sin t) (yh,yl) ->
 let '(h,l):=add64 xh xl yh yl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=0.009 /\ Rabs(B l)<=0.009 /\
 exists d, Rabs d<=776/2^114 /\ B h+B l=(B xh+B xl+(B yh+B yl))*(1+d).
Proof.
 intros A T X Y.
 assert (First:Rabs(sin a*(cos t-1))<=0.000031) by (interval with (i_prec 100)).
 assert (Second:Rabs(cos a*sin t)<=0.007813) by interval.
 destruct (trig_reference_magnitudes _ xh xl 0.000031 X ltac:(lra) First)
   as [Xfull [Xhead Xlow]].
 destruct (trig_reference_magnitudes _ yh yl 0.007813 Y ltac:(lra) Second)
   as [Yfull [Yhead Ylow]].
 destruct X as [Xh [Xl [Xn [Xe Xhe]]]]. destruct Y as [Yh [Yl [Yn [Ye Yhe]]]].
 pose proof (trig_head_dominance (B xh) (B yh) _ _ Xhe Yhe
   (trig_sine_product_dominance a t A T)) as Dominant.
 pose proof (proj1(trig_dominant_cancellation _ _ Dominant)) as Cancel.
 assert (Wide:1<=bpow radix2 1016) by (change 1 with (bpow radix2 0);apply bpow_le;lia).
 pose proof (trig_add_ieee xh xl yh yl Xh Xl Xn Yh Yl Yn
   ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) Cancel) as Result.
 destruct (add64 xh xl yh yl) as [h l]. destruct Result as [H [L [N [d [D Value]]]]].
 assert (Sum:Rabs(B xh+B xl+(B yh+B yl))<=0.007923).
 { pose proof (Rabs_triang (B xh+B xl) (B yh+B yl));lra. }
 destruct (trig_inner_word_bounds h l _ d H L N Sum D Value) as [Bh Bl].
 split;[exact H|]. split;[exact L|]. split;[exact N|].
 split;[exact Bh|]. split;[exact Bl|]. exists d;split;assumption.
Qed.

Theorem trig_cosine_inner_correct a t xh xl yh yl :
 (a=0 \/ /64<=a<=50/64) -> Rabs t<=0.0078126 ->
 trig_reference_contract (cos a*(cos t-1)) (xh,xl) ->
 trig_reference_contract (sin a*sin t) (yh,yl) ->
 let '(h,l):=sub64 xh xl yh yl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=0.009 /\ Rabs(B l)<=0.009 /\
 exists d, Rabs d<=776/2^114 /\ B h+B l=(B xh+B xl-(B yh+B yl))*(1+d).
Proof.
 intros A T X Y.
 assert (Range:0<=a<=50/64) by (destruct A;lra).
 assert (First:Rabs(cos a*(cos t-1))<=0.000031) by (interval with (i_prec 100)).
 assert (Second:Rabs(sin a*sin t)<=0.007813) by interval.
 destruct (trig_reference_magnitudes _ xh xl 0.000031 X ltac:(lra) First)
   as [Xfull [Xhead Xlow]].
 destruct (trig_reference_magnitudes _ yh yl 0.007813 Y ltac:(lra) Second)
   as [Yfull [Yhead Ylow]].
 destruct X as [Xh [Xl [Xn [Xe Xhe]]]]. destruct Y as [Yh [Yl [Yn [Ye Yhe]]]].
 assert (Cancel:Rabs(B xh)+Rabs(B yh)<=8*Rabs(B xh-B yh)).
 { destruct A as [Zero|Nonzero].
   - rewrite Zero,sin_0,Rmult_0_l,Rabs_R0,Rmult_0_r,Rminus_0_r in Yhe.
     assert (Yzero:B yh=0) by (apply Rabs_le_inv in Yhe;lra).
     apply (proj2(trig_zero_cancellation _ _ (or_intror Yzero))).
   - pose proof (trig_head_dominance (B xh) (B yh) _ _ Xhe Yhe
       (trig_cosine_product_dominance a t Nonzero T)) as Dominant.
     exact (proj2(trig_dominant_cancellation _ _ Dominant)). }
 assert (Wide:1<=bpow radix2 1016) by (change 1 with (bpow radix2 0);apply bpow_le;lia).
 pose proof (trig_sub_ieee xh xl yh yl Xh Xl Xn Yh Yl Yn
   ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) Cancel) as Result.
 destruct (sub64 xh xl yh yl) as [h l]. destruct Result as [H [L [N [d [D Value]]]]].
 assert (Sum:Rabs(B xh+B xl-(B yh+B yl))<=0.007923).
 { pose proof (Rabs_triang (B xh+B xl) (-(B yh+B yl))) as Triangle.
   rewrite Rabs_Ropp in Triangle;unfold Rminus;lra. }
 destruct (trig_inner_word_bounds h l _ d H L N Sum D Value) as [Bh Bl].
 split;[exact H|]. split;[exact L|]. split;[exact N|].
 split;[exact Bh|]. split;[exact Bl|]. exists d;split;assumption.
Qed.
