(** IEEE double-word addition under bounded cancellation, including exact zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import LnFastAdd TrigMultiply.
Open Scope R_scope.

Lemma trig_add_zero_words xh xl yh yl :
 fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) ->
 Rabs xh+Rabs yh<=8*Rabs(xh+yh) -> xh+xl+(yh+yl)=0 ->
 xh=0 /\ xl=0 /\ yh=0 /\ yl=0.
Proof.
 intros Xh Xl X Yh Yl Y Cancel Zero.
 pose proof (trig_dw_low xh xl Xh Xl X) as LowX.
 pose proof (trig_dw_low yh yl Yh Yl Y) as LowY.
 pose proof (Rabs_triang xl yl) as Sum.
 assert (Value:Rabs(xh+yh)=Rabs(xl+yl)).
 { replace (xh+yh) with (-(xl+yl)) by lra;apply Rabs_Ropp. }
 assert (Heads:Rabs xh=0 /\ Rabs yh=0).
 { rewrite Value in Cancel. pose proof (Rabs_pos xh);pose proof (Rabs_pos yh).
   clear - LowX LowY Sum Cancel H H0;unfold trig_mul_u in *;split;lra. }
 destruct Heads as [Hx Hy].
 assert (Hx0:xh=0) by (pose proof (Rabs_le_inv xh 0 ltac:(lra));lra).
 assert (Hy0:yh=0) by (pose proof (Rabs_le_inv yh 0 ltac:(lra));lra).
 rewrite Hx in LowX;rewrite Hy in LowY.
 apply Rabs_le_inv in LowX,LowY. repeat split;try assumption;lra.
Qed.

Lemma trig_add_zero : add 0 0 0 0=(0,0).
Proof.
 unfold add,two_sum,fast_two_sum;cbn zeta.
 repeat first [rewrite round_0 by exact _|rewrite Rplus_0_l|rewrite Rminus_0_r]. reflexivity.
Qed.

Theorem trig_add_ieee xh xl yh yl :
 finite xh -> finite xl -> B xh=rndF(B xh+B xl) ->
 finite yh -> finite yl -> B yh=rndF(B yh+B yl) ->
 Rabs(B xh)<=bpow radix2 1016 -> Rabs(B xl)<=bpow radix2 1016 ->
 Rabs(B yh)<=bpow radix2 1016 -> Rabs(B yl)<=bpow radix2 1016 ->
 Rabs(B xh)+Rabs(B yh)<=8*Rabs(B xh+B yh) ->
 let '(h,l):=add64 xh xl yh yl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 exists a, Rabs a<=776/2^114 /\ B h+B l=(B xh+B xl+(B yh+B yl))*(1+a).
Proof.
 intros Xh Xl X Yh Yl Y Bxh Bxl Byh Byl Cancel.
 assert (U:forall v, Rabs v<=bpow radix2 1016 -> bnd 1 1016 v)
   by (intros v V;unfold bnd;lra).
 destruct (add64_ok 1 1016 xh xl yh yl Xh Xl Yh Yl
   (U _ Bxh) (U _ Bxl) (U _ Byh) (U _ Byl) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
   as [Fh [Fl Values]].
 pose proof (lf_add_normalized (B xh) (B xl) (B yh) (B yl)
   (B_fmt xh) (B_fmt xl) X (B_fmt yh) (B_fmt yl) Y Cancel) as Normal.
 rewrite <-Values in Normal.
 destruct (add64 xh xl yh yl) as [h l] eqn:Output;cbn [fst snd] in *.
 split;[exact Fh|]. split;[exact Fl|]. split;[exact Normal|].
 destruct (Req_dec (B xh+B xl+(B yh+B yl)) 0) as [Zero|Nonzero].
 - destruct (trig_add_zero_words (B xh) (B xl) (B yh) (B yl)
     (B_fmt xh) (B_fmt xl) X (B_fmt yh) (B_fmt yl) Y Cancel Zero)
     as [Hx [Lx [Hy Ly]]].
   rewrite Hx,Lx,Hy,Ly,trig_add_zero in Values. injection Values as H L.
   exists 0;split;[rewrite Rabs_R0;interval|rewrite H,L,Zero;ring].
 - pose proof (add_ieee xh xl yh yl Xh Xl X Yh Yl Y Bxh Bxl Byh Byl Nonzero) as Bound.
   rewrite Output in Bound. destruct Bound as [_ [_ Error]].
   exists ((B h+B l-(B xh+B xl+(B yh+B yl)))/(B xh+B xl+(B yh+B yl))).
   split.
   + eapply Rle_trans;[exact Error|]. unfold prec.
     change (bpow radix2 (-53)) with (/9007199254740992);interval.
   + field;exact Nonzero.
Qed.

Theorem trig_sub_ieee xh xl yh yl :
 finite xh -> finite xl -> B xh=rndF(B xh+B xl) ->
 finite yh -> finite yl -> B yh=rndF(B yh+B yl) ->
 Rabs(B xh)<=bpow radix2 1016 -> Rabs(B xl)<=bpow radix2 1016 ->
 Rabs(B yh)<=bpow radix2 1016 -> Rabs(B yl)<=bpow radix2 1016 ->
 Rabs(B xh)+Rabs(B yh)<=8*Rabs(B xh-B yh) ->
 let '(h,l):=sub64 xh xl yh yl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 exists a, Rabs a<=776/2^114 /\ B h+B l=(B xh+B xl-(B yh+B yl))*(1+a).
Proof.
 intros Xh Xl X Yh Yl Y Bxh Bxl Byh Byl Cancel.
 assert (Nb:forall x, B(fneg x)=-B x) by (intro x;apply B2R_Bopp).
 assert (Nf:forall x, finite x -> finite(fneg x))
   by (intros x Fx;unfold fneg,b64_opp;now rewrite is_finite_Bopp).
 unfold sub64.
 pose proof (trig_add_ieee xh xl (fneg yh) (fneg yl) Xh Xl X (Nf _ Yh) (Nf _ Yl)) as A.
 rewrite !Nb in A.
 replace (B xh+B xl-(B yh+B yl)) with (B xh+B xl+(-B yh+ -B yl)) by ring.
 apply A;try assumption;rewrite ?Rabs_Ropp;try assumption.
 apply dw_opp;exact Y.
Qed.
