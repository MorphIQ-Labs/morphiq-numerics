(** Reconstruction cancellation budgets, derived from analytic term sizes and
    the proved errors of normalized double-word products. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import TrigMultiply TrigOperandBounds TrigProducts TrigPolynomial
 TrigTables TrigReconstructionRatios.
Open Scope R_scope.

Lemma trig_head_reference h l v : fmtF h -> fmtF l -> h=rndF(h+l) ->
 Rabs(h+l-v)<=/2^60*Rabs v -> Rabs(h-v)<=/2^50*Rabs v.
Proof.
 intros H L N Error.
 destruct (trig_dw_head_magnitude h l v (/2^60) H L N ltac:(interval) Error)
   as [_ [Head Low]].
 pose proof (Rabs_triang (h+l-v) (-l)) as T.
 replace (h+l-v+ -l) with (h-v) in T by ring;rewrite Rabs_Ropp in T.
 pose proof (Rabs_pos v) as P. clear - Error Head Low T P. unfold trig_mul_u in *;lra.
Qed.

Lemma trig_dw_word_upper h l bound : fmtF h -> fmtF l -> h=rndF(h+l) ->
 0<=bound -> Rabs(h+l)<=bound ->
 Rabs h<=1.01*bound /\ Rabs l<=trig_mul_u*(1.01*bound).
Proof.
 intros H L N P Upper. pose proof (trig_dw_low h l H L N) as Low.
 pose proof (Rabs_triang (h+l) (-l)) as T.
 replace (h+l+ -l) with h in T by ring;rewrite Rabs_Ropp in T.
 clear - Upper Low T P;unfold trig_mul_u in *;split;lra.
Qed.

Lemma trig_product_reference x y h l v w ex ey :
 trig_product_contract x y (h,l) ->
 Rabs ex<=953/2^117 -> Rabs ey<=/2^65 ->
 trig_dw_value x=v*(1+ex) -> trig_dw_value y=w*(1+ey) ->
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-v*w)<=/2^60*Rabs(v*w) /\
 Rabs(B h-v*w)<=/2^50*Rabs(v*w).
Proof.
 intros [H [L [N [m [M Value]]]]] Ex Ey X Y.
 rewrite X,Y in Value.
 assert (Factor:Rabs((1+ex)*(1+ey)*(1+m)-1)<=/2^60) by (interval with (i_prec 180)).
 assert (Error:Rabs(B h+B l-v*w)<=/2^60*Rabs(v*w)).
 { rewrite Value. replace (v*(1+ex)*(w*(1+ey))*(1+m)-v*w) with
     (((1+ex)*(1+ey)*(1+m)-1)*(v*w)) by ring.
   rewrite Rabs_mult;apply Rmult_le_compat_r;[apply Rabs_pos|exact Factor]. }
 split;[exact H|]. split;[exact L|]. split;[exact N|]. split;[exact Error|].
 apply (trig_head_reference (B h) (B l));try apply B_fmt;assumption.
Qed.

Lemma trig_head_dominance x y v w :
 Rabs(x-v)<=/2^50*Rabs v -> Rabs(y-w)<=/2^50*Rabs w ->
 Rabs v<=0.6*Rabs w -> Rabs x<=0.75*Rabs y.
Proof.
 intros X Y Dominant.
 pose proof (Rabs_triang (x-v) v) as Tx.
 replace (x-v+v) with x in Tx by ring.
 pose proof (Rabs_triang (w-y) y) as Ty.
 replace (w-y+y) with w in Ty by ring;rewrite Rabs_minus_sym in Ty.
 pose proof (Rabs_pos w);lra.
Qed.

Lemma trig_dominant_cancellation x y : Rabs x<=0.75*Rabs y ->
 Rabs x+Rabs y<=8*Rabs(x+y) /\ Rabs x+Rabs y<=8*Rabs(x-y).
Proof.
 intro D.
 pose proof (Rabs_triang (x+y) (-x)) as Plus.
 replace (x+y+ -x) with y in Plus by ring;rewrite Rabs_Ropp in Plus.
 pose proof (Rabs_triang (x-y) (-x)) as Minus.
 replace (x-y+ -x) with (-y) in Minus by ring;rewrite !Rabs_Ropp in Minus.
 pose proof (Rabs_pos y);split;lra.
Qed.

Lemma trig_zero_cancellation x y : x=0 \/ y=0 ->
 Rabs x+Rabs y<=8*Rabs(x+y) /\ Rabs x+Rabs y<=8*Rabs(x-y).
Proof.
 intros [X|Y].
 - subst x;rewrite Rabs_R0,!Rplus_0_l.
   replace (0-y) with (-y) by ring;rewrite Rabs_Ropp.
   pose proof (Rabs_pos y);split;lra.
 - subst y;rewrite Rabs_R0,!Rplus_0_r,Rminus_0_r.
   pose proof (Rabs_pos x);split;lra.
Qed.

Lemma trig_small_sin_lower t : Rabs t<=0.0078126 -> 0.9*Rabs t<=Rabs(sin t).
Proof.
 intro T. destruct (trig_sin_polynomial_model t T) as [al [Al Value]].
 assert (Factor:0.9<=1+t*t*trig_ps(t*t)*(1+al)).
 { unfold trig_ps,trig_poly_error in *;rewrite trig_s0_val,trig_s1_val,trig_s2_val;interval. }
 rewrite Value. replace (t+t^3*trig_ps(t*t)*(1+al)) with (t*(1+t*t*trig_ps(t*t)*(1+al))) by ring.
 rewrite Rabs_mult,(Rabs_pos_eq (1+t*t*trig_ps(t*t)*(1+al))) by lra.
 pose proof (Rabs_pos t);nra.
Qed.

Lemma trig_residual_square_upper t : Rabs t<=0.0078126 -> t*t<=0.0078126*Rabs t.
Proof.
 intro T. assert (Square:Rabs t*Rabs t=t*t).
 { rewrite <-Rabs_mult;apply Rabs_pos_eq;apply Rle_0_sqr. }
 pose proof (Rabs_pos t);nra.
Qed.

Lemma trig_sine_product_dominance a t : 0<=a<=50/64 -> Rabs t<=0.0078126 ->
 Rabs(sin a*(cos t-1))<=0.6*Rabs(cos a*sin t).
Proof.
 intros A T.
 assert (Sa:Rabs(sin a)<=1) by (apply Rabs_le;apply SIN_bound).
 assert (Ca:0.7<=Rabs(cos a)) by interval.
 pose proof (trig_small_sin_lower t T) as St.
 assert (Ct:Rabs(cos t-1)<=t*t/2) by (apply trig_cos_minus_one_magnitude;lra).
 pose proof (trig_residual_square_upper t T) as Square.
 assert (First:Rabs(sin a*(cos t-1))<=t*t/2).
 { rewrite Rabs_mult. pose proof (Rabs_pos(cos t-1));pose proof (Rabs_pos(sin a));nra. }
 assert (Second:0.63*Rabs t<=Rabs(cos a*sin t)).
 { rewrite Rabs_mult. pose proof (Rabs_pos t);pose proof (Rabs_pos(sin t));nra. }
 pose proof (Rabs_pos t) as P;clear - First Second Square P;lra.
Qed.

Lemma trig_cosine_product_dominance a t : /64<=a<=50/64 -> Rabs t<=0.0078126 ->
 Rabs(cos a*(cos t-1))<=0.6*Rabs(sin a*sin t).
Proof.
 intros A T.
 assert (Sa:0.015<=Rabs(sin a)) by interval.
 assert (Ca:Rabs(cos a)<=1) by (apply Rabs_le;apply COS_bound).
 pose proof (trig_small_sin_lower t T) as St.
 assert (Ct:Rabs(cos t-1)<=t*t/2) by (apply trig_cos_minus_one_magnitude;lra).
 pose proof (trig_residual_square_upper t T) as Square.
 assert (First:Rabs(cos a*(cos t-1))<=t*t/2).
 { rewrite Rabs_mult. pose proof (Rabs_pos(cos t-1));pose proof (Rabs_pos(cos a));nra. }
 assert (Second:0.0135*Rabs t<=Rabs(sin a*sin t)).
 { rewrite Rabs_mult. pose proof (Rabs_pos t);pose proof (Rabs_pos(sin t));nra. }
 pose proof (Rabs_pos t) as P;clear - First Second Square P;lra.
Qed.

Definition trig_reference_contract v (p:f64*f64) :=
 let '(h,l):=p in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-v)<=/2^60*Rabs v /\ Rabs(B h-v)<=/2^50*Rabs v.

Lemma trig_reference_from_error h l v eps : finite h -> finite l ->
 B h=rndF(B h+B l) -> eps<=/2^60 ->
 Rabs(B h+B l-v)<=eps*Rabs v -> trig_reference_contract v (h,l).
Proof.
 intros H L N E Error.
 assert (Error':Rabs(B h+B l-v)<=/2^60*Rabs v).
 { eapply Rle_trans;[exact Error|];apply Rmult_le_compat_r;[apply Rabs_pos|exact E]. }
 unfold trig_reference_contract.
 split;[exact H|]. split;[exact L|]. split;[exact N|]. split;[exact Error'|].
 apply (trig_head_reference (B h) (B l));try apply B_fmt;assumption.
Qed.

Lemma trig_reference_magnitudes v h l bound : trig_reference_contract v (h,l) ->
 0<=bound -> Rabs v<=bound ->
 Rabs(B h+B l)<=1.01*bound /\ Rabs(B h)<=1.01*bound /\ Rabs(B l)<=1.01*bound.
Proof.
 intros [H [L [N [Error HeadError]]]] P Upper.
 pose proof (trig_dw_low (B h) (B l) (B_fmt h) (B_fmt l) N) as Low.
 pose proof (Rabs_triang (B h+B l-v) v) as Full.
 replace (B h+B l-v+v) with (B h+B l) in Full by ring.
 pose proof (Rabs_triang (B h-v) v) as Head.
 replace (B h-v+v) with (B h) in Head by ring.
 clear - Error HeadError Upper Low P Full Head.
 unfold trig_mul_u in *;split;[|split];lra.
Qed.
