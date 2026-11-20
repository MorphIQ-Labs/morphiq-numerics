(** Outer table-plus-correction additions, with cancellation premises proved
    from the table's reference error and the inner correction's word bounds. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import TrigAdd TrigCancellation.
Open Scope R_scope.

Lemma trig_sine_head_floor a h : (a=0 \/ /64<=a<=50/64) ->
 Rabs(h-sin a)<=/2^50*Rabs(sin a) -> h=0 \/ 0.015<=Rabs h.
Proof.
 intros [Zero|A] Error.
 - rewrite Zero,sin_0,Rabs_R0,Rmult_0_r,Rminus_0_r in Error.
   left;apply Rabs_le_inv in Error;lra.
 - assert (Lower:0.0156<=Rabs(sin a)) by interval.
   assert (Upper:Rabs(sin a)<=1) by (apply Rabs_le;apply SIN_bound).
   pose proof (Rabs_triang (sin a-h) h) as T.
   replace (sin a-h+h) with (sin a) in T by ring;rewrite Rabs_minus_sym in T.
   right;lra.
Qed.

Lemma trig_cosine_head_floor a h : 0<=a<=50/64 ->
 Rabs(h-cos a)<=/2^50*Rabs(cos a) -> 0.7<=Rabs h.
Proof.
 intros A Error.
 assert (Lower:0.709<=Rabs(cos a)) by interval.
 assert (Upper:Rabs(cos a)<=1) by (apply Rabs_le;apply COS_bound).
 pose proof (Rabs_triang (cos a-h) h) as T.
 replace (cos a-h+h) with (cos a) in T by ring;rewrite Rabs_minus_sym in T.
 lra.
Qed.

Lemma trig_outer_cancellation sh ih : (sh=0 \/ 0.015<=Rabs sh) -> Rabs ih<=0.009 ->
 Rabs sh+Rabs ih<=8*Rabs(sh+ih).
Proof.
 intros [Zero|Lower] Upper.
 - exact (proj1(trig_zero_cancellation _ _ (or_introl Zero))).
 - assert (Dominant:Rabs ih<=0.75*Rabs sh) by lra.
   pose proof (proj1(trig_dominant_cancellation ih sh Dominant)) as C.
   rewrite (Rplus_comm ih sh) in C;lra.
Qed.

Theorem trig_outer_add_correct sh sl ih il :
 finite sh -> finite sl -> B sh=rndF(B sh+B sl) ->
 finite ih -> finite il -> B ih=rndF(B ih+B il) ->
 Rabs(B sh)<=2 -> Rabs(B sl)<=2 -> Rabs(B ih)<=0.009 -> Rabs(B il)<=0.009 ->
 (B sh=0 \/ 0.015<=Rabs(B sh)) ->
 let '(h,l):=add64 sh sl ih il in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 exists d, Rabs d<=776/2^114 /\ B h+B l=(B sh+B sl+(B ih+B il))*(1+d).
Proof.
 intros Sh Sl S Ih Il I Bsh Bsl Bih Bil Floor.
 assert (Cancel:Rabs(B sh)+Rabs(B ih)<=8*Rabs(B sh+B ih))
   by (apply trig_outer_cancellation;assumption).
 assert (Wide:2<=bpow radix2 1016) by (change 2 with (bpow radix2 1);apply bpow_le;lia).
 apply trig_add_ieee;try assumption;lra.
Qed.
