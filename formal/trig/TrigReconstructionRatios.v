(** Analytic term budgets for the actual nearest-table reconstruction.
    Bounds are scaled by the exact result, so zero residuals and table row
    zero are included without division by a possibly zero term. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import AsinFacts TrigAccurate.
Open Scope R_scope.

Definition trig_sin_ka_bound : R := 518/2^23.
Definition trig_sin_kb_bound : R := 518/2^9.
Definition trig_cos_ka_bound : R := 522/2^24.
Definition trig_cos_kb_bound : R := 515/2^16.

Lemma trig_sin_magnitude t : Rabs(sin t)<=Rabs t.
Proof.
 pose proof (trig_sin_lipschitz t 0) as Bound.
 rewrite sin_0,!Rminus_0_r in Bound;exact Bound.
Qed.

Lemma trig_cos_minus_one_magnitude t : Rabs t<=1 -> Rabs(cos t-1)<=t*t/2.
Proof.
 intro T. destruct (cos_taylor t T) as [L U].
 apply Rabs_le; lra.
Qed.

Lemma trig_reconstruction_sin_lower a t : /64<=a<=50/64 ->
 Rabs t<=0.0078126 ->
 0<a+t /\ 0.89*(a+t)<=sin(a+t) /\
 (a<=/8 -> 0.99*(a+t)<=sin(a+t)).
Proof.
 intros A T. apply Rabs_le_inv in T.
 assert (Range:0<=a+t<=1) by lra.
 destruct (sin_taylor_pos (a+t) Range) as [L U].
 assert (Square:(a+t)*(a+t)<=0.64) by nra.
 split;[lra|]. split.
 - assert ((a+t)*(a+t)*(a+t)/6<=0.11*(a+t)) by nra. lra.
 - intro Small. assert (S:(a+t)*(a+t)<=0.06) by nra.
   assert ((a+t)*(a+t)*(a+t)/6<=0.01*(a+t)) by nra. lra.
Qed.

Theorem trig_sin_reconstruction_terms a t :
 (a=0 \/ /64<=a<=50/64) -> Rabs t<=0.0078126 ->
 Rabs(sin a*(cos t-1))<=trig_sin_ka_bound*Rabs(sin(a+t)) /\
 Rabs(cos a*sin t)<=trig_sin_kb_bound*Rabs(sin(a+t)).
Proof.
 intros [Zero|A] T.
 - subst a. rewrite sin_0,cos_0,Rplus_0_l,Rmult_0_l,Rmult_1_l,Rabs_R0.
   split;[apply Rmult_le_pos;[unfold trig_sin_ka_bound;interval|apply Rabs_pos]|].
   assert (Budget:1<=trig_sin_kb_bound) by (unfold trig_sin_kb_bound;interval).
   pose proof (Rabs_pos(sin t));nra.
 - destruct (trig_reconstruction_sin_lower a t A T) as [Positive [Lower SmallLower]].
   assert (SinPositive:0<=sin(a+t)) by lra.
   rewrite (Rabs_pos_eq (sin(a+t)) SinPositive).
   assert (SinA:Rabs(sin a)<=a).
   { pose proof (trig_sin_magnitude a) as S;rewrite (Rabs_pos_eq a) in S by lra;exact S. }
   assert (CosA:Rabs(cos a)<=1) by (apply Rabs_le;apply COS_bound).
   pose proof (trig_sin_magnitude t) as SinT.
   assert (CosT:Rabs(cos t-1)<=t*t/2) by (apply trig_cos_minus_one_magnitude;lra).
   assert (First:Rabs(sin a*(cos t-1))<=a*(t*t/2)).
   { rewrite Rabs_mult;apply Rmult_le_compat;try apply Rabs_pos;assumption. }
   assert (Second:Rabs(cos a*sin t)<=Rabs t).
   { rewrite Rabs_mult. pose proof (Rabs_pos(sin t));pose proof (Rabs_pos(cos a));nra. }
   pose proof (Rabs_le_inv t _ T) as RealT.
   assert (Square:t*t<=0.0078126^2) by nra.
   assert (Scaled:a*(t*t/2)<=a*(0.0078126^2/2)) by nra.
   destruct (Rle_dec a (/8)) as [Small|Large].
   + specialize (SmallLower Small).
     assert (Ka:a*(0.0078126^2/2)<=trig_sin_ka_bound*(0.99*(a+t))).
     { unfold trig_sin_ka_bound. cbn [pow];nra. }
     assert (Kb:0.0078126<=trig_sin_kb_bound*(0.99*(a+t))).
     { unfold trig_sin_kb_bound. cbn [pow];nra. }
     assert (Pa:0<=trig_sin_ka_bound) by (unfold trig_sin_ka_bound;interval).
     assert (Pb:0<=trig_sin_kb_bound) by (unfold trig_sin_kb_bound;interval).
     split;nra.
   + assert (Ka:a*(0.0078126^2/2)<=trig_sin_ka_bound*(0.89*(a+t))).
     { unfold trig_sin_ka_bound. cbn [pow];nra. }
     assert (Kb:0.0078126<=trig_sin_kb_bound*(0.89*(a+t))).
     { unfold trig_sin_kb_bound. cbn [pow];nra. }
     assert (Pa:0<=trig_sin_ka_bound) by (unfold trig_sin_ka_bound;interval).
     assert (Pb:0<=trig_sin_kb_bound) by (unfold trig_sin_kb_bound;interval).
     split;nra.
Qed.

Theorem trig_cos_reconstruction_terms a t : 0<=a<=50/64 ->
 Rabs t<=0.0078126 ->
 Rabs(cos a*(cos t-1))<=trig_cos_ka_bound*Rabs(cos(a+t)) /\
 Rabs(sin a*sin t)<=trig_cos_kb_bound*Rabs(cos(a+t)).
Proof.
 intros A T. pose proof (Rabs_le_inv t _ T) as RealT.
 assert (CosA:0<=cos a) by interval.
 assert (CosSum:0.704<=cos(a+t)) by interval.
 assert (SinA:Rabs(sin a)<=0.705) by interval.
 pose proof (trig_cos_lipschitz a (a+t)) as Difference.
 replace (a-(a+t)) with (-t) in Difference by ring.
 rewrite Rabs_Ropp in Difference. apply Rabs_le_inv in Difference.
 assert (CosRatio:cos a<=1.012*cos(a+t)) by lra.
 assert (CosT:Rabs(cos t-1)<=t*t/2) by (apply trig_cos_minus_one_magnitude;lra).
 pose proof (trig_sin_magnitude t) as SinT.
 assert (Square:t*t<=0.0078126^2) by nra.
 assert (First:Rabs(cos a*(cos t-1))<=cos a*(0.0078126^2/2)).
 { rewrite Rabs_mult,(Rabs_pos_eq (cos a) CosA).
   apply Rmult_le_compat_l;[exact CosA|lra]. }
 assert (Second:Rabs(sin a*sin t)<=0.705*0.0078126).
 { rewrite Rabs_mult;apply Rmult_le_compat;try apply Rabs_pos;[exact SinA|lra]. }
 rewrite (Rabs_pos_eq (cos(a+t))) by lra.
 assert (Ka:1.012*(0.0078126^2/2)<=trig_cos_ka_bound) by (unfold trig_cos_ka_bound;interval).
 assert (Kb:0.705*0.0078126<=trig_cos_kb_bound*0.704) by (unfold trig_cos_kb_bound;cbn [pow];lra).
 assert (Pa:0<=trig_cos_ka_bound) by (unfold trig_cos_ka_bound;interval).
 assert (Pb:0<=trig_cos_kb_bound) by (unfold trig_cos_kb_bound;cbn [pow];lra).
 split;nra.
Qed.
