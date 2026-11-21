(** Reconstruction models with analytic table/residual references. Every
    arithmetic error remains an explicit premise to bind to the executable
    double-word operations; the analytic ratios and split effect are derived. *)
From Coq Require Import Reals ZArith Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import TrigReconstructionRatios TrigSplitAnalytic TrigReconstructionCertificate.
Open Scope R_scope.

Definition trig_sin_reconstruction_model a t es ec esn ecm m1 m2 a1 a2 :=
 (sin a*(1+es)+
  ((sin a*(1+es)*((cos t-1)*(1+ecm)))*(1+m1)+
   (cos a*(1+ec)*(sin t*(1+esn)))*(1+m2))*(1+a1))*(1+a2).
Definition trig_cos_reconstruction_model a t es ec esn ecm m1 m2 a1 a2 :=
 (cos a*(1+ec)+
  ((cos a*(1+ec)*((cos t-1)*(1+ecm)))*(1+m1)-
   (sin a*(1+es)*(sin t*(1+esn)))*(1+m2))*(1+a1))*(1+a2).

Lemma trig_reconstruction_ratio_bound x y e : y<>0 -> Rabs x<=e*Rabs y ->
 Rabs(x/y)<=e.
Proof.
 intros Nonzero Bound. unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact Nonzero.
 apply (Rmult_le_reg_r (Rabs y));[apply Rabs_pos_lt;exact Nonzero|].
 rewrite Rmult_assoc,Rinv_l,Rmult_1_r by (apply Rabs_no_R0;exact Nonzero). exact Bound.
Qed.

Theorem trig_sin_reconstruction_model_correct a t r es ec esn ecm m1 m2 a1 a2 :
 (a=0 \/ /64<=a<=50/64) -> Rabs t<=0.0078126 ->
 Rabs r<=0.785399 -> r<>0 -> Rabs(a+t-r)<=(3/2)*bpow radix2 (-105)*Rabs r ->
 Rabs es<=953/2^117 -> Rabs ec<=953/2^117 ->
 Rabs esn<=/2^65 -> Rabs ecm<=/2^65 ->
 Rabs m1<=9/2^106 -> Rabs m2<=9/2^106 ->
 Rabs a1<=776/2^114 -> Rabs a2<=776/2^114 ->
 Rabs(trig_sin_reconstruction_model a t es ec esn ecm m1 m2 a1 a2-sin r)<=/2^62*Rabs(sin r).
Proof.
 intros A T R Nonzero Split Es Ec Esn Ecm M1 M2 A1 A2.
 destruct (trig_sin_reconstruction_terms a t A T) as [Ta Tb].
 assert (Nz:sin(a+t)<>0) by (apply (trig_split_sine_nonzero r);assumption).
 destruct (trig_split_analytic_factors r (a+t) R Split) as [[er [Er Value]] _].
 assert (Er':Rabs er<=/2^104).
 { change (bpow radix2 (-104)) with (/20282409603651670423947251286016) in Er.
   replace (/2^104) with (/20282409603651670423947251286016) by (f_equal;ring);exact Er. }
 set (ka:=sin a*(cos t-1)/sin(a+t)).
 set (kb:=cos a*sin t/sin(a+t)).
 assert (Ka:Rabs ka<=trig_sin_ka_bound) by (apply trig_reconstruction_ratio_bound;assumption).
 assert (Kb:Rabs kb<=trig_sin_kb_bound) by (apply trig_reconstruction_ratio_bound;assumption).
 pose proof (trig_sin_reconstruction_certificate ka kb es ec esn ecm m1 m2 a1 a2 er
   Ka Kb Es Ec Esn Ecm M1 M2 A1 A2 Er') as Certificate.
 assert (TermA:sin a*(cos t-1)=sin(a+t)*ka) by (unfold ka;field;exact Nz).
 assert (TermB:cos a*sin t=sin(a+t)*kb) by (unfold kb;field;exact Nz).
 assert (Leading:sin a=sin(a+t)*(1-ka-kb)).
 { pose proof (sin_plus a t) as Addition. clear - TermA TermB Addition; nra. }
 assert (Model:trig_sin_reconstruction_model a t es ec esn ecm m1 m2 a1 a2=
   sin r*trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er).
 { unfold trig_sin_reconstruction_model,trig_sin_reconstruction_factor.
   replace (sin a*(1+es)*((cos t-1)*(1+ecm))*(1+m1)) with
     ((sin a*(cos t-1))*((1+es)*(1+ecm)*(1+m1))) by ring.
   replace (cos a*(1+ec)*(sin t*(1+esn))*(1+m2)) with
     ((cos a*sin t)*((1+ec)*(1+esn)*(1+m2))) by ring.
   rewrite TermA,TermB,Leading,Value. ring. }
 rewrite Model. replace (sin r*trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-sin r)
  with ((trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)*sin r) by ring.
 rewrite Rabs_mult. apply Rmult_le_compat_r;[apply Rabs_pos|exact Certificate].
Qed.

Theorem trig_cos_reconstruction_model_correct a t r es ec esn ecm m1 m2 a1 a2 :
 0<=a<=50/64 -> Rabs t<=0.0078126 ->
 Rabs r<=0.785399 -> Rabs(a+t-r)<=(3/2)*bpow radix2 (-105)*Rabs r ->
 Rabs es<=953/2^117 -> Rabs ec<=953/2^117 ->
 Rabs esn<=/2^65 -> Rabs ecm<=/2^65 ->
 Rabs m1<=9/2^106 -> Rabs m2<=9/2^106 ->
 Rabs a1<=776/2^114 -> Rabs a2<=776/2^114 ->
 Rabs(trig_cos_reconstruction_model a t es ec esn ecm m1 m2 a1 a2-cos r)<=/2^62*Rabs(cos r).
Proof.
 intros A T R Split Es Ec Esn Ecm M1 M2 A1 A2.
 destruct (trig_cos_reconstruction_terms a t A T) as [Ta Tb].
 pose proof (Rabs_le_inv t _ T) as RealT.
 assert (Positive:0.704<=cos(a+t)) by interval.
 assert (Nz:cos(a+t)<>0) by lra.
 destruct (trig_split_analytic_factors r (a+t) R Split) as [_ [er [Er Value]]].
 assert (Er':Rabs er<=/2^104).
 { change (bpow radix2 (-104)) with (/20282409603651670423947251286016) in Er.
   replace (/2^104) with (/20282409603651670423947251286016) by (f_equal;ring);exact Er. }
 set (ka:=cos a*(cos t-1)/cos(a+t)).
 set (kb:=sin a*sin t/cos(a+t)).
 assert (Ka:Rabs ka<=trig_cos_ka_bound) by (apply trig_reconstruction_ratio_bound;assumption).
 assert (Kb:Rabs kb<=trig_cos_kb_bound) by (apply trig_reconstruction_ratio_bound;assumption).
 pose proof (trig_cos_reconstruction_certificate ka kb es ec esn ecm m1 m2 a1 a2 er
   Ka Kb Es Ec Esn Ecm M1 M2 A1 A2 Er') as Certificate.
 assert (TermA:cos a*(cos t-1)=cos(a+t)*ka) by (unfold ka;field;exact Nz).
 assert (TermB:sin a*sin t=cos(a+t)*kb) by (unfold kb;field;exact Nz).
 assert (Leading:cos a=cos(a+t)*(1-ka+kb)).
 { pose proof (cos_plus a t) as Addition. clear - TermA TermB Addition; nra. }
 assert (Model:trig_cos_reconstruction_model a t es ec esn ecm m1 m2 a1 a2=
   cos r*trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er).
 { unfold trig_cos_reconstruction_model,trig_cos_reconstruction_factor.
   replace (cos a*(1+ec)*((cos t-1)*(1+ecm))*(1+m1)) with
     ((cos a*(cos t-1))*((1+ec)*(1+ecm)*(1+m1))) by ring.
   replace (sin a*(1+es)*(sin t*(1+esn))*(1+m2)) with
     ((sin a*sin t)*((1+es)*(1+esn)*(1+m2))) by ring.
   rewrite TermA,TermB,Leading,Value. ring. }
 rewrite Model. replace (cos r*trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-cos r)
  with ((trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)*cos r) by ring.
 rewrite Rabs_mult. apply Rmult_le_compat_r;[apply Rabs_pos|exact Certificate].
Qed.
