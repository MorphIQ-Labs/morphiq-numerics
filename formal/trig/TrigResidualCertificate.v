(** Compose the analytic polynomial models with the residual certificates. *)
From Coq Require Import Reals ZArith Lra Psatz.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigPolynomial TrigTail.
Require trig_sin_t trig_cos_t.
Open Scope R_scope.

Lemma trig_sin_residual_certificate th dl al et d2 :
 /2^60<=Rabs th<=0.0078126 -> Rabs dl<=/2^53 ->
 Rabs al<=trig_poly_error -> Rabs et<=/2^50 -> Rabs d2<=/2^105 ->
 let t:=th*(1+dl) in
 let st:=t+t*t*t*trig_ps(t*t)*(1+al) in
 let sn:=(t+th*th*th*trig_ps(th*th)*(1+et))*(1+d2) in
 Rabs((sn-st)/st)<=/2^65.
Proof.
 intros T Dl Al Et D2 t st sn.
 apply Rabs_le_inv in Dl,Al,Et,D2. unfold trig_poly_error in Al.
 destruct trig_coefficient_gappa_values as [S0 [S1 [S2 _]]].
 assert (G:BND ((sn-st)/st) (makepairF (Float2 (-1) (-65)) (Float2 1 (-65)))).
 { subst t st sn. unfold trig_ps. rewrite S0,S1,S2.
   gappa_goal (trig_sin_t.l1 th dl al et d2). }
 apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all. apply Rabs_le; lra.
Qed.

Lemma trig_cos_residual_certificate th dl al et ec eu d2 :
 /2^60<=Rabs th<=0.0078126 -> Rabs dl<=/2^53 ->
 Rabs al<=trig_poly_error -> Rabs et<=/2^50 ->
 Rabs ec<=/2^53 -> Rabs eu<=/2^53 -> Rabs d2<=/2^105 ->
 let t:=th*(1+dl) in
 let ct:=-(t*t/2)+t*t*t*t*trig_pc(t*t)*(1+al) in
 let v:=(th*th*th*th*trig_pc(th*th)*(1+et)-th*th*dl*(1+ec))*(1+eu) in
 let cm:=(-(th*th/2)+v)*(1+d2) in
 Rabs((cm-ct)/ct)<=/2^65.
Proof.
 intros T Dl Al Et Ec Eu D2 t ct v cm.
 apply Rabs_le_inv in Dl,Al,Et,Ec,Eu,D2. unfold trig_poly_error in Al.
 destruct trig_coefficient_gappa_values as [_ [_ [_ [C0 [C1 C2]]]]].
 assert (G:BND ((cm-ct)/ct) (makepairF (Float2 (-1) (-65)) (Float2 1 (-65)))).
 { subst t ct v cm. unfold trig_pc. rewrite C0,C1,C2.
   gappa_goal (trig_cos_t.l1 th dl al et ec eu d2). }
 apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all. apply Rabs_le; lra.
Qed.

Theorem trig_sin_residual_model th dl et d2 :
 /2^60<=Rabs th<=0.0078126 -> Rabs dl<=/2^53 ->
 Rabs et<=/2^50 -> Rabs d2<=/2^105 -> Rabs(th*(1+dl))<=0.0078126 ->
 let t:=th*(1+dl) in
 Rabs(((t+th^3*trig_ps(th*th)*(1+et))*(1+d2)-sin t)/sin t)<=/2^65.
Proof.
 intros T Dl Et D2 Range t.
 destruct (trig_sin_polynomial_model t Range) as [al [Al Analytic]].
 pose proof (trig_sin_residual_certificate th dl al et d2 T Dl Al Et D2) as Bound.
 change (Rabs (((t+th*th*th*trig_ps(th*th)*(1+et))*(1+d2)-
   (t+t*t*t*trig_ps(t*t)*(1+al)))/(t+t*t*t*trig_ps(t*t)*(1+al)))<=/2^65) in Bound.
 replace (th*th*th) with (th^3) in Bound by ring.
 replace (t*t*t) with (t^3) in Bound by ring.
 rewrite <-Analytic in Bound. exact Bound.
Qed.

Theorem trig_cos_residual_model th dl et ec eu d2 :
 /2^60<=Rabs th<=0.0078126 -> Rabs dl<=/2^53 -> Rabs et<=/2^50 ->
 Rabs ec<=/2^53 -> Rabs eu<=/2^53 -> Rabs d2<=/2^105 ->
 Rabs(th*(1+dl))<=0.0078126 ->
 let t:=th*(1+dl) in
 let v:=(th^4*trig_pc(th*th)*(1+et)-th*th*dl*(1+ec))*(1+eu) in
 Rabs(((-(th*th/2)+v)*(1+d2)-(cos t-1))/(cos t-1))<=/2^65.
Proof.
 intros T Dl Et Ec Eu D2 Range t v.
 destruct (trig_cos_polynomial_model t Range) as [al [Al Analytic]].
 pose proof (trig_cos_residual_certificate th dl al et ec eu d2 T Dl Al Et Ec Eu D2) as Bound.
 cbv zeta in Bound. fold t in Bound.
 replace (th*th*th*th) with (th^4) in Bound by ring. fold v in Bound.
 replace (t*t*t*t) with (t^4) in Bound by ring.
 replace (-(t*t/2)+t^4*trig_pc(t*t)*(1+al)) with (cos t-1) in Bound by lra.
 exact Bound.
Qed.
