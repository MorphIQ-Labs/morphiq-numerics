(** The existing reconstruction certificates, with every error allowance
    explicit. Analytic term budgets and the Q256 split effect are proved
    separately; arithmetic errors describe the chosen double-word operations. *)
From Coq Require Import Reals ZArith Lra.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
Require Import StageGappa TrigReconstructionRatios.
Require trig_fast_sin trig_fast_cos.
Open Scope R_scope.

Definition trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er :=
 ((1-ka-kb)*(1+es)+
   (ka*((1+es)*(1+ecm)*(1+m1))+kb*((1+ec)*(1+esn)*(1+m2)))*(1+a1))*(1+a2)*(1+er).
Definition trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er :=
 ((1-ka+kb)*(1+ec)+
   (ka*((1+ec)*(1+ecm)*(1+m1))-kb*((1+es)*(1+esn)*(1+m2)))*(1+a1))*(1+a2)*(1+er).

Lemma trig_sin_reconstruction_certificate ka kb es ec esn ecm m1 m2 a1 a2 er :
 Rabs ka<=trig_sin_ka_bound -> Rabs kb<=trig_sin_kb_bound ->
 Rabs es<=953/2^117 -> Rabs ec<=953/2^117 ->
 Rabs esn<=/2^65 -> Rabs ecm<=/2^65 ->
 Rabs m1<=9/2^106 -> Rabs m2<=9/2^106 ->
 Rabs a1<=776/2^114 -> Rabs a2<=776/2^114 -> Rabs er<=/2^104 ->
 Rabs(trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)<=/2^62.
Proof.
 intros Ka Kb Es Ec Esn Ecm M1 M2 A1 A2 Er.
 apply Rabs_le_inv in Ka,Kb,Es,Ec,Esn,Ecm,M1,M2,A1,A2,Er.
 unfold trig_sin_ka_bound in Ka;unfold trig_sin_kb_bound in Kb.
 assert (G:BND (trig_sin_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)
   (makepairF (Float2 (-1) (-62)) (Float2 1 (-62)))).
 { unfold trig_sin_reconstruction_factor.
   gappa_goal (trig_fast_sin.l1 ka kb es ecm m1 ec esn m2 a1 a2 er). }
 apply bnd_to in G. destruct G as [L U]. bpow_num_all. apply Rabs_le;lra.
Qed.

Lemma trig_cos_reconstruction_certificate ka kb es ec esn ecm m1 m2 a1 a2 er :
 Rabs ka<=trig_cos_ka_bound -> Rabs kb<=trig_cos_kb_bound ->
 Rabs es<=953/2^117 -> Rabs ec<=953/2^117 ->
 Rabs esn<=/2^65 -> Rabs ecm<=/2^65 ->
 Rabs m1<=9/2^106 -> Rabs m2<=9/2^106 ->
 Rabs a1<=776/2^114 -> Rabs a2<=776/2^114 -> Rabs er<=/2^104 ->
 Rabs(trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)<=/2^62.
Proof.
 intros Ka Kb Es Ec Esn Ecm M1 M2 A1 A2 Er.
 apply Rabs_le_inv in Ka,Kb,Es,Ec,Esn,Ecm,M1,M2,A1,A2,Er.
 unfold trig_cos_ka_bound in Ka;unfold trig_cos_kb_bound in Kb.
 assert (G:BND (trig_cos_reconstruction_factor ka kb es ec esn ecm m1 m2 a1 a2 er-1)
   (makepairF (Float2 (-1) (-62)) (Float2 1 (-62)))).
 { unfold trig_cos_reconstruction_factor.
   gappa_goal (trig_fast_cos.l1 ka kb ec ecm m1 es esn m2 a1 a2 er). }
 apply bnd_to in G. destruct G as [L U]. bpow_num_all. apply Rabs_le;lra.
Qed.
