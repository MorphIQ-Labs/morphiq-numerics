(** Reconstruct after adding one, avoiding a subnormal correction product. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingCore RoundingConstant.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal.
Require exp_fast_scaled.
Open Scope R_scope.
Definition fast_reconstruct64 h u := fmul h (fadd one u).
Lemma fast_reconstruction_budget u dt du ep ey :
 Rabs u<=/1024 -> Rabs dt<=4503599627370498*bpow radix2(-105) ->
 Rabs du<=bpow radix2(-59) -> Rabs ep<=1025*bpow radix2(-63) ->
 Rabs ey<=1026*bpow radix2(-63) ->
 Rabs(((1+u+ep+ey)-(1+dt)*(1+u+du))/((1+dt)*(1+u+du)))<=bpow radix2(-51).
Proof.
 intros U Dt Du Ep Ey. apply Rabs_le_inv in U,Dt,Du,Ep,Ey.
 apply Rabs_le;erfcx_goal (exp_fast_scaled.l1 u ep ey dt du).
Qed.
Theorem fast_reconstruction_ok h u dt du : finite h -> finite u ->
 bpow radix2(-1016)<=B h<=bpow radix2 1017 -> Rabs(B u)<=/1024 ->
 Rabs dt<=4503599627370498*bpow radix2(-105) -> Rabs du<=bpow radix2(-59) ->
 finite(fast_reconstruct64 h u) /\
 Rabs((B(fast_reconstruct64 h u)-B h*((1+dt)*(1+B u+du)))/
   (B h*((1+dt)*(1+B u+du))))<=bpow radix2(-51).
Proof.
 intros Fh Fu H U Dt Du.
 destruct one_ok as [Fo Vo].
 pose proof(Rabs_le_inv _ _ U) as UI.
 assert (Hp:0<B h) by (pose proof(bpow_gt_0 radix2(-1016));lra).
 assert (Hb:Rabs(B h)=B h) by (apply Rabs_pos_eq;lra).
 destruct (fadd_bnd 1 1 one u Fo Fu ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;rewrite Vo;apply Rabs_le;bpow_num_all;lra)) as [Fs [Vs Cs]].
 rewrite Vo in Vs.
 assert (Spos:0<1+B u) by lra.
 assert (Sn:bpow radix2(-1022)<=Rabs(1+B u)).
 { rewrite Rabs_pos_eq by lra. eapply Rle_trans with (/2);[bpow_num_all;lra|lra]. }
 pose proof(rnd_rel (1+B u) Sn) as Es.
 change (Rabs(rndF(1+B u)-(1+B u))<=bpow radix2(-53)*Rabs(1+B u)) in Es.
 rewrite <-Vs,(Rabs_pos_eq (1+B u)) in Es by lra.
 assert (Ep:Rabs(B(fadd one u)-(1+B u))<=1025*bpow radix2(-63)).
 { eapply Rle_trans;[exact Es|]. bpow_num_all;nra. }
 pose proof(Rabs_le_inv _ _ Ep) as EI.
 assert (Srange:/2<=B(fadd one u)<=1026/1024) by (bpow_num_all;lra).
 assert (Ppos:0<B h*B(fadd one u)) by nra.
 destruct (fmul_bnd 1 1018 h (fadd one u) Fh Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;
     replace (bpow radix2 1018) with (2*bpow radix2 1017) by (change 2 with(bpow radix2 1);rewrite <-bpow_plus;reflexivity);
     nra)) as [Fy [Vy Cy]].
 assert (Pn:bpow radix2(-1022)<=Rabs(B h*B(fadd one u))).
 { rewrite Rabs_pos_eq by lra.
   eapply Rle_trans with (/2*bpow radix2(-1016));[bpow_num_all;lra|nra]. }
 pose proof(rnd_rel (B h*B(fadd one u)) Pn) as Ey.
 change (Rabs(rndF(B h*B(fadd one u))-B h*B(fadd one u))<=
   bpow radix2(-53)*Rabs(B h*B(fadd one u))) in Ey.
 rewrite <-Vy,(Rabs_pos_eq (B h*B(fadd one u))) in Ey by lra.
 assert (Eybound:Rabs(B(fmul h(fadd one u))-B h*B(fadd one u))<=1026*bpow radix2(-63)*B h).
 { eapply Rle_trans;[exact Ey|]. bpow_num_all;nra. }
 set (ep:=B(fadd one u)-(1+B u)).
 set (ey:=(B(fmul h(fadd one u))-B h*B(fadd one u))/B h).
 assert (Eyn:Rabs ey<=1026*bpow radix2(-63)).
 { unfold ey,Rdiv;rewrite Rabs_mult,Rabs_Rinv,Hb by lra.
   apply (Rmult_le_reg_r (B h));[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Eybound. }
 pose proof (fast_reconstruction_budget (B u) dt du ep ey U Dt Du Ep Eyn) as Budget.
 assert (Tpos:0<(1+dt)*(1+B u+du)).
 { apply Rabs_le_inv in Dt,Du;bpow_num_all.
   apply Rmult_lt_0_compat;lra. }
 assert (Identity:(B(fmul h(fadd one u))-B h*((1+dt)*(1+B u+du)))/
   (B h*((1+dt)*(1+B u+du)))=
   ((1+B u+ep+ey)-(1+dt)*(1+B u+du))/((1+dt)*(1+B u+du))).
 { unfold ep,ey;field;repeat split;nra. }
 split;[exact Fy|]. unfold fast_reconstruct64;rewrite Identity;exact Budget.
Qed.
