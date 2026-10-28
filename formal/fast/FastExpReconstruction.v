(** Scaled high-word reconstruction, including a subnormal correction product. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingCore RoundingConstant.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal.
Require exp_fast_scaled.
Open Scope R_scope.
Lemma fast_round_absolute v :
 Rabs(rndF v-v)<=bpow radix2(-53)*Rabs v+bpow radix2(-1075).
Proof.
 destruct (Rle_dec (bpow radix2(-1022)) (Rabs v)) as [N|N].
 - pose proof (rnd_rel v N) as E. change (Rabs(rndF v-v)<=bpow radix2(-53)*Rabs v) in E. pose proof (bpow_gt_0 radix2(-1075));lra.
 - assert (E:Rabs(rndF v-v)<=bpow radix2(-1075)).
   { apply (rnd_err_below v (-1021));[lia|].
     eapply Rle_trans with (bpow radix2(-1022));[lra|apply bpow_le;lia]. }
   pose proof (Rabs_pos v);pose proof(bpow_gt_0 radix2(-53));nra.
Qed.
Definition fast_reconstruct64 h u := fadd h (fmul h u).
Lemma fast_reconstruction_budget u dt du ep ey :
 Rabs u<=/1024 -> Rabs dt<=4503599627370498*bpow radix2(-105) ->
 Rabs du<=bpow radix2(-59) -> Rabs ep<=bpow radix2(-58) ->
 Rabs ey<=3*bpow radix2(-54) ->
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
 assert (Hp:0<B h) by (pose proof(bpow_gt_0 radix2(-1016));lra).
 assert (Hb:Rabs(B h)=B h) by (apply Rabs_pos_eq;lra).
 destruct (fmul_bnd 1 1017 h u Fh Fu ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;rewrite Rmult_1_l,Rabs_mult,Hb;
      assert (B h*Rabs(B u)<=B h) by (pose proof(Rabs_pos(B u));nra);lra)) as [Fp [Vp Cp]].
 pose proof (fast_round_absolute (B h*B u)) as Eprod.
 rewrite <-Vp,Rabs_mult,Hb in Eprod.
 assert (Eta:bpow radix2(-1075)<=bpow radix2(-59)*B h).
 { replace (bpow radix2(-1075)) with (bpow radix2(-59)*bpow radix2(-1016))
     by (rewrite <-bpow_plus;reflexivity).
   apply Rmult_le_compat_l;[apply bpow_ge_0|lra]. }
 assert (Ep:Rabs(B(fmul h u)-B h*B u)<=bpow radix2(-58)*B h).
 { bpow_num_all;pose proof(Rabs_pos(B u));nra. }
 pose proof(Rabs_le_inv _ _ Ep) as EpI.
 pose proof(Rabs_le_inv _ _ U) as UI.
 assert (Sum: /2*B h<=B h+B(fmul h u)<=3/2*B h) by (bpow_num_all;nra).
 assert (Spos:0<B h+B(fmul h u)) by nra.
 destruct (fadd_bnd 1 1018 h (fmul h u) Fh Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;
     replace (bpow radix2 1018) with (2*bpow radix2 1017) by (change 2 with(bpow radix2 1);rewrite <-bpow_plus;reflexivity);
     nra)) as [Fy [Vy Cy]].
 assert (N:bpow radix2(-1022)<=Rabs(B h+B(fmul h u))).
 { rewrite Rabs_pos_eq by lra.
   eapply Rle_trans with (/2*bpow radix2(-1016));[bpow_num_all;lra|nra]. }
 pose proof(rnd_rel (B h+B(fmul h u)) N) as Esum.
 change (Rabs(rndF(B h+B(fmul h u))-(B h+B(fmul h u)))<=
   bpow radix2(-53)*Rabs(B h+B(fmul h u))) in Esum.
 rewrite <-Vy,(Rabs_pos_eq (B h+B(fmul h u))) in Esum by lra.
 assert (Ey:Rabs(B(fadd h (fmul h u))-(B h+B(fmul h u)))<=3*bpow radix2(-54)*B h).
 { bpow_num_all;nra. }
 set (ep:=(B(fmul h u)-B h*B u)/B h).
 set (ey:=(B(fadd h (fmul h u))-(B h+B(fmul h u)))/B h).
 assert (Epn:Rabs ep<=bpow radix2(-58)).
 { unfold ep,Rdiv;rewrite Rabs_mult,Rabs_Rinv,Hb by lra.
   apply (Rmult_le_reg_r (B h));[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Ep. }
 assert (Eyn:Rabs ey<=3*bpow radix2(-54)).
 { unfold ey,Rdiv;rewrite Rabs_mult,Rabs_Rinv,Hb by lra.
   apply (Rmult_le_reg_r (B h));[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Ey. }
 pose proof (fast_reconstruction_budget (B u) dt du ep ey U Dt Du Epn Eyn) as Budget.
 assert (Tpos:0<(1+dt)*(1+B u+du)).
 { apply Rabs_le_inv in Dt,Du;bpow_num_all.
   apply Rmult_lt_0_compat;lra. }
 assert (Identity:(B(fadd h(fmul h u))-B h*((1+dt)*(1+B u+du)))/
   (B h*((1+dt)*(1+B u+du)))=
   ((1+B u+ep+ey)-(1+dt)*(1+B u+du))/((1+dt)*(1+B u+du))).
 { unfold ep,ey;field;repeat split;nra. }
 split;[exact Fy|]. unfold fast_reconstruct64;rewrite Identity;exact Budget.
Qed.
