(** Actual IEEE table reconstruction, composed with the analytic error model. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid.
From Interval Require Import Tactic.
Require Import TrigTables TrigTable TrigResidual TrigSinResidual TrigCosResidual
 TrigProducts TrigCancellation TrigInner TrigOuter TrigError TrigReconstructionModel.
Open Scope R_scope.

Definition trig_reconstruct i th tl :=
 let '((sh,sl),(ch,cl)):=trig_table_dw i in
 let '(scm,csn,ccm,ssn):=trig_reconstruction_products i th tl in
 let '(sih,sil):=add64 (fst scm) (snd scm) (fst csn) (snd csn) in
 let '(cih,cil):=sub64 (fst ccm) (snd ccm) (fst ssn) (snd ssn) in
 (add64 sh sl sih sil,add64 ch cl cih cil).

Theorem trig_reconstruct_correct i th tl r :
 (i<51)%nat -> finite th -> finite tl ->
 (B th=0 \/ /2^320<=Rabs(B th)) -> Rabs(B th)<=0.0078126 ->
 Rabs(B tl)<=/2^53*Rabs(B th) -> B th=rndF(B th+B tl) ->
 on_grid (-320) (B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 Rabs r<=0.785399 -> r<>0 ->
 Rabs(IZR(Z.of_nat i)/64+(B th+B tl)-r)<=(3/2)*bpow radix2 (-105)*Rabs r ->
 let '((sh,sl),(ch,cl)):=trig_reconstruct i th tl in
 finite sh /\ finite sl /\ B sh=rndF(B sh+B sl) /\
 finite ch /\ finite cl /\ B ch=rndF(B ch+B cl) /\
 Rabs(B sh+B sl-sin r)<=/2^62*Rabs(sin r) /\
 Rabs(B ch+B cl-cos r)<=/2^62*Rabs(cos r).
Proof.
 intros I Th Tl Domain Upper Low Normal Grid Range R Nonzero Split.
 pose proof (trig_table_dw_ok i I) as [TableS TableC].
 pose proof (trig_sin_residual_correct th tl Th Tl Domain Upper Low Normal Range) as Sin.
 pose proof (trig_cos_residual_correct th tl Th Tl Domain Upper Low Grid Range) as Cos.
 pose proof (trig_reconstruction_products_correct i th tl I Th Tl Domain Upper Low Normal Grid Range) as Products.
 set (a:=IZR(Z.of_nat i)/64) in *;set (t:=B th+B tl) in *.
 assert (A:0<=a<=50/64).
 { unfold a. assert (IZ:0<=IZR(Z.of_nat i)<=50) by (split;apply IZR_le;lia). lra. }
 assert (As:a=0 \/ /64<=a<=50/64).
 { destruct (Nat.eq_dec i 0) as [Zero|Positive].
   - left;unfold a;rewrite Zero;cbn;field.
   - right;split;[|exact (proj2 A)]. unfold a.
     assert (IZ:1<=IZR(Z.of_nat i)) by (apply IZR_le;lia);lra. }
 unfold trig_reconstruct.
 destruct (trig_table_dw i) as [[sh sl][ch cl]] eqn:Table.
 cbn [fst snd] in TableS,TableC.
 destruct (trig_sin_residual th tl) as [snh snl] eqn:Sine.
 destruct (trig_cos_residual th tl) as [cmh cml] eqn:Cosine.
 destruct (trig_reconstruction_products i th tl) as [[[[scmh scml][csnh csnl]][ccmh ccml]][ssnh ssnl]] eqn:Parts.
 cbn [fst snd] in Products |- *.
 destruct Products as [P1 [P2 [P3 P4]]].
 destruct TableS as [Sh [Sl [Sn Se]]]. destruct TableC as [Ch [Cl [Cn Ce]]].
 destruct Sin as [Snh [Snl [Snn Sne]]]. destruct Cos as [Cmh [Cml [Cmn Cme]]].
 unfold trig_table_error in Se,Ce.
 destruct (trig_relative_factor (B sh+B sl) (sin a) (953/2^117) ltac:(interval) Se) as [es [Es Vs]].
 destruct (trig_relative_factor (B ch+B cl) (cos a) (953/2^117) ltac:(interval) Ce) as [ec [Ec Vc]].
 destruct (trig_relative_factor (B snh+B snl) (sin t) (/2^65) ltac:(interval) Sne) as [esn [Esn Vsn]].
 destruct (trig_relative_factor (B cmh+B cml) (cos t-1) (/2^65) ltac:(interval) Cme) as [ecm [Ecm Vcm]].
 assert (Ref1:trig_reference_contract (sin a*(cos t-1)) (scmh,scml)).
 { apply (trig_product_reference (sh,sl) (cmh,cml) scmh scml (sin a) (cos t-1) es ecm);assumption. }
 assert (Ref2:trig_reference_contract (cos a*sin t) (csnh,csnl)).
 { apply (trig_product_reference (ch,cl) (snh,snl) csnh csnl (cos a) (sin t) ec esn);assumption. }
 assert (Ref3:trig_reference_contract (cos a*(cos t-1)) (ccmh,ccml)).
 { apply (trig_product_reference (ch,cl) (cmh,cml) ccmh ccml (cos a) (cos t-1) ec ecm);assumption. }
 assert (Ref4:trig_reference_contract (sin a*sin t) (ssnh,ssnl)).
 { apply (trig_product_reference (sh,sl) (snh,snl) ssnh ssnl (sin a) (sin t) es esn);assumption. }
 pose proof (trig_sine_inner_correct a t scmh scml csnh csnl A Range Ref1 Ref2) as SI.
 pose proof (trig_cosine_inner_correct a t ccmh ccml ssnh ssnl As Range Ref3 Ref4) as CI.
 destruct (add64 scmh scml csnh csnl) as [sih sil].
 destruct (sub64 ccmh ccml ssnh ssnl) as [cih cil].
 destruct SI as [Sih [Sil [SinN [SihB [SilB [sa [Sa Svalue]]]]]]].
 destruct CI as [Cih [Cil [CosN [CihB [CilB [ca [Ca Cvalue]]]]]]].
 assert (Sref:trig_reference_contract (sin a) (sh,sl)).
 { apply (trig_reference_from_error sh sl (sin a) (953/2^117));try assumption;interval. }
 assert (Cref:trig_reference_contract (cos a) (ch,cl)).
 { apply (trig_reference_from_error ch cl (cos a) (953/2^117));try assumption;interval. }
 destruct (trig_reference_magnitudes (sin a) sh sl 1 Sref ltac:(lra)
   ltac:(apply Rabs_le;apply SIN_bound)) as [_ [ShB SlB]].
 destruct (trig_reference_magnitudes (cos a) ch cl 1 Cref ltac:(lra)
   ltac:(apply Rabs_le;apply COS_bound)) as [_ [ChB ClB]].
 destruct Sref as [_ [_ [_ [_ ShError]]]]. destruct Cref as [_ [_ [_ [_ ChError]]]].
 pose proof (trig_sine_head_floor a (B sh) As ShError) as Sfloor.
 pose proof (trig_cosine_head_floor a (B ch) A ChError) as Cfloor.
 pose proof (trig_outer_add_correct sh sl sih sil Sh Sl Sn Sih Sil SinN
   ltac:(lra) ltac:(lra) SihB SilB Sfloor) as Sout.
 assert (Cf:B ch=0 \/ 0.015<=Rabs(B ch)) by (right;clear - Cfloor;lra).
 pose proof (trig_outer_add_correct ch cl cih cil Ch Cl Cn Cih Cil CosN
   ltac:(lra) ltac:(lra) CihB CilB Cf) as Cout.
 destruct (add64 sh sl sih sil) as [oh ol].
 destruct (add64 ch cl cih cil) as [ph pl].
 destruct Sout as [Oh [Ol [On [sb [Sb OutS]]]]].
 destruct Cout as [Ph [Pl [Pn [cb [Cb OutC]]]]].
 destruct P1 as [_ [_ [_ [m1 [M1 V1]]]]]. destruct P2 as [_ [_ [_ [m2 [M2 V2]]]]].
 destruct P3 as [_ [_ [_ [m3 [M3 V3]]]]]. destruct P4 as [_ [_ [_ [m4 [M4 V4]]]]].
 unfold trig_dw_value in V1,V2,V3,V4;cbn [fst snd] in V1,V2,V3,V4.
 assert (SinModel:B oh+B ol=trig_sin_reconstruction_model a t es ec esn ecm m1 m2 sa sb).
 { rewrite OutS,Svalue,V1,V2,Vs,Vc,Vsn,Vcm;reflexivity. }
 assert (CosModel:B ph+B pl=trig_cos_reconstruction_model a t es ec esn ecm m3 m4 ca cb).
 { rewrite OutC,Cvalue,V3,V4,Vs,Vc,Vsn,Vcm;reflexivity. }
 split;[exact Oh|]. split;[exact Ol|]. split;[exact On|].
 split;[exact Ph|]. split;[exact Pl|]. split;[exact Pn|]. split.
 - rewrite SinModel;apply trig_sin_reconstruction_model_correct;assumption.
 - rewrite CosModel;apply trig_cos_reconstruction_model_correct;assumption.
Qed.
