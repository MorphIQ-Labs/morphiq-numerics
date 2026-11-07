(** Private radius logarithm: comparison with the certified full stage. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings RoundingTest.
From Interval Require Import Tactic.
Require Import StageGappa Ln1pCertificates Ln1pStageH Ln1pStageB LnStageEvaluation
 LnReduction Ln1pReduction Ln1pCheck Ln1pTables Ln1pLemmas LnNormalized LnUnit FastLn.
Require normal_normal_pair_log.
Open Scope R_scope.

Definition pair_old64 hi lo z :=
 let z2:=fmul z z in
 let t0:=fsub (fmul z (st_hc 0)) c_half in
 let t1:=fadd (fmul z (st_hc 2)) (st_hc 1) in
 let a1:=fadd (fmul z2 (st_hc 3)) t1 in
 let q:=fmul z2 (fadd (fmul z2 a1) t0) in
 let s:=fadd hi z in
 let e1:=fsub z (fsub s hi) in
 fadd s (fadd (fadd e1 lo) q).
Definition pair_new64 hi lo z :=
 let z2:=fmul z z in
 let t0:=fsub (fmul z (st_hc 0)) c_half in
 let q:=fmul z2 (fadd t0 (fmul z2 (st_hc 1))) in
 fadd (fadd hi z) (fadd lo q).
Definition pair_old_value hi lo z :=
 let z2:=rn(z*z) in
 let t0:=rn(rn(z*h3)-IZR 1*bpow radix2 (-1)) in
 let t1:=rn(rn(z*h5)+h4) in
 let a1:=rn(rn(z2*h6)+t1) in
 let q:=rn(z2*rn(rn(z2*a1)+t0)) in
 let s:=rn(hi+z) in
 let e1:=rn(z-rn(s-hi)) in
 rn(s+rn(rn(e1+lo)+q)).
Definition pair_new_value hi lo z :=
 let z2:=rn(z*z) in
 let t0:=rn(rn(z*h3)-IZR 1*bpow radix2 (-1)) in
 let q:=rn(z2*rn(t0+rn(z2*h4))) in
 rn(rn(hi+z)+rn(lo+q)).

Ltac pair_bound :=
 first [match goal with
 | Ha : Rabs ?a <= ?u, Hb : Rabs ?b <= ?v |- Rabs (?a * ?b) <= _ =>
   rewrite Rabs_mult;apply Rle_trans with (u*v);
   [apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Ha|exact Hb]|lra]
 end | eapply Rle_trans;[apply Rabs_triang|rewrite ?Rabs_Ropp;lra] ].
Ltac pair_op op k a b F V C :=
 destruct (op k 0%Z a b ltac:(assumption) ltac:(assumption)
   ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;StageGappa.bpow_num;cbn [IZR];pair_bound)) as [F [V C]];
 unfold bnd in C;revert C;StageGappa.bpow_num;cbn [IZR];intro C.

Lemma pair_sequences_ieee hi lo z : finite hi -> finite lo -> finite z ->
 Rabs(B hi)<=38 -> Rabs(B lo)<=1 -> Rabs(B z)<=1 ->
 finite(pair_old64 hi lo z) /\ finite(pair_new64 hi lo z) /\
 B(pair_old64 hi lo z)=pair_old_value (B hi) (B lo) (B z) /\
 B(pair_new64 hi lo z)=pair_new_value (B hi) (B lo) (B z).
Proof.
 intros Fhi Flo Fz Chi Clo Cz.
 pose proof Cz as Czcopy.
 destruct st_h3_ok as [Fh3 Vh3]. destruct st_h4_ok as [Fh4 Vh4].
 destruct st_h5_ok as [Fh5 Vh5]. destruct st_h6_ok as [Fh6 Vh6].
 destruct c_half_ok as [Fhalf Vhalf].
 assert (C3:Rabs(B(st_hc 0))<=1) by (rewrite Vh3;unfold h3;bpow_num;apply Rabs_le;lra).
 assert (C4:Rabs(B(st_hc 1))<=1) by (rewrite Vh4;unfold h4;bpow_num;apply Rabs_le;lra).
 assert (C5:Rabs(B(st_hc 2))<=1) by (rewrite Vh5;unfold h5;bpow_num;apply Rabs_le;lra).
 assert (C6:Rabs(B(st_hc 3))<=1) by (rewrite Vh6;unfold h6;bpow_num;apply Rabs_le;lra).
 assert (Chalf:Rabs(B c_half)<=1) by (rewrite Vhalf;bpow_num;apply Rabs_le;lra).
 pair_op fmul_bnd 1%Z z z Fz2 Vz2 Cz2.
 set (z2:=fmul z z) in *.
 pair_op fmul_bnd 1%Z z (st_hc 0) Fm0 Vm0 Cm0.
 set (m0:=fmul z (st_hc 0)) in *.
 pair_op fsub_bnd 2%Z m0 c_half Ft0 Vt0 Ct0.
 set (t0:=fsub m0 c_half) in *.
 pair_op fmul_bnd 1%Z z (st_hc 2) Fm2 Vm2 Cm2.
 set (m2:=fmul z (st_hc 2)) in *.
 pair_op fadd_bnd 2%Z m2 (st_hc 1) Ft1 Vt1 Ct1.
 set (t1:=fadd m2 (st_hc 1)) in *.
 pair_op fmul_bnd 1%Z z2 (st_hc 3) Fm3 Vm3 Cm3.
 set (m3:=fmul z2 (st_hc 3)) in *.
 pair_op fadd_bnd 4%Z m3 t1 Fa1 Va1 Ca1.
 set (a1:=fadd m3 t1) in *.
 pair_op fmul_bnd 4%Z z2 a1 Fp0 Vp0 Cp0.
 set (p0:=fmul z2 a1) in *.
 pair_op fadd_bnd 8%Z p0 t0 Fp Vp Cp.
 set (p:=fadd p0 t0) in *.
 pair_op fmul_bnd 8%Z z2 p Fq6 Vq6 Cq6.
 set (q6:=fmul z2 p) in *.
 pair_op fmul_bnd 1%Z z2 (st_hc 1) Fq40 Vq40 Cq40.
 set (q40:=fmul z2 (st_hc 1)) in *.
 pair_op fadd_bnd 4%Z t0 q40 Fq41 Vq41 Cq41.
 set (q41:=fadd t0 q40) in *.
 pair_op fmul_bnd 4%Z z2 q41 Fq4 Vq4 Cq4.
 set (q4:=fmul z2 q41) in *.
 pair_op fadd_bnd 64%Z hi z Fs Vs Cs.
 set (s:=fadd hi z) in *.
 pair_op fsub_bnd 128%Z s hi Fe10 Ve10 Ce10.
 set (e10:=fsub s hi) in *.
 pair_op fsub_bnd 256%Z z e10 Fe1 Ve1 Ce1.
 set (e1:=fsub z e10) in *.
 pair_op fadd_bnd 512%Z e1 lo Fpre Vpre Cpre.
 set (pre:=fadd e1 lo) in *.
 pair_op fadd_bnd 1024%Z pre q6 Foldlo Voldlo Coldlo.
 set (oldlo:=fadd pre q6) in *.
 pair_op fadd_bnd 2048%Z s oldlo Fold Vold Cold.
 set (old:=fadd s oldlo) in *.
 pair_op fadd_bnd 8%Z lo q4 Fnewlo Vnewlo Cnewlo.
 set (newlo:=fadd lo q4) in *.
 pair_op fadd_bnd 128%Z s newlo Fnew Vnew Cnew.
 set (new:=fadd s newlo) in *.

 unfold pair_old64,pair_new64;fold z2 m0 t0 m2 t1 m3 a1 p0 p q6 q40 q41 q4 s e10 e1 pre oldlo old newlo new.
 repeat split;try assumption.
 - unfold pair_old_value;cbv zeta.
   rewrite Vold,Voldlo,Vpre,Ve1,Ve10,Vs,Vq6,Vp,Vp0,Va1,Vm3,Vt1,Vm2,Vt0,Vm0,Vz2,Vh3,Vh4,Vh5,Vh6,Vhalf.
   rewrite Rmult_1_l. reflexivity.
 - unfold pair_new_value;cbv zeta.
   rewrite Vnew,Vnewlo,Vs,Vq4,Vq41,Vq40,Vt0,Vm0,Vz2,Vh3,Vh4,Vhalf.
   rewrite Rmult_1_l. reflexivity.
Qed.

Lemma pair_sequences_difference hi lo z : finite hi -> finite lo -> finite z ->
 Rabs(B hi)<=38 -> Rabs(B lo)<=/2^38 -> Rabs(B z)<=/2^9 ->
 finite(pair_new64 hi lo z) /\
 Rabs(B(pair_new64 hi lo z)-B(pair_old64 hi lo z))<=/2^45.
Proof.
 intros Fhi Flo Fz Hi Lo Z.
 destruct (pair_sequences_ieee hi lo z Fhi Flo Fz Hi ltac:(lra) ltac:(lra)) as [Fo [Fn [Vo Vn]]].
 split;[exact Fn|]. rewrite Vo,Vn.
 assert (Hir:-38<=B hi<=38) by (apply Rabs_le_inv;exact Hi).
 assert (Lor:-/2^38<=B lo<=/2^38) by (apply Rabs_le_inv;exact Lo).
 assert (Zr:-/2^9<=B z<=/2^9) by (apply Rabs_le_inv;exact Z).
 assert (Rh:rn(B hi)=B hi) by (apply round_generic;[exact _|apply B_fmt]).
 assert (Rl:rn(B lo)=B lo) by (apply round_generic;[exact _|apply B_fmt]).
 assert (Rz:rn(B z)=B z) by (apply round_generic;[exact _|apply B_fmt]).
 unfold pair_new_value,pair_old_value;cbv zeta.
 rewrite <-Rh,<-Rl,<-Rz. unfold h3,h4,h5,h6.
 clear -Hir Lor Zr.
 apply Rabs_le;split;apply Rnot_lt_le;intro Bad;
 apply (normal_normal_pair_log.l1 (B hi) (B z) (B lo));split;
 [gappa_hyps | intro Hb;gnorm_in Hb;gnorm_in Bad;bpow_num_all;lra
 |gappa_hyps | intro Hb;gnorm_in Hb;gnorm_in Bad;bpow_num_all;lra].
Qed.

Definition pair_stage64 E h :=
 let i:=rd_i(bits_of_b64 h) in
 pair_new64 (fadd (fmul (of_int E) st_l1) (st_th i))
            (fadd (fmul (of_int E) st_l0) (st_tl i)) (rd_z h).

Lemma pair_stage_difference E h : finite h ->
 bpow radix2 (-53)<=B h<=bpow radix2 1020 -> (-53<=E<=0)%Z ->
 let '(s,lo,_) := ln_parts E h in
 finite(pair_stage64 E h) /\
 Rabs(B(pair_stage64 E h)-B(fadd s lo))<=/2^45.
Proof.
 intros Fh Hr HE.
 pose proof (Ln1pReduction.reduce_ok h Fh Hr) as RD. cbv zeta in RD.
 destruct RD as [Er [Hi [RR [Yr [Yi [Frs [Brs [Fz [Bz [Zg [[zi [Zi [Zz [Zn Zf]]]] [Fth [Ftl [Gth [Ttl [Tth Terr]]]]]]]]]]]]]]]].
 pose proof (l_check_ok st_bounds st_l1_bits st_l0_bits st_el_bits st_l_check) as LO.
 destruct LO as [FL1 [FL0 [GL1 [[L1p L1u] [L0b [Lerr EL]]]]]].
 fold st_l1 in FL1,GL1,L1p,L1u,Lerr. fold st_l0 in FL0,L0b,Lerr.
 assert (Db:forall d,dval d=IZR(fst d)*bpow radix2(snd d)) by reflexivity.
 cbn [st_bounds b_l0_max b_l_err b_tl_max b_th_max b_t_err] in L0b,Lerr,Ttl,Tth,Terr.
 rewrite !Db in L0b,Lerr,Ttl,Tth,Terr;cbn [fst snd] in L0b,Lerr,Ttl,Tth,Terr.
 bpow_num_all.
 assert (Ln2:0.69314718055<=ln 2<=0.69314718056) by (split;interval with(i_prec 64)).
 assert (L1:Rabs(B st_l1)<=0.7).
 { apply Rabs_le_inv in L0b. apply Rabs_le_inv in Lerr. apply Rabs_le;lra. }
 destruct (of_int_ok E ltac:(lia)) as [Fe Ve].
 assert (EI:Rabs(B(of_int E))<=53) by (rewrite Ve,<-abs_IZR;apply IZR_le;lia).
 destruct (fmul_bnd 75 (-1) (of_int E) st_l1 Fe FL1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Fhi [Vhi Chi]].
 { unfold bnd;StageGappa.bpow_num;cbn [IZR]. rewrite Rabs_mult.
   apply Rle_trans with (53*0.7);[apply Rmult_le_compat;try apply Rabs_pos;assumption|lra]. }
 unfold bnd in Chi;bpow_num_in Chi.
 destruct (fadd_bnd 38 0 (fmul (of_int E) st_l1) (st_th(rd_i(bits_of_b64 h))) Fhi Fth ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Fh1 [Vh1 Ch1]].
 { unfold bnd;StageGappa.bpow_num;cbn [IZR]. eapply Rle_trans;[apply Rabs_triang|lra]. }
 unfold bnd in Ch1;change (bpow radix2 0) with 1 in Ch1.
 destruct (fmul_bnd 53 (-44) (of_int E) st_l0 Fe FL0 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Flo [Vlo Clo]].
 { unfold bnd;StageGappa.bpow_num;cbn [IZR]. rewrite Rabs_mult.
   apply Rle_trans with (53*/17592186044416);[apply Rmult_le_compat;try apply Rabs_pos;[exact EI|lra]|lra]. }
 unfold bnd in Clo;bpow_num_in Clo.
 destruct (fadd_bnd 54 (-44) (fmul (of_int E) st_l0) (st_tl(rd_i(bits_of_b64 h))) Flo Ftl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Fl1 [Vl1 Cl1]].
 { unfold bnd;StageGappa.bpow_num;cbn [IZR]. eapply Rle_trans;[apply Rabs_triang|lra]. }
 unfold bnd in Cl1;bpow_num_in Cl1.
 assert (Z:Rabs(B(rd_z h))<=/2^9) by (eapply Rle_trans;[exact Zz|];eapply Rle_trans;[exact Zi|];simpl;lra).
 pose proof (pair_sequences_difference _ _ _ Fh1 Fl1 Fz ltac:(cbn [IZR] in Ch1;lra) ltac:(cbn [IZR] in Cl1;lra) Z) as D.
 unfold pair_stage64. unfold ln_parts;cbv zeta.
 exact D.
Qed.

Definition pair_regular64 x :=
 let '(e,_,h,_) := LnReduction.reduce x in
 pair_stage64 (e+rd_e(bits_of_b64 h)) h.

Theorem pair_regular_difference x : finite x -> /2^53<=B x<1 ->
 finite(pair_regular64 x) /\
 Rabs(B(pair_regular64 x)-B(fast_ln_regular64 x))<=/2^45.
Proof.
 intros Fx X.
 pose proof (LnReduction.reduce_ok x Fx ltac:(lra)) as RD.
 pose proof (reduced_stage_exponent_zero x) as ZE.
 unfold pair_regular64,fast_ln_regular64. revert RD ZE.
 generalize (LnReduction.reduce x);intros [[[e i]h]r] RD [ZE ZU].
 destruct RD as [I [_ [Fh [Y [_ [XY Er]]]]]].
 destruct (LnReduction.ln_range i I) as [Yl [Yu _]].
 assert (E:(-53<=e<=0)%Z).
 { split.
   - apply Z.nlt_ge;intro Bad.
     assert (P:bpow radix2 e<=bpow radix2 (-54)) by (apply bpow_le;lia).
     pose proof (bpow_gt_0 radix2 e). bpow_num_in P. nra.
   - apply Z.nlt_ge;intro Bad.
     assert (P:2<=bpow radix2 e) by (change 2 with (bpow radix2 1);apply bpow_le;lia).
     nra. }
 rewrite ZE,Z.add_0_r.
 apply pair_stage_difference;[exact Fh| |exact E].
 split;[bpow_num;lra|apply Rle_trans with 2;[lra|change 2 with (bpow radix2 1);apply bpow_le;lia]].
Qed.

Definition pair_unit x :=
 ((st_off+298*2^43 <=? bits_of_b64 x) &&
  (bits_of_b64 x <? st_off+301*2^43))%Z.
Definition pair_log64 x := if pair_unit x then fast_ln_regular64 x else pair_regular64 x.

Lemma pair_unit_spec x : pair_unit x=true <-> unit_bits(bits_of_b64 x).
Proof. unfold pair_unit,unit_bits. rewrite Bool.andb_true_iff,Z.leb_le,Z.ltb_lt. reflexivity. Qed.

Lemma pair_unit_contains x : finite x -> 511/512<=B x<1 -> pair_unit x=true.
Proof.
 intros Fx X.
 assert (Normal:bpow radix2 (-1022)<=B x).
 { apply Rle_trans with (/2);[change (/2) with (bpow radix2 (-1));apply bpow_le;lia|lra]. }
 destruct (pos_normal x Fx Normal) as [m [e [H [Eq [M [E [V [_ [_ Bits]]]]]]]]].
 assert (Ml:4503599627370496<=IZR(Zpos m)) by (apply IZR_le;exact(proj1 M)).
 assert (Mu:IZR(Zpos m)<9007199254740992) by (apply IZR_lt;exact(proj2 M)).
 assert (Ee:e=(-53)%Z).
 { destruct (Z_lt_ge_dec e (-53)) as [Less|Ge].
   - assert (P:bpow radix2 e<=bpow radix2 (-54)) by (apply bpow_le;lia).
     pose proof (bpow_gt_0 radix2 e). bpow_num_in P. nra.
   - destruct (Z.eq_dec e (-53));[assumption|].
     assert (P:bpow radix2 (-52)<=bpow radix2 e) by (apply bpow_le;lia).
     bpow_num_in P. nra. }
 subst e. bpow_num_in V.
 assert (Low:(2^53-2^44<=Zpos m)%Z).
 { apply le_IZR. change (8989607068696576<=IZR(Zpos m)). nra. }
 apply pair_unit_spec. unfold unit_bits. rewrite Bits,join_eq. unfold st_off. lia.
Qed.

Theorem pair_log_near_one x : pair_unit x=true -> B x<>1 ->
 pair_log64 x = let '(s,lo,_) := unit_parts x in fadd s lo.
Proof.
 intros U N. unfold pair_log64;rewrite U. apply unit_fast_identical;[apply pair_unit_spec;exact U|exact N].
Qed.

Theorem pair_log_ok x : finite x -> /2^53<=B x<1 ->
 finite(pair_log64 x) /\
 (Rabs(B(pair_log64 x)-ln(B x))<=/2^53*Rabs(ln(B x))+/2^65 \/
 (/2^9<= -ln(B x) /\
 Rabs(B(pair_log64 x)-ln(B x))<=/2^48*Rabs(ln(B x))+/2^45)).
Proof.
 intros Fx X.
 destruct (fast_ln_regular_ok x Fx ltac:(lra) ltac:(lra)) as [Fo O].
 unfold pair_log64;destruct (pair_unit x) eqn:U.
 - split;[exact Fo|left;bpow_num_all;lra].
 - destruct (pair_regular_difference x Fx X) as [Fn D]. split;[exact Fn|right].
   assert (Far:B x<511/512).
   { destruct (Rlt_dec (B x) (511/512));[assumption|].
     assert (pair_unit x=true) by (apply pair_unit_contains;[exact Fx|lra]). congruence. }
   assert (L:/2^9<= -ln(B x)) by (interval with(i_prec 100)).
   split;[exact L|].
   replace (B(pair_regular64 x)-ln(B x)) with
     ((B(pair_regular64 x)-B(fast_ln_regular64 x))+(B(fast_ln_regular64 x)-ln(B x))) by ring.
   eapply Rle_trans;[apply Rabs_triang|].
   rewrite (Rabs_left (ln(B x))) in O |- * by lra.
   bpow_num_all;lra.
Qed.
