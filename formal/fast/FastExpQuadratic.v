(** Public low-latency exp: one-word reduction and parallel quadratic.
    The internal normal-family cubic keeps its separate tighter contract. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul
 RoundingConstant RoundingTest RoundingCore Grid Encodings.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA
 ErfcxTableEvaluation ErfcxReciprocal FastExpTables FastExpReduction FastExpScale.
Require exp_fast_quadratic exp_fast_quadratic_mvt exp_fast_quadratic_scaled.
Open Scope R_scope.

Lemma fast_short_reduction_ok x n ni : finite x -> Rabs(B x)<704 ->
 finite n -> B n=IZR ni -> (Z.abs ni<=1040035)%Z ->
 finite(fsub x(fmul n fx_step)) /\
 B(fsub x(fmul n fx_step))=rn(B x-B(fmul n fx_step)) /\
 Rabs(B x-B(fmul n fx_step)-(B x-IZR ni*fast_L))<=bpow radix2(-42).
Proof.
 intros Fx X Fn N Ni.
 assert (A:Rabs(IZR ni)<=1040035) by (rewrite <-abs_IZR;apply IZR_le;lia).
 assert (Step:0<=B fx_step<=0.000677) by (rewrite fx_step_val;split;interval).
 assert (P:Rabs(B n*B fx_step)<=1024).
 { rewrite N,Rabs_mult,(Rabs_pos_eq(B fx_step)) by lra. nra. }
 destruct (fmul_ok 1 10 n fx_step Fn fx_step_finite ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia) ltac:(unfold bnd;change(bpow radix2 10)with 1024;lra)) as [Fp Vp].
 assert (Pb:Rabs(B(fmul n fx_step))<=1024).
 { rewrite Vp. apply abs_round_le_generic;auto with typeclass_instances.
   - change 1024 with(bpow radix2 10). apply generic_format_bpow. unfold FLT_exp,emin,prec;lia.
 }
 destruct (fsub_ok 1 11 x(fmul n fx_step) Fx Fp ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)) as [Fr Vr].
 { unfold bnd;change(bpow radix2 11)with 2048.
   unfold Rminus;eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;lra. }
 split;[exact Fr|]. split;[exact Vr|].
 pose proof (ExpReduction.rnd_abs_err(B n*B fx_step)) as E.
 change (Rabs(rn(B n*B fx_step)-B n*B fx_step)<=bpow radix2(-53)*Rabs(B n*B fx_step)+ /2*bpow radix2(-1074)) in E. change (B(fmul n fx_step)=rn(B n*B fx_step)) in Vp. rewrite <-Vp in E.
 assert (Tiny:bpow radix2(-1074)<=bpow radix2(-100)) by (apply bpow_le;lia).
 assert (Round:Rabs(B(fmul n fx_step)-B n*B fx_step)<=
  bpow radix2(-53)*1024+bpow radix2(-100)).
 { eapply Rle_trans;[exact E|]. bpow_num_all;lra. }
 assert (Close:Rabs(fast_L-B fx_step)<=bpow radix2(-64)).
 { unfold fast_L;rewrite Rabs_minus_sym. change(-64)%Z with(-Z.of_nat 64)%Z.
   rewrite bpow_m;exact fx_step_close. }
 replace (B x-B(fmul n fx_step)-(B x-IZR ni*fast_L)) with
  (IZR ni*(fast_L-B fx_step)+(B n*B fx_step-B(fmul n fx_step))) by (rewrite N;ring).
 eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult,(Rabs_minus_sym (B n*B fx_step) (B(fmul n fx_step))).
 assert (Split:Rabs(IZR ni)*Rabs(fast_L-B fx_step)<=1040035*bpow radix2(-64)).
 { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
 bpow_num_all;lra.
Qed.

Definition fast_quad_half : f64 := b64_of_bits 4602678819172646912.
Lemma fast_quad_half_ok : finite fast_quad_half /\ B fast_quad_half= /2.
Proof. split.
 - exact(bits_finite 4602678819172646912 _ _ _ eq_refl).
 - change(B(b64_of_bits 4602678819172646912)= /2).
   rewrite (bits_val 4602678819172646912 false 4503599627370496 53 eq_refl). simpl;field.
Qed.
Definition fast_c1_g : R := float2R(Float2 4503599691855895 (-52)).
Lemma fast_c1_g_eq : B fx_c1=fast_c1_g.
Proof. rewrite fx_c1_val. unfold fast_c1_g,float2R,F2R;simpl;bpow_num_all;lra. Qed.
Definition fast_quadratic64 r :=
 fadd(fadd one(fmul fx_c1 r))(fmul(fmul fast_quad_half r)r).
Definition fast_quadratic_value r :=
 rn(rn(1+rn(fast_c1_g*r))+rn(rn(half_g*r)*r)).

Lemma fast_quadratic_ieee r : finite r -> Rabs(B r)<=/1024 ->
 finite(fast_quadratic64 r) /\ B(fast_quadratic64 r)=fast_quadratic_value(B r).
Proof.
 intros Fr Rr. destruct one_ok as [Fo Vo]. destruct fast_quad_half_ok as [Fh Vh].
 pose proof fx_c1_finite as Fc.
 assert (Cc:Rabs(B fx_c1)<=2) by (rewrite fx_c1_val;interval).
 assert (Co:Rabs(B one)<=1) by (rewrite Vo;apply Rabs_le;lra).
 assert (Ch:Rabs(B fast_quad_half)<=1) by (rewrite Vh;apply Rabs_le;lra).
 table_op fmul_bnd 1%Z (-9)%Z fx_c1 r Fa Va Ca.
 table_op fadd_bnd 2%Z 0%Z one (fmul fx_c1 r) Fp Vp Cp.
 table_op fmul_bnd 1%Z (-9)%Z fast_quad_half r Fb Vb Cb.
 table_op fmul_bnd 1%Z (-18)%Z (fmul fast_quad_half r) r Fv Vv Cv.
 table_op fadd_bnd 4%Z 0%Z (fadd one(fmul fx_c1 r)) (fmul(fmul fast_quad_half r)r) Fq Vq Cq.
 unfold fast_quadratic64;split;[exact Fq|].
 rewrite Vq,Vp,Va,Vv,Vb,Vo,Vh,fast_c1_g_eq. unfold fast_quadratic_value;rewrite half_g_eq;reflexivity.
Qed.

Lemma fast_quadratic_mvt r delta : Rabs r<=0.000339 ->
 Rabs delta<=bpow radix2(-41) -> Rabs(Qs(r+delta)-Qs r)<=bpow radix2(-52).
Proof.
 intros Hr Hd;unfold Qs,half_g,d3_g,d4_g,d5_g.
 apply Rabs_le_inv in Hr,Hd;apply Rabs_le.
 erfcx_goal(exp_fast_quadratic_mvt.l1 r delta).
Qed.

Lemma fast_quadratic_certificate R dr m a : Rabs R<=0.000338451 ->
 Rabs dr<=bpow radix2(-42) -> Rabs m<=bpow radix2(-52) ->
 Rabs a<=IZR 5174524961095286666344419*bpow radix2(-158) ->
 Rabs(fast_quadratic_value(rn(R+dr))-(1+R+Qs(rn(R+dr))+m+a))<=9*bpow radix2(-42) /\
 0.999<=fast_quadratic_value(rn(R+dr))<=1.001.
Proof.
 intros HR Hd Hm Ha;unfold fast_quadratic_value,fast_c1_g,Qs,half_g,d3_g,d4_g,d5_g.
 apply Rabs_le_inv in HR,Hd,Hm,Ha.
 split;[apply Rabs_le|];erfcx_goal(exp_fast_quadratic.l1 R dr m a).
Qed.

Theorem fast_quadratic_approx r R dr : finite r -> Rabs R<=0.000338451 ->
 Rabs dr<=bpow radix2(-42) -> B r=rn(R+dr) ->
 finite(fast_quadratic64 r) /\
 Rabs(B(fast_quadratic64 r)-exp R)<=9*bpow radix2(-42) /\
 0.999<=B(fast_quadratic64 r)<=1.001.
Proof.
 intros Fr HR Hd Br.
 assert (Er:Rabs(B r-(R+dr))<=bpow radix2(-64)).
 { rewrite Br;apply(rnd_err_below _ (-10));[lia|].
   eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
 assert (Hr:Rabs(B r)<=0.000339).
 { pose proof(Rabs_le_inv _ _ Er);pose proof(Rabs_le_inv _ _ HR);pose proof(Rabs_le_inv _ _ Hd).
   apply Rabs_le;bpow_num_all;lra. }
 set (m:=Qs R-Qs(B r)).
 assert (Hm:Rabs m<=bpow radix2(-52)).
 { unfold m;replace R with(B r+(R-B r))at 1 by ring.
   apply fast_quadratic_mvt;[exact Hr|].
   apply Rabs_le_inv in Er;pose proof(Rabs_le_inv _ _ Hd);apply Rabs_le;bpow_num_all;lra. }
 set (a:=exp R-1-R-Qs R).
 assert (Ha:Rabs a<=IZR 5174524961095286666344419*bpow radix2(-158)).
 { pose proof(st_poly_approx R ltac:(lra))as A;unfold st_poly_bound,Rdiv in A.
   rewrite <-(bpow_m 158)in A;rewrite d3_g_eq,d4_g_eq,d5_g_eq in A.
   unfold a,Qs;rewrite half_g_eq;replace(/2)with(1/2)by field;exact A. }
 destruct(fast_quadratic_ieee r Fr ltac:(lra))as[Fq Vq].
 destruct(fast_quadratic_certificate R dr m a HR Hd Hm Ha)as[Error Range].
 rewrite <-Br,<-Vq in Error,Range.
 assert(Id:1+R+Qs(B r)+m+a=exp R)by(unfold m,a;ring).
 rewrite Id in Error;exact(conj Fq (conj Error Range)).
Qed.

Lemma fast_quadratic_product h q dt dq : finite h -> finite q ->
 bpow radix2(-1016)<=B h<=bpow radix2 1017 -> 0.999<=B q<=1.001 ->
 Rabs dt<=4503599627370498*bpow radix2(-105) -> Rabs dq<=9*bpow radix2(-42) ->
 finite(fmul h q) /\
 Rabs((B(fmul h q)-B h*((1+dt)*(B q+dq)))/(B h*((1+dt)*(B q+dq))))<=bpow radix2(-38).
Proof.
 intros Fh Fq H Q Dt Dq.
 assert (Hp:0<B h)by(pose proof(bpow_gt_0 radix2(-1016));lra).
 assert (Ppos:0<B h*B q)by nra.
 destruct(fmul_bnd 1 1018 h q Fh Fq ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;
   replace(bpow radix2 1018)with(2*bpow radix2 1017)by(change 2 with(bpow radix2 1);rewrite <-bpow_plus;reflexivity);nra))as[Fy[Vy Cy]].
 assert (Pn:bpow radix2(-1022)<=Rabs(B h*B q)).
 { rewrite Rabs_pos_eq by lra;eapply Rle_trans with(/2*bpow radix2(-1016));[bpow_num_all;lra|nra]. }
 pose proof(rnd_rel(B h*B q)Pn)as Ey.
 change(Rabs(rndF(B h*B q)-B h*B q)<=bpow radix2(-53)*Rabs(B h*B q))in Ey.
 rewrite <-Vy,(Rabs_pos_eq(B h*B q))in Ey by lra.
 assert (Eybound:Rabs(B(fmul h q)-B h*B q)<=1026*bpow radix2(-63)*B h).
 { eapply Rle_trans;[exact Ey|];bpow_num_all;nra. }
 set (ey:=(B(fmul h q)-B h*B q)/B h).
 assert (Eyn:Rabs ey<=1026*bpow radix2(-63)).
 { unfold ey,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(B h))by lra.
   apply(Rmult_le_reg_r(B h));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Eybound. }
 assert (Budget:Rabs(((B q+ey)-(1+dt)*(B q+dq))/((1+dt)*(B q+dq)))<=bpow radix2(-38)).
 { apply Rabs_le_inv in Dt,Dq,Eyn;apply Rabs_le;erfcx_goal(exp_fast_quadratic_scaled.l1 (B q) ey dt dq). }
 assert (Tpos:0<(1+dt)*(B q+dq)).
 { apply Rabs_le_inv in Dt,Dq;bpow_num_all;apply Rmult_lt_0_compat;lra. }
 assert (Id:(B(fmul h q)-B h*((1+dt)*(B q+dq)))/(B h*((1+dt)*(B q+dq)))=
  ((B q+ey)-(1+dt)*(B q+dq))/((1+dt)*(B q+dq))).
 { unfold ey;field;repeat split;nra. }
 split;[exact Fy|];rewrite Id;exact Budget.
Qed.

Definition fast_exp_quadratic64 x :=
 let '(n,j,k,_):=fast_stage_of x in
 let r:=fsub x(fmul n fx_step)in
 fmul(fast_scaled_high64(Z.to_nat j)k)(fast_quadratic64 r).

Theorem fast_exp_quadratic_ok x : finite x -> Rabs(B x)<704 ->
 finite(fast_exp_quadratic64 x) /\
 Rabs(B(fast_exp_quadratic64 x)-exp(B x))<=bpow radix2(-38)*exp(B x).
Proof.
 intros Fx X;pose proof(fast_stage_of_ok x Fx X)as SO.
 unfold fast_exp_quadratic64;revert SO;generalize(fast_stage_of x).
 intros [[[n j]k]r1] SO.
 destruct SO as[ni[Bn[Fn[Hn[Hjk[Hj[Hk[Fr1[Br1[HR Rest]]]]]]]]]].
 assert(Jn:(Z.to_nat j<1024)%nat)by lia.
 destruct(fast_short_reduction_ok x n ni Fx X Fn Bn Hn)as[Fr[Br Hdr]].
 set(r:=fsub x(fmul n fx_step))in *.
 set(R:=B x-IZR ni*fast_L)in *.
 set(dr:=B x-B(fmul n fx_step)-R)in *.
 assert(Rvalue:B r=rn(R+dr))by(rewrite Br;f_equal;unfold dr;ring).
 destruct(fast_quadratic_approx r R dr Fr HR Hdr Rvalue)as[Fq[Eq Q]].
 destruct(fast_table_facts(Z.to_nat j)Jn)as[Fth[Ftl[Th[Tl Et]]]].
 destruct(fast_scaled_high_ok(Z.to_nat j)k Jn Hk)as[Fh Vh].
 change(B(fast_scaled_high64(Z.to_nat j)k)=B(fx_t_hi(Z.to_nat j))*bpow radix2 k)in Vh.
 set(h:=fast_scaled_high64(Z.to_nat j)k)in *.
 set(q:=fast_quadratic64 r)in *.
 set(th:=B(fx_t_hi(Z.to_nat j)))in *.
 set(T:=exp(INR(Z.to_nat j)*ln 2/1024))in *.
 assert(Hrange:bpow radix2(-1016)<=B h<=bpow radix2 1017).
 { rewrite Vh;pose proof(bpow_gt_0 radix2 k).
   assert(L:bpow radix2(-1016)<=bpow radix2 k)by(apply bpow_le;lia).
   assert(U:bpow radix2 k<=bpow radix2 1016)by(apply bpow_le;lia).
   replace(bpow radix2 1017)with(2*bpow radix2 1016)by(change 2 with(bpow radix2 1);rewrite <-bpow_plus;reflexivity).
   split;nra. }
 set(dt:=(T-th)/th);set(dq:=exp R-B q).
 assert(Dt:Rabs dt<=4503599627370498*bpow radix2(-105)).
 { assert(E:Rabs(T-th)<=bpow radix2(-53)+bpow radix2(-104)).
   { replace(T-th)with(B(fx_t_lo(Z.to_nat j))-(th+B(fx_t_lo(Z.to_nat j))-T))by ring.
     eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;lra. }
   unfold dt,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq th)by lra.
   apply(Rmult_le_reg_r th);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
 assert(Dq:Rabs dq<=9*bpow radix2(-42))by(unfold dq;rewrite Rabs_minus_sym;exact Eq).
 destruct(fast_quadratic_product h q dt dq Fh Fq Hrange Q Dt Dq)as[Fy Error].
 assert(Ex:exp(B x)=T*exp R*bpow radix2 k).
 { unfold T;rewrite <-fast_exp_split;f_equal;rewrite Z2Nat.id by lia;unfold R;rewrite Hjk;ring. }
 assert(Scale:B h*((1+dt)*(B q+dq))=exp(B x)).
 { rewrite Vh,Ex;unfold dt,dq;field;lra. }
 rewrite Scale in Error;split;[exact Fy|].
 unfold Rdiv in Error;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(exp(B x)))in Error by(pose proof(exp_pos(B x));lra).
 apply(Rmult_le_reg_r(/exp(B x)));[apply Rinv_0_lt_compat,exp_pos|].
 rewrite Rmult_assoc,Rinv_r,Rmult_1_r by(pose proof(exp_pos(B x));lra);exact Error.
Qed.
