(** Bounded exponential: scaled high-word table and cubic reconstruction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingConstant RoundingTest RoundingGaps Grid.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA
 FastExpTables FastExpReduction FastExpScale FastExpPolynomial FastExpReconstruction.
Open Scope R_scope.
Definition fast_exp_entry64 x :=
 let '(n,j,k,r1):=fast_stage_of x in
 let r:=fsub r1 (fmul n fx_l2d) in
 fast_reconstruct64 (fast_scaled_high64 (Z.to_nat j) k) (fast_cubic64 r).

Theorem fast_exp_entry_ok x : finite x -> Rabs (B x)<704 ->
 finite (fast_exp_entry64 x) /\
 Rabs (B (fast_exp_entry64 x)-exp (B x))<=bpow radix2 (-51)*exp (B x).
Proof.
 intros Fx X. pose proof (fast_stage_of_ok x Fx X) as SO.
 unfold fast_exp_entry64. revert SO.
 generalize (fast_stage_of x). intros [[[n j] k] r1] SO.
 destruct SO as [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 _]]]]]]]]]]].
 assert (Jn:(Z.to_nat j<1024)%nat) by lia.
 destruct (fast_stage_r_ok n r1 ni (B x) Fn Bn Hn Fr1 Br1 HR Hr1) as [Fr [Br Hdr]].
 set (r:=fsub r1 (fmul n fx_l2d)) in *.
 set (R:=B x-IZR ni*fast_L) in *.
 set (dr:=B r1-B(fmul n fx_l2d)-R) in *.
 assert (Rvalue:B r=rn(R+dr)) by (rewrite Br;f_equal;unfold dr;ring).
 destruct (fast_cubic_approx r R dr Fr HR Hdr Rvalue) as [Fu [Eu U]].
 destruct (fast_table_facts (Z.to_nat j) Jn) as [Fth [Ftl [Th [Tl Et]]]].
 destruct (fast_scaled_high_ok (Z.to_nat j) k Jn Hk) as [Fh Vh].
 change (B(fast_scaled_high64 (Z.to_nat j) k)=B(fx_t_hi (Z.to_nat j))*bpow radix2 k) in Vh.
 set (h:=fast_scaled_high64 (Z.to_nat j) k) in *.
 set (u:=fast_cubic64 r) in *.
 set (th:=B(fx_t_hi (Z.to_nat j))) in *.
 set (T:=exp(INR(Z.to_nat j)*ln 2/1024)) in *.
 assert (Hrange:bpow radix2(-1016)<=B h<=bpow radix2 1017).
 { rewrite Vh. pose proof (bpow_gt_0 radix2 k).
   assert (L:bpow radix2(-1016)<=bpow radix2 k) by (apply bpow_le;lia).
   assert (Upper:bpow radix2 k<=bpow radix2 1016) by (apply bpow_le;lia).
   replace (bpow radix2 1017) with (2*bpow radix2 1016)
     by (change 2 with(bpow radix2 1);rewrite <-bpow_plus;reflexivity).
   split;nra. }
 set (dt:=(T-th)/th).
 set (du:=exp R-1-B u).
 assert (Dtu:Rabs dt<=4503599627370498*bpow radix2(-105)).
 { assert (E:Rabs(T-th)<=bpow radix2(-53)+bpow radix2(-104)).
   { replace (T-th) with (B(fx_t_lo (Z.to_nat j))-(th+B(fx_t_lo (Z.to_nat j))-T)) by ring.
     eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;lra. }
   unfold dt,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq th) by lra.
   apply (Rmult_le_reg_r th);[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
   bpow_num_all;nra. }
 assert (Duu:Rabs du<=7*bpow radix2(-56)) by (unfold du;rewrite Rabs_minus_sym;exact Eu).
 destruct (fast_reconstruction_ok h u dt du Fh Fu Hrange U Dtu Duu) as [Fy Error].
 assert (Ex:exp(B x)=T*exp R*bpow radix2 k).
 { unfold T;rewrite <-fast_exp_split;f_equal.
   rewrite Z2Nat.id by lia;unfold R;rewrite Hjk;ring. }
 assert (Scale:B h*((1+dt)*(1+B u+du))=exp(B x)).
 { rewrite Vh,Ex;unfold dt,du;field;lra. }
 rewrite Scale in Error. split;[exact Fy|].
 unfold Rdiv in Error;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(exp(B x))) in Error by (pose proof(exp_pos(B x));lra).
 apply (Rmult_le_reg_r (/exp(B x)));[apply Rinv_0_lt_compat,exp_pos|].
 rewrite Rmult_assoc,Rinv_r,Rmult_1_r by (pose proof(exp_pos(B x));lra).
 exact Error.
Qed.

Theorem fast_exp_entry_positive x : finite x -> Rabs (B x)<704 ->
 0<B (fast_exp_entry64 x).
Proof.
 intros Fx X. destruct (fast_exp_entry_ok x Fx X) as [_ Error].
 pose proof (Rabs_le_inv _ _ Error) as E.
 pose proof (exp_pos (B x)). clear - E H. bpow_num_all; nra.
Qed.

Theorem fast_exp_nonpositive_range x : finite x -> -32<=B x<=0 ->
 bpow radix2 (-47)<=B (fast_exp_entry64 x)<=2.
Proof.
 intros Fx X. assert (Domain : Rabs (B x)<704) by (apply Rabs_lt;lra).
 destruct (fast_exp_entry_ok x Fx Domain) as [_ Error].
 pose proof (Rabs_le_inv _ _ Error) as E.
 assert (Range : 1/100000000000000<=exp (B x)<=1).
 { split; interval with (i_prec 80). }
 clear - E Range. bpow_num_all; nra.
Qed.

(** Public dispatch reuses the existing exp stage screen, equivalent to the
    Rust absolute-value comparison. The strong owner's result is an explicit
    parameter: this theorem does not re-prove the existing strong fallback. *)
Require ExpStageB FastExpQuadratic.
Definition fast_exp_public64 x strong_result :=
 if ExpStageB.screen x then FastExpQuadratic.fast_exp_quadratic64 x else strong_result.

Theorem fast_exp_public_accelerated x strong_result :
 ExpStageB.screen x=true ->
 finite (fast_exp_public64 x strong_result) /\
 Rabs (B (fast_exp_public64 x strong_result)-exp (B x))<=
   bpow radix2 (-38)*exp (B x).
Proof.
 intros Screen. unfold fast_exp_public64;rewrite Screen.
 destruct (ExpStageB.screen_ok x Screen) as [Fx X].
 apply FastExpQuadratic.fast_exp_quadratic_ok;assumption.
Qed.

Theorem fast_exp_public_fallback x strong_result :
 ExpStageB.screen x=false -> fast_exp_public64 x strong_result=strong_result.
Proof. intros Screen;unfold fast_exp_public64;rewrite Screen;reflexivity. Qed.
