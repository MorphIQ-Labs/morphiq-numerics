(** IEEE large-tail reconstruction, with explicit analytic remainder. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal ErfcxEntryTables ErfcxQuotient ErfcxRounding ErfcxTailCorrection.
Require erfcx_tail_composition.
Open Scope R_scope.

Lemma tail_composition_model T eu rem eq l dm da am aa :
 0 <= T <= /2^18 -> - /2^69 <= eu <= /2^69 ->
 0 <= rem <= 7/2^72 -> - /2^69 <= eq <= /2^69 ->
 - /2^51 <= l <= /2^51 -> - /2^53 <= dm <= /2^53 -> - /2^53 <= da <= /2^53 ->
 - /2^170 <= am <= /2^170 -> - /2^170 <= aa <= /2^170 ->
 let u := tail_polynomial T+eu in let z := u*(1+dm)+am in
 let r := (l+z)*(1+da)+aa in let s := 1+tail_polynomial T+rem in
 let f := ((1+l)/(1+eq))*s in
 - /2^67 <= ((1+r)-f)/f <= /2^67 /\ - /2^17 <= r <= /2^17 /\ 99/100 <= s <= 101/100.
Proof.
 intros T0 Eu Rem Eq L Dm Da Am Aa. cbv zeta. unfold tail_polynomial.
 repeat split; erfcx_goal (erfcx_tail_composition.l1 eq l T eu dm am da aa rem).
Qed.

Definition tail_reconstruct64 q ql u := fast_two_sum64 q (fadd ql (fmul q u)).

Theorem tail_reconstruct_ieee q ql u z T rem :
 finite q -> finite ql -> finite u -> 0<z ->
 bpow radix2 (-899) <= B q <= bpow radix2 (-9) ->
 - /2^51 <= B ql/B q <= /2^51 ->
 - /2^18 <= B u <= 0 ->
 - /2^69 <= ((B q+B ql)-z)/z <= /2^69 ->
 0 <= T <= /2^18 -> - /2^69 <= B u-tail_polynomial T <= /2^69 ->
 0 <= rem <= 7/2^72 ->
 let '(h,l) := tail_reconstruct64 q ql u in
 finite h /\ finite l /\
 - /2^67 <= ((B h+B l)-z*(1+tail_polynomial T+rem))/(z*(1+tail_polynomial T+rem)) <= /2^67.
Proof.
 intros Fq Fql Fu Z Q L U Eq Tr Eu Rem.
 assert (Qpos : 0<B q) by (pose proof (bpow_gt_0 radix2 (-899)); lra).
 assert (Qsmall : B q<=/512) by (change (bpow radix2 (-9)) with (/512) in Q; lra).
 assert (Lid : B ql=(B ql/B q)*B q) by (field; lra).
 assert (Lsmall : -1 <= B ql <= 1) by (clear - L Lid Qpos Qsmall; nra).
 destruct (fmul_bnd 1 0 q u Fq Fu ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; clear - Qpos Qsmall U; nra)) as [Fm [Bm M]].
 unfold bnd in M. rewrite Rmult_1_l in M. change (bpow radix2 0) with 1 in M.
 destruct (fadd_ok 2 0 ql (fmul q u) Fql Fm ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        pose proof (Rabs_le_inv _ _ M); apply Rabs_le; lra)) as [Fr Br].
 destruct (normalized_rounding (B q*B u) (B q) ltac:(lra)) as [dm [am [Dm [Am Em]]]].
 rewrite <- Bm in Em. replace ((B q*B u)/B q) with (B u) in Em by (field; lra).
 destruct (normalized_rounding (B ql+B (fmul q u)) (B q) ltac:(lra)) as [da [aa [Da [Aa Ea]]]].
 rewrite <- Br in Ea.
 replace ((B ql+B (fmul q u))/B q) with (B ql/B q+B (fmul q u)/B q) in Ea by (field; lra).
 pose proof (tail_composition_model T (B u-tail_polynomial T) rem
  (((B q+B ql)-z)/z) (B ql/B q) dm da am aa Tr Eu Rem Eq L
  ltac:(bpow_num_all; simpl; lra) ltac:(bpow_num_all; simpl; lra)
  ltac:(bpow_num_all; simpl; lra) ltac:(bpow_num_all; simpl; lra)) as Model.
 cbv zeta in Model.
 replace (tail_polynomial T+(B u-tail_polynomial T)) with (B u) in Model by ring.
 rewrite <- Em,<-Ea in Model.
 destruct Model as [Err [R S]].
 set (r := fadd ql (fmul q u)) in *.
 assert (Rid : B r=(B r/B q)*B q) by (field; lra).
 assert (Dom : Rabs (B r) <= Rabs (B q)).
 { rewrite (Rabs_pos_eq (B q)) by lra. apply Rabs_le. clear - R Rid Qpos; nra. }
 pose proof (fast_two_sum_ieee q r Fq Fr
  ltac:(apply Rle_trans with 1; [apply Rabs_le; lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
  ltac:(apply Rle_trans with 1; [apply Rle_trans with (Rabs (B q)); [exact Dom | apply Rabs_le; lra] |
        change 1 with (bpow radix2 0); apply bpow_le; lia])
  ltac:(right; left; exact Dom)) as FS.
 unfold tail_reconstruct64. fold r.
 destruct (fast_two_sum64 q r) as [h lo]. destruct FS as [Fh [Fl [_ Sum]]].
 assert (OneEq : 1+((B q+B ql)-z)/z <> 0) by (clear - Eq; nra).
 assert (Qsum : 0<B q+B ql) by (clear - Qpos L Lid; nra).
 assert (Fval : ((1+B ql/B q)/(1+((B q+B ql)-z)/z)) = z/B q).
 { field. repeat split; lra. }
 rewrite Fval in Err.
 assert (E : ((1+B r/B q)-(z/B q)*(1+tail_polynomial T+rem))/((z/B q)*(1+tail_polynomial T+rem))
  = ((B h+B lo)-z*(1+tail_polynomial T+rem))/(z*(1+tail_polynomial T+rem))).
 { rewrite Sum. field. repeat split; lra. }
 rewrite E in Err. repeat split; tauto.
Qed.

Lemma quotient_constant_error h l c0 c x : 0<c -> 0<x ->
 - /2^110 <= (c0-c)/c <= /2^110 ->
 - /2^70 <= ((h+l)-c0/x)/(c0/x) <= /2^70 ->
 - /2^69 <= ((h+l)-c/x)/(c/x) <= /2^69.
Proof.
 intros C X Ec Eq.
 assert (C0id : c0=(1+(c0-c)/c)*c) by (field; lra).
 assert (C0 : 0<c0).
 { set (ec := (c0-c)/c) in *. clear - C C0id Ec. nra. }
 assert (E : ((h+l)-c/x)/(c/x) = (1+(c0-c)/c)*(1+((h+l)-c0/x)/(c0/x))-1).
 { field. repeat split; lra. }
 rewrite E. set (ec := (c0-c)/c) in *. set (eq := ((h+l)-c0/x)/(c0/x)) in *.
 clear - Ec Eq. nra.
Qed.

Definition tail64 x :=
 let '(q,ql) := quotient64 x in tail_reconstruct64 q ql (tail_correction64 x).

Theorem tail_ieee x c rem : finite x -> 512 <= B x <= bpow radix2 897 -> 0<c ->
 - /2^110 <= ((B cs+B csl)-c)/c <= /2^110 -> 0 <= rem <= 7/2^72 ->
 let '(h,l) := tail64 x in
 finite h /\ finite l /\
 - /2^67 <= ((B h+B l)-(c/B x)*(1+tail_polynomial ((1/B x)*(1/B x))+rem))/
  ((c/B x)*(1+tail_polynomial ((1/B x)*(1/B x))+rem)) <= /2^67.
Proof.
 intros Fx X C Ec Rem.
 pose proof (quotient_ieee x Fx X) as Q.
 destruct (tail_correction_ieee x Fx ltac:(lra)) as [Fu [Eu U]].
 unfold tail64. destruct (quotient64 x) as [q ql].
 destruct Q as [Fq [Fql [Eq [L H]]]].
 assert (Eq' : - /2^70 <= ((B q+B ql)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= /2^70).
 { replace (/2^70) with (bpow radix2 (-70)) by (bpow_num; simpl; field). exact Eq. }
 pose proof (quotient_constant_error (B q) (B ql) (B cs+B csl) c (B x) C ltac:(lra) Ec Eq') as E.
 assert (Z : 0<c/B x) by (apply Rdiv_lt_0_compat; lra).
 assert (Y : 0 <= 1/B x <= /512).
 { unfold Rdiv. rewrite Rmult_1_l. split; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
 exact (tail_reconstruct_ieee q ql (tail_correction64 x) (c/B x) ((1/B x)*(1/B x)) rem
  Fq Fql Fu Z H ltac:(replace (/2^51) with (bpow radix2 (-51)) by (bpow_num; simpl; field); exact L) U E ltac:(clear - Y; nra) Eu Rem).
Qed.

Require Import ErfcxQuotientScale.
Require erfcx_tail_scaled.
Lemma scaled_tail_model eq correction : - /2^69 <= eq <= /2^69 ->
 0 <= correction <= bpow radix2 (-1794) ->
 - /2^68 <= ((1+eq)-(1-correction))/(1-correction) <= /2^68.
Proof.
 intros E C. split; erfcx_goal (erfcx_tail_scaled.l1 eq correction).
Qed.

Theorem scaled_tail_ieee x c correction : finite x -> bpow radix2 896 <= B x -> 0<c ->
 - /2^110 <= ((B cs+B csl)-c)/c <= /2^110 ->
 0 <= correction <= bpow radix2 (-1794) ->
 let '(h,l) := scaled_quotient64 x in
 finite h /\ finite l /\
 - /2^68 <= ((B h+B l)*bpow radix2 (-600)-(c/B x)*(1-correction))/
 ((c/B x)*(1-correction)) <= /2^68.
Proof.
 intros Fx X C Ec Corr.
 pose proof (scaled_quotient_ieee x Fx X) as Q.
 destruct (scaled_quotient64 x) as [h l]. destruct Q as [Fh [Fl Eq]].
 assert (Xpos : 0<B x) by (pose proof (bpow_gt_0 radix2 896); lra).
 assert (Eq' : - /2^70 <=
 ((B h+B l)*bpow radix2 (-600)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= /2^70).
 { replace (/2^70) with (bpow radix2 (-70)) by (bpow_num; simpl; field). exact Eq. }
 pose proof (quotient_constant_error ((B h+B l)*bpow radix2 (-600)) 0
  (B cs+B csl) c (B x) C Xpos Ec ltac:(rewrite Rplus_0_r; exact Eq')) as E.
 rewrite Rplus_0_r in E.
 pose proof (scaled_tail_model _ _ E Corr) as Bound.
 assert (Spos : 0<1-correction).
 { assert (Small : bpow radix2 (-1794) <= /2).
   { change (/2) with (bpow radix2 (-1)). apply bpow_le; lia. } lra. }
 assert (Id :
 ((1+((B h+B l)*bpow radix2 (-600)-c/B x)/(c/B x))-(1-correction))/(1-correction)
 = ((B h+B l)*bpow radix2 (-600)-(c/B x)*(1-correction))/((c/B x)*(1-correction))).
 { field. repeat split; lra. }
 rewrite Id in Bound. repeat split; tauto.
Qed.
