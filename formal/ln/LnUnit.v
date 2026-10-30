(** The reciprocal-one cells use the exact reduction z=x-1. The existing
    polynomial, error budget and decision remain unchanged. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool List.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import LnNormalized Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pStageH Ln1pStageB LnStageEvaluation Ln1pLemmas ExpFast.
Open Scope R_scope.

Lemma unit_add_zero x : finite x -> B x <> 0 -> fadd c_zero x = x.
Proof. intros F N. destruct x; try reflexivity; simpl in N; contradiction. Qed.

Lemma unit_sub_zero x : finite x -> fsub x c_zero = x.
Proof. intros F. destruct x; try reflexivity; try discriminate. destruct s; reflexivity. Qed.

Lemma unit_sub_self x : finite x -> fsub x x = c_zero.
Proof.
 intros F.
 pose proof (Bminus_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x x F F) as C.
 rewrite Rminus_diag_eq, round_0, Rabs_R0 in C by (reflexivity || exact _).
 rewrite Rlt_bool_true in C by apply bpow_gt_0.
 rewrite Rcompare_Eq in C by reflexivity.
 destruct C as [V [Fin Sign]].
 apply B2R_Bsign_inj; [exact Fin | exact c_zero_finite | exact V | ].
 change (Bsign 53 1024 (fsub x x) = false).
 exact (eq_trans Sign (andb_negb_r _)).
Qed.

Definition unit_bits (bits:Z) : Prop :=
 (st_off + 298*2^43 <= bits < st_off + 301*2^43)%Z.

Lemma unit_fields bits : unit_bits bits ->
 rd_e bits=0%Z /\ (298 <= rd_i bits < 301)%nat.
Proof.
 intros H. unfold unit_bits in H.
 assert (Range : (st_off <= bits < st_off + 2^52)%Z) by lia.
 destruct (interval_exponent_zero bits Range) as [E U]. split; [exact E | ].
 destruct (rd_fields bits ltac:(unfold st_off in *; lia)) as [I [_ [r [R D]]]].
 rewrite E in D. lia.
Qed.

Lemma unit_tables i : (298 <= i < 301)%nat ->
 st_r i = Ln1pReduction.c_one /\ st_th i = c_zero /\ st_tl i = c_zero.
Proof.
 intros H. assert (i=298 \/ i=299 \/ i=300)%nat by lia.
 destruct H0 as [-> | [-> | ->]]; vm_compute; repeat split; reflexivity.
Qed.

Lemma unit_reduction x : finite x -> /2 <= B x <= 2 ->
 unit_bits (bits_of_b64 x) -> B x <> 1 -> rd_z x = fsub x Ln1pReduction.c_one.
Proof.
 intros Fx X U N.
 destruct (unit_fields _ U) as [E I].
 destruct (unit_tables _ I) as [R _].
 assert (Range : bpow radix2 (-53) <= B x <= bpow radix2 1020).
 { split; [apply Rle_trans with (/2); [change (/2) with (bpow radix2 (-1)); apply bpow_le; lia | lra] |
   apply Rle_trans with 2; [lra | change 2 with (bpow radix2 1); apply bpow_le; lia]]. }
 pose proof (Ln1pReduction.reduce_ok x Fx Range) as Red. cbv zeta in Red.
 destruct Red as [_ [_ [_ [_ [_ [_ [_ [Fz [Bz _]]]]]]]]].
 rewrite E, R, (proj2 c_one_ok) in Bz. change (B (rd_z x) = B x * 1 * 1 - 1) in Bz.
 destruct (fsub_s x Ln1pReduction.c_one Fx (proj1 c_one_ok)) as [Fd Bd].
 { rewrite (proj2 c_one_ok). apply Rle_trans with 2; [apply Rabs_le; lra | change 2 with (bpow radix2 1); apply bpow_le; lia]. }
 rewrite (proj2 c_one_ok), exact_round in Bd.
 2: { apply sterbenz; [exact _ | exact _ | apply B_fmt | rewrite <- (proj2 c_one_ok); apply B_fmt | lra]. }
 assert (Strict : forall y:f64, B y<>0 -> is_finite_strict 53 1024 y=true).
 { intros y Ny. destruct y; try reflexivity; exfalso; apply Ny; reflexivity. }
 apply B2R_inj; [apply Strict; lra | apply Strict; lra | lra].
Qed.

Lemma unit_input x : unit_bits (bits_of_b64 x) ->
 finite x /\ 511/512 <= B x <= 513/512.
Proof.
 intros U. set (b:=bits_of_b64 x) in *.
 unfold unit_bits, st_off in U.
 assert (Back : x=b64_of_bits b).
 { unfold b. symmetry. apply (binary_float_of_bits_of_binary_float 52 11). }
 destruct (Z_lt_ge_dec b (1023*2^52)) as [Below | Above].
 - set (m:=(b-1022*2^52)%Z).
   assert (M : (0<=m<2^52)%Z) by (unfold m; lia).
   assert (J : b=join_bits 52 11 false m 1022) by (rewrite join_eq; unfold m; ring).
   destruct (join_val m 1022 M ltac:(lia)) as [F V].
   rewrite Back,J. split; [exact F | rewrite V].
   assert (Lo : IZR (2^53-2^44) <= IZR (m+2^52)) by (apply IZR_le; unfold m; lia).
   assert (Hi : IZR (m+2^52) <= IZR (2^53)) by (apply IZR_le; lia).
   change (8989607068696576 <= IZR (m+2^52)) in Lo.
   change (IZR (m+2^52) <= 9007199254740992) in Hi. change (bpow radix2 (1022-1075)) with (bpow radix2 (-53)). bpow_num. nra.
 - set (m:=(b-1023*2^52)%Z).
   assert (M : (0<=m<2^52)%Z) by (unfold m; lia).
   assert (J : b=join_bits 52 11 false m 1023) by (rewrite join_eq; unfold m; ring).
   destruct (join_val m 1023 M ltac:(lia)) as [F V].
   rewrite Back,J. split; [exact F | rewrite V].
   assert (Lo : IZR (2^52) <= IZR (m+2^52)) by (apply IZR_le; lia).
   assert (Hi : IZR (m+2^52) <= IZR (2^52+2^43)) by (apply IZR_le; unfold m; lia).
   change (4503599627370496 <= IZR (m+2^52)) in Lo.
   change (IZR (m+2^52) <= 4512395720392704) in Hi. change (bpow radix2 (1023-1075)) with (bpow radix2 (-52)). bpow_num. nra.
Qed.

Definition unit_parts x :=
 let z:=fsub x Ln1pReduction.c_one in
 let z2:=fmul z z in
 let t0:=fsub (fmul z (st_hc 0)) c_half in
 let t1:=fadd (fmul z (st_hc 2)) (st_hc 1) in
 let a1:=fadd (fmul z2 (st_hc 3)) t1 in
 let p:=fadd (fmul z2 a1) t0 in
 let q:=fmul z2 p in
 let eps:=fadd (fmul z2 c_kh) (fadd (fmul (b64_abs z) c_k2h) c_ah) in
 (z, fadd c_zero q, eps).

Theorem unit_parts_identical x : unit_bits (bits_of_b64 x) -> B x<>1 ->
 ln_parts 0 x = unit_parts x.
Proof.
 intros U N. destruct (unit_input x U) as [Fx X].
 destruct (unit_fields _ U) as [E I].
 destruct (unit_tables _ I) as [_ [Th Tl]].
 pose proof (unit_reduction x Fx ltac:(lra) U N) as Z.
 destruct (fsub_s x Ln1pReduction.c_one Fx (proj1 c_one_ok)) as [Fz Bz].
 { rewrite (proj2 c_one_ok). apply Rle_trans with 2; [apply Rabs_le; lra | change 2 with (bpow radix2 1); apply bpow_le; lia]. }
 rewrite (proj2 c_one_ok), exact_round in Bz.
 2: { apply sterbenz; [exact _ | exact _ | apply B_fmt | rewrite <- (proj2 c_one_ok); apply B_fmt | lra]. }
 unfold ln_parts, unit_parts. rewrite Z,Th,Tl. cbv zeta.
 replace (fadd (fmul (of_int 0) st_l1) c_zero) with c_zero by (vm_compute; reflexivity).
 replace (fadd (fmul (of_int 0) st_l0) c_zero) with c_zero by (vm_compute; reflexivity).
 rewrite (unit_add_zero _ Fz ltac:(lra)), (unit_sub_zero _ Fz), (unit_sub_self _ Fz).
 change (fadd c_zero c_zero) with c_zero. reflexivity.
Qed.

Require Import LnReduction LnStage FastLn.

Lemma unit_normalization x : unit_bits (bits_of_b64 x) ->
 exists i r, LnReduction.reduce x = (0%Z,i,x,r).
Proof.
 intros U. destruct (unit_input x U) as [Fx X].
 pose proof (LnReduction.reduce_ok x Fx ltac:(lra)) as Red.
 destruct (LnReduction.reduce x) as [[[e i]y]r] eqn:D.
 destruct Red as [I [_ [Fy [Y [_ [XY _]]]]]].
 destruct (LnReduction.ln_range i I) as [Yl [Yu _]].
 assert (E:e=0%Z).
 { destruct (Z_lt_ge_dec e 0) as [Neg | Nonneg].
   - assert (P:bpow radix2 e <= /2)
       by (change (/2) with (bpow radix2 (-1)); apply bpow_le; lia).
     pose proof (bpow_gt_0 radix2 e). nra.
   - destruct (Z.eq_dec e 0); [assumption | ].
     assert (P:2<=bpow radix2 e)
       by (change 2 with (bpow radix2 1); apply bpow_le; lia).
     nra. }
 rewrite E in XY. change (B x=1*B y) in XY.
 assert (Strict:forall v:f64, B v<>0 -> is_finite_strict 53 1024 v=true).
 { intros v N. destruct v; try reflexivity; exfalso; apply N; reflexivity. }
 assert (Same:y=x) by (apply B2R_inj; [apply Strict; lra | apply Strict; lra | lra]).
 subst e y. exists i,r. reflexivity.
Qed.

Theorem unit_fast_identical x : unit_bits (bits_of_b64 x) -> B x<>1 ->
 fast_ln_regular64 x = let '(s,lo,_) := unit_parts x in fadd s lo.
Proof.
 intros U N. destruct (unit_normalization x U) as [i [r D]].
 destruct (unit_fields _ U) as [E _].
 unfold fast_ln_regular64. rewrite D. cbv zeta iota. rewrite E. change (0+0)%Z with 0%Z.
 rewrite (unit_parts_identical x U N). reflexivity.
Qed.

Theorem unit_strong_decision_identical x : unit_bits (bits_of_b64 x) -> B x<>1 ->
 ln_stage x = let '(s,lo,eps) := unit_parts x in decide s lo eps.
Proof.
 intros U N. destruct (unit_normalization x U) as [i [r D]].
 destruct (unit_fields _ U) as [E _].
 unfold ln_stage. rewrite D. cbv zeta iota. rewrite E. change (0+0)%Z with 0%Z.
 rewrite (unit_parts_identical x U N). reflexivity.
Qed.

Theorem unit_one : let '(s,lo,_) := unit_parts (b64_of_bits 4607182418800017408) in
 fadd s lo=c_zero.
Proof. vm_compute; reflexivity. Qed.

(** Closed independent check of the maximal generated reciprocal-one block. *)
Theorem unit_table_domain : forallb (fun i =>
 Bool.eqb (Z.eqb (nth i st_r_bits 0%Z) 4607182418800017408)
          ((298 <=? i) && (i <? 301))%nat) (seq 0 512) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem unit_encoding_screen bits : (0<=bits<2^64)%Z ->
 (((bits-(st_off+298*2^43)) mod 2^64 < 3*2^43)%Z <-> unit_bits bits).
Proof.
 intros B. unfold unit_bits.
 destruct (Z_lt_ge_dec bits (st_off+298*2^43)) as [Below | Above].
 - replace ((bits-(st_off+298*2^43)) mod 2^64)%Z
     with (bits-(st_off+298*2^43)+2^64)%Z.
   2: { apply Z.mod_unique with (-1)%Z; [left; unfold st_off in *; lia | ring]. }
   unfold st_off in *. split; lia.
 - rewrite Z.mod_small by (unfold st_off in *; lia). split; lia.
Qed.
