(** Direct IEEE quotient correction for both erfcx positive-tail scales. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal ErfcxEntryTables ErfcxQuotientBounds.
Open Scope R_scope.
Definition quotient64 x : f64*f64 :=
 let q := fdiv cs x in
 let '(p,pe) := two_prod64 q x in
 (q, fdiv (fadd (fsub (fsub cs p) pe) csl) x).

Theorem quotient_ieee x : finite x -> 512 <= B x <= bpow radix2 897 ->
 let '(q,ql) := quotient64 x in
 finite q /\ finite ql /\
 - bpow radix2 (-70) <= ((B q+B ql)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= bpow radix2 (-70) /\
 - bpow radix2 (-51) <= B ql/B q <= bpow radix2 (-51) /\
 bpow radix2 (-899) <= B q <= bpow radix2 (-9).
Proof.
 intros Fx X.
 assert (Inv : 0 < /B x <= /512).
 { split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
 destruct cs_ok as [Fc [Bc Ac]]. destruct csl_ok as [Fcl [Bcl Acl]].
 assert (Ch : 1/2 <= B cs <= 5/8).
 { rewrite Bc. unfold cs_r,float2R,F2R; simpl; bpow_num; split; lra. }
 assert (Rx : rn (B x) = B x) by (apply round_generic; [exact _ | apply B_fmt]).
 pose proof (quotient_model (B x) ltac:(rewrite Rx; exact X)) as M.
 unfold quotient_bounds in M. destruct M as [Merr [Mratio [Mq [Mp [Me [Mr1 [Mr Mql]]]]]]].
 destruct (fdiv_ok 1 0 cs x Fc ltac:(lra) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
        unfold Rdiv; apply Rabs_le; nra)) as [Fq Bq].
 assert (Qeq : B (fdiv cs x) = q_high (B x)).
 { unfold q_high. rewrite Rx,<-Bc. exact Bq. }
 rewrite <- Qeq in Mq.
 pose proof (two_prod_ieee (-9) 897 (fdiv cs x) x Fq Fx
  ltac:(rewrite Rabs_pos_eq; [lra | apply Rle_trans with (bpow radix2 (-899)); [apply bpow_ge_0 | lra]])
  ltac:(rewrite Rabs_pos_eq by lra; lra)
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(right; rewrite Rabs_mult; rewrite (Rabs_pos_eq (B x)) by lra;
        rewrite (Rabs_pos_eq (B (fdiv cs x))) by (apply Rle_trans with (bpow radix2 (-899)); [apply bpow_ge_0 | lra]);
        apply Rle_trans with (bpow radix2 (-899)*bpow radix2 9);
        [rewrite <- bpow_plus; apply bpow_le; lia |
         apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | lra | change (bpow radix2 9) with 512; lra]])) as TP.
 unfold quotient64. destruct (two_prod64 (fdiv cs x) x) as [p pe].
 destruct TP as [Fp [Fpe [Bp Epe]]].
 assert (Peq : B p = q_product (B x)).
 { unfold q_product. rewrite Rx,<-Qeq. exact Bp. }
 assert (Eeq : B pe = q_error (B x)).
 { unfold q_error. rewrite Rx,<-Qeq,<-Peq. lra. }
 rewrite <- Peq in Mp. rewrite <- Eeq in Me.
 assert (Fmt : fmtF (B cs-B p)).
 { apply sterbenz; try exact _. all: try apply B_fmt. lra. }
 destruct (fsub_ok 1 0 cs p Fc Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; lra)) as [Fd Bd].
 rewrite round_generic in Bd by (exact _ || exact Fmt).
 destruct (fsub_ok 2 0 (fsub cs p) pe Fd Fpe ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r,Bd;
        bpow_num_all; apply Rabs_le; lra)) as [Fr1 Br1].
 assert (R1eq : B (fsub (fsub cs p) pe) = q_residual1 (B x)).
 { unfold q_residual1. rewrite <- Peq,<-Eeq,<-Bc,Br1,Bd. reflexivity. }
 rewrite <- R1eq in Mr1.
 destruct (fadd_ok 65537 0 (fsub (fsub cs p) pe) csl Fr1 Fcl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        rewrite <- Bcl in Acl; pose proof (Rabs_le_inv _ _ Acl);
        bpow_num_all; apply Rabs_le; lra)) as [Fr Br].
 assert (Req : B (fadd (fsub (fsub cs p) pe) csl) = q_residual (B x)).
 { unfold q_residual. rewrite <- R1eq,<-Bcl. exact Br. }
 rewrite <- Req in Mr.
 destruct (fdiv_ok 1 0 (fadd (fsub (fsub cs p) pe) csl) x Fr ltac:(lra)
  ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
        unfold Rdiv; bpow_num_all; apply Rabs_le; nra)) as [Fql Bql].
 assert (Leq : B (fdiv (fadd (fsub (fsub cs p) pe) csl) x) = q_low (B x)).
 { unfold q_low. rewrite Rx,<-Req. exact Bql. }
 rewrite <- Qeq,<-Leq,Rx,<-Bc,<-Bcl in Merr.
 rewrite <- Qeq,<-Leq in Mratio. repeat split; tauto.
Qed.

Definition normalized_quotient64 x : f64*f64 :=
 let '(q,ql) := quotient64 x in fast_two_sum64 q ql.

Theorem normalized_quotient_words_ieee x : finite x -> 512 <= B x <= bpow radix2 897 ->
 let '(h,l) := normalized_quotient64 x in
 finite h /\ finite l /\
 - bpow radix2 (-70) <= ((B h+B l)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= bpow radix2 (-70) /\
 B h = rndF (B h+B l).
Proof.
 intros Fx X. pose proof (quotient_ieee x Fx X) as Q.
 unfold normalized_quotient64. destruct (quotient64 x) as [q ql].
 destruct Q as [Fq [Fql [E [R H]]]].
 assert (Pos : 0<B q) by (pose proof (bpow_gt_0 radix2 (-899)); lra).
 assert (Id : B ql=(B ql/B q)*B q) by (field; lra).
 assert (Dom : Rabs (B ql) <= Rabs (B q)).
 { rewrite (Rabs_pos_eq (B q)) by lra. bpow_num_all; apply Rabs_le; nra. }
 assert (Qb : Rabs (B q) <= 1).
 { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-9)); [lra | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
 pose proof (fast_two_sum_ieee q ql Fq Fql
   ltac:(apply Rle_trans with 1; [exact Qb | change 1 with (bpow radix2 0); apply bpow_le; lia])
   ltac:(apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
   ltac:(right; left; exact Dom)) as FS.
 destruct (fast_two_sum64 q ql) as [h l].
 destruct FS as [Fh [Fl [High Sum]]].
 split; [exact Fh | split; [exact Fl | split; [rewrite Sum; exact E | rewrite Sum; exact High]]].
Qed.


Theorem normalized_quotient_ieee x : finite x -> 512 <= B x <= bpow radix2 897 ->
 let '(h,l) := normalized_quotient64 x in
 finite h /\ finite l /\
 - bpow radix2 (-70) <= ((B h+B l)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= bpow radix2 (-70).
Proof.
 intros Fx X. pose proof (normalized_quotient_words_ieee x Fx X) as Q.
 destruct (normalized_quotient64 x) as [h l]. tauto.
Qed.
