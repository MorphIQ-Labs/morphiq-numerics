(** Exact power-of-two scaling before erfcx's largest-input quotient. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxEntryTables ErfcxQuotient.
Open Scope R_scope.
Definition scale600 : f64 := b64_of_bits 1905022642377719808.
Lemma scale600_ok : finite scale600 /\ B scale600 = bpow radix2 (-600).
Proof.
 split.
 - exact (bits_finite 1905022642377719808 false 4503599627370496 (-652) eq_refl).
 - pose proof (bits_val 1905022642377719808 false 4503599627370496 652 eq_refl) as V.
   unfold scale600. rewrite V. bpow_num. simpl. field.
Qed.

Lemma scale_input_ieee x : finite x -> bpow radix2 896 <= B x ->
 finite (fmul x scale600) /\ B (fmul x scale600)=B x*bpow radix2 (-600) /\
 bpow radix2 296 <= B (fmul x scale600) <= bpow radix2 424.
Proof.
 intros Fx X. destruct scale600_ok as [Fk Bk].
 assert (Pos : 0<=B x) by (pose proof (bpow_gt_0 radix2 896); lra).
 assert (Upper : B x <= bpow radix2 1024).
 { pose proof (abs_B2R_lt_emax 53 1024 x) as U.
   rewrite Rabs_pos_eq in U by lra. lra. }
 assert (Range : bpow radix2 296 <= B x*bpow radix2 (-600) <= bpow radix2 424).
 { split.
   - replace (bpow radix2 296) with (bpow radix2 896*bpow radix2 (-600))
       by (rewrite <- bpow_plus; reflexivity).
     apply Rmult_le_compat_r; [apply bpow_ge_0 | exact X].
   - replace (bpow radix2 424) with (bpow radix2 1024*bpow radix2 (-600))
       by (rewrite <- bpow_plus; reflexivity).
     apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Upper]. }
 destruct (fmul_ok 1 424 x scale600 Fx Fk ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l,Bk,Rabs_pos_eq;
        [lra | apply Rmult_le_pos; [exact Pos | apply bpow_ge_0]])) as [Fs Bs].
 rewrite Bk in Bs.
 assert (Fmt : fmtF (B x*bpow radix2 (-600))).
 { apply mult_bpow_exact_FLT; [apply B_fmt | ].
   assert (M : (897 <= mag radix2 (B x))%Z).
   { apply mag_ge_bpow. change (bpow radix2 (897-1)) with (bpow radix2 896).
     rewrite Rabs_pos_eq by lra; exact X. }
   unfold emin,prec. lia. }
 rewrite round_generic in Bs by (exact _ || exact Fmt).
 rewrite Bs. repeat split; tauto.
Qed.

Definition scaled_quotient64 x := normalized_quotient64 (fmul x scale600).

Theorem scaled_quotient_ieee x : finite x -> bpow radix2 896 <= B x ->
 let '(h,l) := scaled_quotient64 x in
 finite h /\ finite l /\
 - bpow radix2 (-70) <=
  ((B h+B l)*bpow radix2 (-600)-(B cs+B csl)/B x)/((B cs+B csl)/B x) <= bpow radix2 (-70).
Proof.
 intros Fx X. destruct (scale_input_ieee x Fx X) as [Fs [Bs S]].
 assert (Domain : 512 <= B (fmul x scale600) <= bpow radix2 897).
 { split.
   - apply Rle_trans with (bpow radix2 296); [change 512 with (bpow radix2 9); apply bpow_le; lia | lra].
   - apply Rle_trans with (bpow radix2 424); [lra | apply bpow_le; lia]. }
 pose proof (normalized_quotient_ieee (fmul x scale600) Fs Domain) as Q.
 unfold scaled_quotient64. destruct (normalized_quotient64 (fmul x scale600)) as [h l].
 destruct Q as [Fh [Fl E]]. rewrite Bs in E.
 assert (Id : ((B h+B l)-(B cs+B csl)/(B x*bpow radix2 (-600)))/((B cs+B csl)/(B x*bpow radix2 (-600)))
 = ((B h+B l)*bpow radix2 (-600)-(B cs+B csl)/B x)/((B cs+B csl)/B x)).
 { assert (Cpos : 0<B cs+B csl).
   { destruct cs_ok as [_ [C _]]. destruct csl_ok as [_ [L _]]. rewrite C,L.
     unfold cs_r,csl_r,float2R,F2R; simpl; bpow_num; lra. }
   pose proof (bpow_gt_0 radix2 (-600)). pose proof (bpow_gt_0 radix2 896).
   field. repeat split; lra. }
 rewrite Id in E. repeat split; tauto.
Qed.
