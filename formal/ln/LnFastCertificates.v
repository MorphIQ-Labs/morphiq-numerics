(** The fast-path Gappa certificates, applied without extra assumptions. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
Require Import LnFastTables Ln1pCertificates StageGappa.
Require ln_tail ln_p.
Open Scope R_scope.
Definition lf_wr x := rn (lf_a3 + rn (x * (rn (lf_a4 + rn (x * (rn (lf_a5 + rn (x * (rn (lf_a6 + rn (x * (rn (lf_a7 + rn (x * (rn (lf_a8 + rn (x * (lf_a9)))))))))))))))))).
Definition lf_tr x := rn (rn (x*rn(x*x))*lf_wr x).
Ltac lf_real_coefficients := rewrite lf_c3_real, lf_c4_real, lf_c5_real, lf_c6_real,
 lf_c7_real, lf_c8_real, lf_c9_real.
Lemma lf_tail_certificate x : rn x = x -> /2^64 <= Rabs x <= 0.0078126 ->
 Rabs ((lf_tr x-x*x*x*lf_w x)/(x*x*x*lf_w x)) <= /2^50.
Proof.
 intros Rx X. unfold lf_tr, lf_wr, lf_w, lf_a3, lf_a4, lf_a5, lf_a6, lf_a7, lf_a8, lf_a9.
 apply Rnot_lt_le; intros Hlt. apply (ln_tail.l1 x). split.
 - gnorm. rewrite Rx. simpl. lra.
 - intros Hb. gnorm_in Hb. rewrite Rx in Hb. gnorm_in Hlt.
   apply (Rlt_irrefl (/2^50)). apply Rlt_le_trans with (1:=Hlt).
   apply Rabs_le. simpl in Hb |- *. gnorm_in Hb. simpl in Hb. lra.
Qed.
Lemma lf_p_certificate x dl et ec eu al d1 d2 : /2^64 <= Rabs x <= 0.0078126 ->
 Rabs dl <= /2^53 -> Rabs et <= /2^50 -> Rabs ec <= /2^53 -> Rabs eu <= /2^53 ->
 Rabs al <= 535/2^63 -> Rabs d1 <= 776/2^114 -> Rabs d2 <= /2^105 ->
 let z := x+x*dl in
 let T := x*x*x*lf_w x in
 let L := z-z*z/2+z*z*z*lf_w z+al*(z*z*z*lf_w z) in
 Rabs ((((z-x*x/2)*(1+d1)+(T*(1+et)-x*(x*dl)*(1+ec))*(1+eu))*(1+d2)-L)/L) <= 3/2^66.
Proof.
 intros X Dl Et Ec Eu Al D1 D2. cbv zeta.
 unfold lf_w, lf_a3, lf_a4, lf_a5, lf_a6, lf_a7, lf_a8, lf_a9.
 apply Rabs_le_inv in Dl. apply Rabs_le_inv in Et. apply Rabs_le_inv in Ec.
 apply Rabs_le_inv in Eu. apply Rabs_le_inv in Al. apply Rabs_le_inv in D1. apply Rabs_le_inv in D2.
 apply Rnot_lt_le; intros Hlt. apply (ln_p.l1 x dl al d1 et ec eu d2). split.
 - gnorm. repeat split; simpl; lra.
 - intros Hb. gnorm_in Hb. gnorm_in Hlt. simpl in Hb |- *.
   apply (Rlt_irrefl (3/2^66)). apply Rlt_le_trans with (1:=Hlt). apply Rabs_le. simpl in Hb |- *. gnorm_in Hb. simpl in Hb. lra.
Qed.
