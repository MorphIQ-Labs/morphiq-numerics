(** The fast-path Gappa certificates, applied without extra assumptions. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
Require Import Expm1Tables Ln1pCertificates StageGappa.
Require expm1_tail expm1_p.
Open Scope R_scope.
Definition em_wr x := rn (em_a3 + rn (x * (rn (em_a4 + rn (x * (rn (em_a5 + rn (x * (rn (em_a6 + rn (x * (rn (em_a7 + rn (x * (rn (em_a8 + rn (x * (em_a9)))))))))))))))))).
Definition em_tr x := rn (rn (x*rn(x*x))*em_wr x).
Ltac em_real_coefficients := rewrite em_c3_real, em_c4_real, em_c5_real, em_c6_real,
 em_c7_real, em_c8_real, em_c9_real.
Lemma em_tail_certificate x : rn x = x -> /2^54 <= Rabs x <= 0.0312501 ->
 Rabs ((em_tr x-x*x*x*em_w x)/(x*x*x*em_w x)) <= /2^50.
Proof.
 intros Rx X. unfold em_tr, em_wr, em_w. em_real_coefficients.
 apply Rnot_lt_le; intros Hlt. apply (expm1_tail.l1 x). split.
 - gnorm. rewrite Rx. simpl. lra.
 - intros Hb. gnorm_in Hb. rewrite Rx in Hb. gnorm_in Hlt.
   apply (Rlt_irrefl (/2^50)). apply Rlt_le_trans with (1:=Hlt).
   apply Rabs_le. simpl in Hb |- *. lra.
Qed.
Lemma em_p_certificate x al d1 et d2 : /2^54 <= Rabs x <= 0.0312501 ->
 Rabs al <= 518/2^63 -> Rabs d1 <= 776/2^114 -> Rabs et <= /2^50 -> Rabs d2 <= /2^105 ->
 let T := x*x*x*em_w x in
 let L := x+x*x/2+T*(1+al) in
 Rabs ((((x+x*x/2)*(1+d1)+T*(1+et))*(1+d2)-L)/L) <= 13/2^66.
Proof.
 intros X A D1 E D2. cbv zeta. unfold em_w. em_real_coefficients.
 apply Rabs_le_inv in A. apply Rabs_le_inv in D1. apply Rabs_le_inv in E. apply Rabs_le_inv in D2.
 apply Rnot_lt_le; intros Hlt. apply (expm1_p.l1 x al d1 et d2). split.
 - gnorm. repeat split; simpl; lra.
 - intros Hb. gnorm_in Hb. gnorm_in Hlt. simpl in Hb |- *.
   apply (Rlt_irrefl (13/2^66)). apply Rlt_le_trans with (1:=Hlt). apply Rabs_le. simpl in Hb |- *. lra.
Qed.
