(** The low-word correction, with its two binary64 roundings. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 Grid.
From Interval Require Import Tactic.
Require Import ExpFast LnFastAdd LnFastPoly LnFastCertificates Ln1pLemmas.
Open Scope R_scope.
Lemma lf_relative v w : Rabs(w-v)<=lf_u*Rabs v ->
 exists e, Rabs e<=lf_u /\ w=v*(1+e).
Proof.
 intros E. destruct (Req_dec v 0) as [Z | N].
 - subst v. rewrite Rabs_R0,Rmult_0_r,Rminus_0_r in E. exists 0. rewrite Rabs_R0. split; [unfold lf_u; lra | apply Rabs_le_inv in E; lra].
 - exists ((w-v)/v). split.
   + apply ratio_bound; [apply Rabs_pos_lt; exact N | exact E].
   + field; exact N.
Qed.
Definition lf_correction x l := fsub (lf_tail x) (fmul x l).
Theorem lf_correction_ok x l : finite x -> finite l -> Rabs(B x)<=/32 -> Rabs(B l)<=1 ->
 on_grid (-116) (B x) -> on_grid (-232) (B l) ->
 finite (lf_correction x l) /\ Rabs(B (lf_correction x l))<=1 /\
 exists ec eu, Rabs ec<=lf_u /\ Rabs eu<=lf_u /\
 B (lf_correction x l)=(B (lf_tail x)-B x*B l*(1+ec))*(1+eu).
Proof.
 intros Fx Fl X L Gx Gl.
 destruct (fmul_p (-5) x l Fx Fl ltac:(lia)) as [Fc [Vc Ac]].
 - change (bpow radix2 (-5)) with (/32). rewrite Rabs_mult. pose proof (Rabs_pos (B x)); pose proof (Rabs_pos (B l)); nra.
 - assert (N : normal_or_zero (B x*B l)).
   { destruct (Req_dec (B x*B l) 0) as [Z | N]; [left; exact Z | right].
     apply Rle_trans with (bpow radix2 (-348)); [apply bpow_le; lia | apply grid_nonzero; [change (-348)%Z with (-116 + -232)%Z; apply grid_mult; assumption | exact N]]. }
   assert (E : Rabs (B (fmul x l)-B x*B l)<=lf_u*Rabs(B x*B l)).
   { rewrite Vc,normal_round by exact N.
     pose proof (relative_error_N_FLX radix2 prec ltac:(unfold prec; lia) ne (B x*B l)) as E.
     replace (/2*bpow radix2 (-prec+1)) with lf_u in E by (unfold prec,lf_u; simpl; lra). exact E. }
   destruct (lf_relative _ _ E) as [ec [Ec VC]].
   destruct (lf_tail_ok x Fx X) as [Ft [Vt At]].
   destruct (fsub_bnd 1 0 (lf_tail x) (fmul x l) Ft Fc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fu [Vu Au]].
   + unfold bnd. change (IZR 1*bpow radix2 0) with (1*1). change (bpow radix2 (-5)) with (/32) in Ac.
     apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra.
   + unfold bnd in Au. change (IZR 1*bpow radix2 0) with (1*1) in Au.
     pose proof (lf_sum_error (B (lf_tail x)) (-B (fmul x l)) (B_fmt _) (generic_format_opp _ _ _ (B_fmt _))) as Eu.
     change (Rabs(rndF(B (lf_tail x)-B (fmul x l))-(B (lf_tail x)-B (fmul x l)))<=lf_u*Rabs(B (lf_tail x)-B (fmul x l))) in Eu.
     rewrite <-Vu in Eu. destruct (lf_relative _ _ Eu) as [eu [EU VU]].
     split; [exact Fu | split; [unfold lf_correction; lra | exists ec,eu; repeat split; try assumption; rewrite <-VC; exact VU]].
Qed.
