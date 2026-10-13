(** The shared polynomial after ln's exact reciprocal reduction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid.
From Interval Require Import Tactic.
Require Import LnTables LnReduction LnFastKernel LnFastZero LnFastAdd Ln1pLemmas.
Open Scope R_scope.
Definition lf_reduced_poly y i := let '(h,l):=reduce_z y (ln_r i) in lf_polynomial h l.
Theorem lf_reduced_poly_ok y i : (i<128)%nat -> finite y -> ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
 let '(h,l):=lf_reduced_poly y i in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=1 /\ Rabs(B l)<=2 /\
 Rabs(B h+B l-ln(B y*B (ln_r i)))<=3/2^66*Rabs(ln(B y*B (ln_r i))).
Proof.
 intros I Fy Y Gy. pose proof (z_ok y i I Fy Y Gy) as Z.
 destruct (z_range y i I Y Gy) as [Pr [Az Gz]].
 unfold lf_reduced_poly. destruct (reduce_z y (ln_r i)) as [zh zl].
 destruct Z as [Fh [Fl [Vz [Dz [A [L Z]]]]]].
 assert (Zh : Rabs(B zh)<=/128) by (rewrite Dz; apply rnd_bound; [apply (fmt_pow (-7)); lia | exact A]).
 assert (G : on_grid (-232) (B zl)).
 { apply (grid_le (-63)); [lia | ]. replace (B zl) with ((B y*B (ln_r i)-1)-B zh) by lra.
   apply grid_minus; [exact Gz | rewrite Dz,Vz; apply grid_round; [exact _ | exact _ | exact Gz]]. }
 assert (P : let '(h,l):=lf_polynomial zh zl in finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h+B l-ln(B y*B (ln_r i)))<=3/2^66*Rabs(ln(B y*B (ln_r i)))).
 { destruct Z as [[Z0 L0] | Z].
   - pose proof (lf_polynomial_zero zh zl Fh Fl Z0 L0) as P.
     destruct (lf_polynomial zh zl) as [h l]. destruct P as [H [T [Vh Vl]]].
     assert (Yr : B y*B (ln_r i)=1) by lra. rewrite Vh,Vl,Yr,ln_1,Rplus_0_l,Rminus_0_l,Ropp_0,Rabs_R0,Rmult_0_r.
     repeat split; try assumption; try lra. symmetry; apply round_0; exact _.
   - pose proof (lf_polynomial_ok zh zl Fh Fl ltac:(split; [apply Rle_trans with (2:=Z); interval with (i_prec 100) | lra])
       ltac:(lra) Dz ltac:(unfold lf_u; change (bpow radix2 (-53)) with (/9007199254740992) in L; exact L) G) as P.
     replace (1+B zh+B zl) with (B y*B (ln_r i)) in P by lra. exact P. }
 destruct (lf_polynomial zh zl) as [h l]. destruct P as [Fh' [Fl' [Dw E]]].
 assert (Log : Rabs(ln(B y*B (ln_r i)))<=/64).
 { apply Rabs_le_inv in Az. generalize Az. generalize (B y*B (ln_r i)). intros v Av. assert (0.99<=v<=1.01) by lra. interval with (i_prec 100). }
 assert (Small : Rabs(B h+B l)<=1).
 { pose proof (Rabs_triang_inv (B h+B l) (ln(B y*B (ln_r i)))).
   assert (3/2^66<=1) by interval with (i_prec 100). pose proof (Rabs_pos (ln(B y*B (ln_r i)))); nra. }
 assert (H : Rabs(B h)<=1) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 0); lia | exact Small]).
 assert (T : Rabs(B l)<=2).
 { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
 repeat split; assumption.
Qed.
