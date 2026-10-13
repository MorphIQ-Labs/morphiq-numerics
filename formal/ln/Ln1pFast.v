(** Both double-word fallback branches of ln_1p. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid.
From Interval Require Import Tactic.
Require Import ExpFast LnAccurate LnFastKernel LnFastAdd Ln1pFastGeneral Ln1pLemmas.
Open Scope R_scope.
Definition lf_ln1p_fast_value x := if small7 x then lf_polynomial x c_zero else lf_ln1p_general_value x.
Theorem lf_ln1p_fast_value_ok x : finite x -> -1<B x -> bpow radix2 (-54)<=Rabs(B x) ->
 let '(h,l):=lf_ln1p_fast_value x in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=2048 /\ Rabs(B l)<=4096 /\
 Rabs(B h+B l-ln(1+B x))<=/2^63*Rabs(ln(1+B x)).
Proof.
 intros Fx X Ax. unfold lf_ln1p_fast_value. destruct (small7 x) eqn:S.
 - apply (proj1 (small7_ok x Fx)) in S. change (bpow radix2 (-7)) with (/128) in S.
   pose proof (lf_polynomial_ok x c_zero Fx c_zero_finite) as P.
   rewrite c_zero_val,Rplus_0_r,Rabs_R0 in P.
   assert (D : B x=rndF(B x)) by (symmetry; apply round_generic; auto with typeclass_instances; apply B_fmt).
   specialize (P ltac:(split; [apply Rle_trans with (2:=Ax); interval with (i_prec 100) | lra]) ltac:(lra) D
    ltac:(apply Rmult_le_pos; [unfold lf_u; lra | apply Rabs_pos]) (grid_0 _)).
   destruct (lf_polynomial x c_zero) as [h l]. destruct P as [Fh [Fl [Dw E]]]. rewrite Rplus_0_r in E.
   assert (Bound : Rabs(B h+B l-ln(1+B x))<=/2^63*Rabs(ln(1+B x))).
   { apply Rle_trans with (1:=E); apply Rmult_le_compat_r; [apply Rabs_pos | interval with (i_prec 100)]. }
   assert (Log : Rabs(ln(1+B x))<=1).
   { pose proof (Rabs_le_inv (B x) (/128) ltac:(lra)). interval with (i_prec 100). }
   assert (Small : Rabs(B h+B l)<=2).
   { pose proof (Rabs_triang_inv (B h+B l) (ln(1+B x))). assert (/2^63<=1) by interval with (i_prec 100).
     pose proof (Rabs_pos (ln(1+B x))); nra. }
   assert (H : Rabs(B h)<=2) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 1); lia | exact Small]).
   assert (L : Rabs(B l)<=4).
   { replace (B l) with ((B h+B l)-B h) by ring; apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
   repeat split; try assumption; lra.
 - apply lf_ln1p_general_ok; try assumption.
   destruct (Rle_or_lt (/128) (Rabs(B x))) as [A | A]; [exact A | ].
   assert (small7 x=true) by (apply (proj2 (small7_ok x Fx)); exact A). congruence.
Qed.
