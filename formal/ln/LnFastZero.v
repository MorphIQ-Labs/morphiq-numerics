(** The exact-zero residual, including all input zero signs. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import LnFastKernel.
Open Scope R_scope.
Lemma lf_finite_zero x : finite x -> B x=0 -> exists s, x=B754_zero 53 1024 s.
Proof.
 intros F Z. destruct x as [s | s | s p H | s m e H]; try discriminate.
 - exists s; reflexivity.
 - pose proof (abs_B2R_ge_emin 53 1024 (B754_finite 53 1024 s m e H) eq_refl) as A.
   rewrite Z,Rabs_R0 in A. pose proof (bpow_gt_0 radix2 (3-1024-53)). lra.
Qed.
Theorem lf_polynomial_zero x l : finite x -> finite l -> B x=0 -> B l=0 ->
 let '(h,t):=lf_polynomial x l in finite h /\ finite t /\ B h=0 /\ B t=0.
Proof.
 intros Fx Fl X L. destruct (lf_finite_zero x Fx X) as [s ->]. destruct (lf_finite_zero l Fl L) as [t ->].
 destruct s,t; vm_compute; repeat split; reflexivity.
Qed.
