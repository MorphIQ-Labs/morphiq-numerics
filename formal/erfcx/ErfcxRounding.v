(** Relative plus absolute binary64 rounding error, including gradual underflow. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add.
Require Import StageGappa.
Open Scope R_scope.

Lemma rounding_decomposition x : exists d a,
 - bpow radix2 (-53) <= d <= bpow radix2 (-53) /\
 - bpow radix2 (-1075) <= a <= bpow radix2 (-1075) /\
 rndF x = x*(1+d)+a.
Proof.
 destruct (Rle_dec (bpow radix2 (-1022)) (Rabs x)) as [Normal|Small].
 - destruct (relative_error_N_FLT_ex radix2 emin prec ltac:(unfold prec;lia) ne x Normal) as [d [D E]].
   exists d,0. replace (/2*bpow radix2 (-prec+1)) with (bpow radix2 (-53)) in D
     by (unfold prec; change (/2) with (bpow radix2 (-1)); rewrite <- bpow_plus; reflexivity).
   pose proof (Rabs_le_inv _ _ D). pose proof (bpow_gt_0 radix2 (-1075)).
   change (rndF x=x*(1+d)) in E. repeat split; lra.
 - exists 0,(rndF x-x).
   assert (Err : Rabs (rndF x-x) <= bpow radix2 (-1075)).
   { pose proof (@error_le_half_ulp radix2 (FLT_exp emin prec) (ltac:(exact _)) ne x) as E.
     rewrite ulp_FLT_small in E.
     - replace (/2*bpow radix2 emin) with (bpow radix2 (-1075)) in E
         by (unfold emin; change (/2) with (bpow radix2 (-1)); rewrite <- bpow_plus; reflexivity). exact E.
     - exact _.
     - apply Rlt_le_trans with (bpow radix2 (-1022)); [lra | apply bpow_le; unfold emin,prec;lia]. }
   pose proof (Rabs_le_inv _ _ Err). pose proof (bpow_gt_0 radix2 (-53)).
   repeat split; lra.
Qed.

Lemma normalized_absolute_error q a : bpow radix2 (-899) <= q ->
 -bpow radix2 (-1075) <= a <= bpow radix2 (-1075) ->
 -bpow radix2 (-170) <= a/q <= bpow radix2 (-170).
Proof.
 intros Q A.
 assert (Pos : 0<q) by (pose proof (bpow_gt_0 radix2 (-899)); lra).
 assert (Bound : bpow radix2 (-1075) <= bpow radix2 (-170)*q).
 { apply Rle_trans with (bpow radix2 (-170)*bpow radix2 (-899)).
   - rewrite <- bpow_plus. apply bpow_le; lia.
   - apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Q]. }
 assert (Id : a=(a/q)*q) by (field; lra).
 pose proof (bpow_gt_0 radix2 (-170)). nra.
Qed.

Lemma normalized_rounding x q : bpow radix2 (-899) <= q ->
 exists d a, -bpow radix2 (-53) <= d <= bpow radix2 (-53) /\
 -bpow radix2 (-170) <= a <= bpow radix2 (-170) /\
 rndF x/q=(x/q)*(1+d)+a.
Proof.
 intros Q. destruct (rounding_decomposition x) as [d [a [D [A E]]]].
 exists d,(a/q). split; [exact D | ]. split.
 - apply normalized_absolute_error; assumption.
 - rewrite E. field. pose proof (bpow_gt_0 radix2 (-899)); lra.
Qed.
