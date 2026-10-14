(** Compose table arithmetic with its certified approximation budget and the
    actual 2^-66 guard. The analytic target and approximation contract are explicit. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxTableEntry ErfcxTableBound.
Open Scope R_scope.

Lemma table_composed_error y p f : 0<f ->
 Rabs ((p-f)/f)<=bpow radix2 (-69) -> Rabs ((y-p)/p)<=/2^67 ->
 Rabs (f-y)<=3*bpow radix2 (-68)*Rabs f.
Proof.
 intros F Approx Eval.
 assert (Pidentity : p=(1+(p-f)/f)*f) by (field; lra).
 assert (Ppos : 0<p).
 { pose proof (Rabs_le_inv _ _ Approx). set (a := (p-f)/f) in *.
   clear - F Pidentity H. bpow_num_all. nra. }
 assert (Identity : (y-f)/f=((y-p)/p)*(1+(p-f)/f)+(p-f)/f) by (field; lra).
 assert (Relative : Rabs ((y-f)/f)<=3*bpow radix2 (-68)).
 { rewrite Identity. pose proof (Rabs_le_inv _ _ Approx). pose proof (Rabs_le_inv _ _ Eval).
   set (a := (p-f)/f) in *. set (e := (y-p)/p) in *.
   apply Rabs_le. clear - H H0. bpow_num_all. nra. }
 assert (Yidentity : y-f=((y-f)/f)*f) by (field; lra).
 rewrite Rabs_minus_sym,Yidentity,Rabs_mult.
 apply Rmult_le_compat_r; [apply Rabs_pos | exact Relative].
Qed.

Definition table_fast64 x :=
 let '(h,l) := table_eval64 x in erfcx_decide64 h l.

Theorem table_fast_ieee x f v : finite x -> -/2<=B x<16 -> 0<f ->
 Rabs ((table_exact x-f)/f)<=bpow radix2 (-69) ->
 table_fast64 x=Some v -> finite v /\ B v=rndF f.
Proof.
 intros Fx X F Approx.
 pose proof (table_evaluation_error x Fx X) as E.
 pose proof (table_eval_normalized_ieee x Fx X) as W.
 unfold table_fast64. destruct (table_eval64 x) as [h l].
 destruct E as (_ & _ & Eval). destruct W as (Fh & Fl & Value & Norm & H).
 pose proof (table_composed_error (B h+B l) (table_exact x) f F Approx Eval) as Error.
 destruct erfcx_eps_ok as [Fe Eps].
 assert (Hb : bpow radix2 (-900)<=Rabs (B h)<=bpow radix2 1000).
 { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-9)); lra). split.
   - apply Rle_trans with (bpow radix2 (-9)); [apply bpow_le; lia | lra].
   - apply Rle_trans with 8; [lra | change 8 with (bpow radix2 3); apply bpow_le; lia]. }
 intros Decision.
 destruct (decide_with_ok h l erfcx_eps f (3*bpow radix2 (-68)) v Fh Fl Fe Hb Norm)
   as [V Round].
 - bpow_num. split; lra.
 - rewrite Eps. bpow_num. split; lra.
 - exact Error.
 - exact Decision.
 - subst v. split; [exact Fh | symmetry; exact Round].
Qed.
