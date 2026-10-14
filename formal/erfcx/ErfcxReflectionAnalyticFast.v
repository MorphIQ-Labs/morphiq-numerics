(** Final negative fast rounding, with every analytic contract discharged. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxGaussianTarget ErfcxDecision ErfcxReflectionSquare
  ErfcxReflectionSubtract ErfcxReflectionOverflow ErfcxReflectionFast
  ErfcxReflectionAnalytic ErfcxAccurateReflectionRange.
Open Scope R_scope.
Lemma gaussian_reflection_below_max x : finite x -> B reflection_limit<B x< -/2 ->
  gaussian_erfcx(B x)<=B erfcx_max.
Proof.
  intros Fx X. pose proof(accurate_reflection_target_range x Fx X) as Range.
  destruct erfcx_max_ok as [_ [Max _]]. rewrite Max. bpow_num_all;lra.
Qed.
Theorem reflection_fast_analytic_ieee x v : finite x -> B reflection_limit<B x< -/2 ->
  reflection_fast64 x=Some v -> finite v /\ B v=rndF(gaussian_erfcx(B x)).
Proof.
  intros Fx X. unfold reflection_fast64.
  pose proof(reflection_value_analytic_ieee x Fx X) as Value.
  destruct(reflection_value64 x) as [[h l]m].
  destruct Value as [Fh [Fl [M [H [Frange [Norm Err]]]]]].
  set(F:=gaussian_erfcx(B x)/bpow radix2 m) in *.
  assert (Rel : Rabs(F-(B h+B l))<=bpow radix2 (-67)*Rabs F).
  { unfold Rdiv in Err. rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq F) in Err by lra.
    rewrite Rabs_minus_sym,(Rabs_pos_eq F) by lra.
    replace (Rabs(B h+B l-F)) with ((Rabs(B h+B l-F)/F)*F) by (field;lra);nra. }
  assert (Hb : bpow radix2 (-900)<=Rabs(B h)<=bpow radix2 1000).
  { rewrite Rabs_pos_eq by lra;split.
    - eapply Rle_trans with(bpow radix2 (-1));[apply bpow_le;lia|change(bpow radix2 (-1))with(/2);lra].
    - eapply Rle_trans with(bpow radix2 2);[change(bpow radix2 2)with 4;lra|apply bpow_le;lia]. }
  intros Decision. pose proof Decision as D0. unfold erfcx_decide_scaled_normal64 in D0.
  destruct(erfcx_decide64 h l) as [r|] eqn:Dec;[|discriminate].
  destruct(erfcx_decide_ieee h l F r Fh Fl Hb Norm Rel Dec) as [R Round];subst r.
  assert (Target : F*bpow radix2 m=gaussian_erfcx(B x))
    by (unfold F;field;apply Rgt_not_eq,bpow_gt_0).
  assert (Mag : (-1<=mag radix2 F)%Z).
  { apply mag_ge_bpow. change(bpow radix2 (-1-1))with(/4). rewrite Rabs_pos_eq;lra. }
  assert (Scale : rndF F*bpow radix2 m=rndF(F*bpow radix2 m))
    by (symmetry;apply round_scale;lra||lia).
  assert (Overflow : B h*bpow radix2 m<bpow radix2 1024).
  { rewrite Round,Scale,Target. destruct erfcx_max_ok as [Fmax [_ Max]].
    eapply Rle_lt_trans;[|exact Max].
    apply round_le_generic;[exact _|exact _|apply B_fmt|].
    apply gaussian_reflection_below_max;assumption. }
  destruct(erfcx_decide_scaled_normal_ieee h l m F v Fh Fl H Norm Rel
    ltac:(lra) M Overflow Decision) as [Fv Bv].
  rewrite Target in Bv;split;assumption.
Qed.
