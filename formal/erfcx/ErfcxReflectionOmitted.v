(** The omitted positive correction, bounded against the finite Gaussian
    definition using the actual exponential dispatch. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Eft IEEE64Mul IEEE64Add.
From Interval Require Import Tactic.
Require Import ExpStageTables StageGappa ExpStageReduction ExpStageB
  ErfcxReflectionReduction ErfcxReflectionSquare ErfcxReflectionExp.
Open Scope R_scope.
Theorem reflection_omitted_input x : finite x -> B reflection_limit<B x< -/2 ->
  let '(s,se):=two_prod64 x x in
  let '(h,l,k):=reflection_exp64 s se in
  (104<k)%Z -> 8<= -B x<=27.
Proof.
  intros Fx X. pose proof(reflection_square_ieee x Fx X) as Square.
  destruct(two_prod64 x x) as [s se]. destruct Square as [Fs [Fse [Exact [S Low]]]].
  pose proof(reflection_reduce_ieee s se Fs ltac:(rewrite Rabs_pos_eq;lra) Fse Low) as Red.
  unfold reflection_exp64. destruct(reflection_reduce64 s se) as [[[j k]rh]rt].
  destruct(stage_b_at rh rt (Z.to_nat j)) as [eh el].
  destruct(fast_two_sum64 eh el) as [yh yl]. intros Klarge.
  destruct Red as (ni & Nk & J & K & Frh & Frt & Grh & Rh & Rt & HR & Err).
  pose proof(Rabs_le_inv _ _ HR) as Reduced. pose proof L_range as Lr.
  assert (Ni : 53760<=IZR ni) by (apply IZR_le;lia).
  pose proof reflection_limit_value as Limit.
  split;nra.
Qed.
Lemma reflection_omitted_gaussian_budget E correction de :
  0.9993<=E<=2 -> Rabs correction<=E*bpow radix2 (-81) ->
  Rabs de<=IZR 209*bpow radix2 (-78) ->
  /4<=E-correction<=3 /\
  Rabs(((E+de)-(E-correction))/(E-correction))<=bpow radix2 (-69).
Proof.
  intros Range Correction Error. apply Rabs_le_inv in Correction,Error.
  split.
  - bpow_num_all;split;nra.
  - assert (Bound : -bpow radix2 (-69)*(E-correction)<=de+correction<=
        bpow radix2 (-69)*(E-correction)) by (bpow_num_all;split;nra).
    assert (Positive : 0<E-correction) by (bpow_num_all;nra).
    assert (Identity : (((E+de)-(E-correction))/(E-correction))*(E-correction)=de+correction)
      by (field;lra).
    apply Rabs_le;split;nra.
Qed.

Require Import ErfcxGaussianTarget ErfcxGaussianForward.
Lemma gaussian_scaled_omission p k : 8<=p<=27 ->
  Rabs(gaussian_erfcx p*bpow radix2 (-k-1))<=
    (exp(p*p)/bpow radix2 k)*bpow radix2 (-81).
Proof.
  intros P. pose proof(gaussian_omitted_relative p P) as Error.
  rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 (-k-1))) by apply bpow_ge_0.
  eapply Rle_trans with (exp(p*p)*bpow radix2 (-80)*bpow radix2 (-k-1)).
  - apply Rmult_le_compat_r;[apply bpow_ge_0|exact Error].
  - replace (-k-1)%Z with (-(k+1))%Z by lia.
    rewrite bpow_opp,bpow_plus. change (bpow radix2 1) with 2.
    right;bpow_num;field;apply Rgt_not_eq,bpow_gt_0.
Qed.
