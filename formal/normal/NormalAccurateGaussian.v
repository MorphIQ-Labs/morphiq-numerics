(** Q256 Gaussian factor: the exact original binary64 square is passed to
    the shared signed exponential reduction, then scaled by one half. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalGaussianKernel ErfcxAccurateExponential
  ErfcxAccurateTerms.
Open Scope R_scope.

Definition normal_q_gaussian_regular x :=
  let '(h,l) := normal_half_square64 x in
  mul_pow2 (q_reflection_exponential h l) (-1).

Theorem normal_q_gaussian_regular_error x : finite x ->
  bpow radix2 (-400)<=B x<=38.6 ->
  valid (normal_q_gaussian_regular x) /\ exists e,
  Rabs e<=bpow radix2 (-238) /\
  qval (normal_q_gaussian_regular x)=exp(-B x*B x/2)*(1+e).
Proof.
  intros F X.
  pose proof(normal_half_square_exact x F ltac:(split;lra)) as Square.
  unfold normal_q_gaussian_regular.
  destruct(normal_half_square64 x) as [h l].
  destruct Square as [Fh [Fl [Exact [H L]]]].
  assert (Domain : -745.1333<=B h<=709.79).
  { assert (Low : Rabs(B l)<=/16).
    { apply Rle_trans with(bpow radix2 (-44));[exact L|interval with(i_prec 80)]. }
    apply Rabs_le_inv in Low. pose proof(bpow_gt_0 radix2 (-400)).
    split;nra. }
  destruct(q_reflection_exponential_error h l Fh Fl Domain L)
    as [Q [e [E Value]]].
  destruct(mul_pow2_any _ (-1) Q) as [Result Scaled].
  split;[exact Result|]. exists e. split;[exact E|].
  rewrite Scaled,Value,Exact. change(bpow radix2 (-1))with(/2). field.
Qed.

Theorem normal_q_gaussian_tiny_error x : Rabs x<=bpow radix2 (-400) ->
  valid q_one /\ exists e, Rabs e<=bpow radix2 (-799) /\
  qval q_one=exp(-x*x/2)*(1+e).
Proof.
  intros X. destruct q_one_ok as [One Value].
  assert (Square : 0<=x*x/2<=bpow radix2 (-801)).
  { apply Rabs_le_inv in X. pose proof(bpow_gt_0 radix2 (-400)).
    replace (bpow radix2 (-801)) with(bpow radix2 (-400)*bpow radix2 (-400)/2).
    - split;nra.
    - unfold Rdiv;change(/2)with(bpow radix2 (-1));rewrite <- !bpow_plus;reflexivity. }
  assert (Error : Rabs(exp(x*x/2)-1)<=bpow radix2 (-799)).
  { apply Rabs_le;split;interval with(i_prec 1000). }
  split;[exact One|]. exists(exp(x*x/2)-1). split;[exact Error|].
  rewrite Value. replace(1+(exp(x*x/2)-1))with(exp(x*x/2))by ring.
  rewrite <- exp_plus. replace(-x*x/2+x*x/2)with 0 by field.
  rewrite exp_0;reflexivity.
Qed.
