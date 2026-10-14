(** Form the accurate tail's t=(1/x)^2/2 from its Q256 reciprocal. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTerms.
Open Scope R_scope.

Definition q_half := from_f64 4602678819172646912.
Definition q_half_square y := mul (mul y y) q_half.

Lemma q_half_ok : valid q_half /\ qval q_half=/2.
Proof.
  split; [apply from_f64_valid | ].
  assert (Half : q_half=mul_pow2 q_one (-1)) by (vm_compute; reflexivity).
  rewrite Half. destruct q_one_ok as [Q V].
  rewrite (proj2 (mul_pow2_any q_one (-1) Q)),V.
  change (bpow radix2 (-1)) with (/2). ring.
Qed.

Lemma half_square_factor e a b :
  Rabs e<=bpow radix2 (-252) -> Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs ((1+e)*(1+e)*(1+a)*(1+b)-1)<=bpow radix2 (-249).
Proof.
  intros E A B. apply Rabs_le_inv in E,A,B.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Theorem q_half_square_error y exact_y : valid y ->
  (exists e, Rabs e<=bpow radix2 (-252) /\ qval y=exact_y*(1+e)) ->
  valid (q_half_square y) /\ exists d,
    Rabs d<=bpow radix2 (-249) /\ qval (q_half_square y)=((exact_y*exact_y)/2)*(1+d).
Proof.
  intros Y [e [E Value]]. destruct q_half_ok as [H Half].
  destruct (mul_relative y y Y Y) as [Q1 [a [A V1]]].
  destruct (mul_relative _ q_half Q1 H) as [Q2 [b [B V2]]].
  split; [exact Q2 | ]. exists ((1+e)*(1+e)*(1+a)*(1+b)-1). split.
  - apply half_square_factor; assumption.
  - unfold q_half_square. rewrite V2,V1,Value,Half. field.
Qed.
