(** Final conversion of a bounded Q256 result, including gradual
    underflow. This is a quantitative bound, not a correct-rounding claim. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxRounding ErfcxAccurateInputs.
Open Scope R_scope.

Theorem normal_q_bounded_rounded q f epsilon : valid q ->
  Rabs f<=1 -> 0<=epsilon<=/4 ->
  (exists e,Rabs e<=epsilon /\ qval q=f*(1+e)) ->
  finite(Q256.to_f64 q) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+2*epsilon /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64 q)=f*(1+d)+a.
Proof.
  intros Q F Epsilon [e [E Value]].
  apply Rabs_le_inv in F.
  destruct(rounding_decomposition(qval q)) as [d [a [D [A Round]]]].
  pose proof(Rabs_le_inv _ _ E) as Eb.
  assert (Range : -2<=qval q<=2) by (rewrite Value;split;nra).
  assert (RoundedRange : Rabs(rndF(qval q))<=4).
  { rewrite Round. apply Rabs_le. bpow_num_all. split;nra. }
  assert (Finite : Rabs(rndF(qval q))<bpow radix2 1024).
  { eapply Rle_lt_trans;[exact RoundedRange|].
    change 4 with(bpow radix2 2). apply bpow_lt;lia. }
  destruct(q_to_float_round _ Q Finite) as [Result Rounded].
  split;[exact Result|]. exists((1+e)*(1+d)-1),a. split.
  - assert (Dabs : Rabs d<=bpow radix2 (-53)) by (apply Rabs_le;exact D).
    replace ((1+e)*(1+d)-1) with(d+e*(1+d)) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult.
    assert (Factor : Rabs(1+d)<=2).
    { apply Rabs_le. bpow_num_all. split;lra. }
    assert (Product : Rabs e*Rabs(1+d)<=epsilon*2).
    { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact E|exact Factor]. }
    lra.
  - split;[apply Rabs_le;exact A|]. rewrite Rounded,Round,Value;ring.
Qed.

Corollary normal_q_positive_rounded q f epsilon : valid q ->
  0<=f<=1 -> 0<=epsilon<=/4 ->
  (exists e,Rabs e<=epsilon /\ qval q=f*(1+e)) ->
  finite(Q256.to_f64 q) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+2*epsilon /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64 q)=f*(1+d)+a.
Proof.
  intros Q F E Error. apply normal_q_bounded_rounded;try assumption.
  rewrite Rabs_pos_eq;lra.
Qed.
