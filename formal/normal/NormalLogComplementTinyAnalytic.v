(** Second-order log-complement approximation in the tiny-tail branch. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa NormalComplementAnalytic.
Open Scope R_scope.

Theorem normal_log_complement_tiny_analytic h l :
  0<h<=bpow radix2 (-54) -> Rabs l<=h*bpow radix2 (-51) ->
  Rabs(ln(1-h-l)-(-h-l-h*h/2))<=h*bpow radix2 (-100).
Proof.
  intros H L.
  assert(Q : 0<h+l<=2*h).
  { apply Rabs_le_inv in L;bpow_num_all;split;nra. }
  assert(Lrange : -bpow radix2 (-54)<=l<=bpow radix2 (-54)).
  { apply Rabs_le_inv in L;bpow_num_all;split;nra. }
  pose proof(normal_complement_remainder 2 (h+l)ltac:(bpow_num_all;split;lra))as Error.
  replace(normal_complement_series 2 (h+l))with((h+l)+(h+l)*(h+l)/2)in Error by(cbn;field).
  assert(Remainder : (h+l)^(2+1)/(1-(h+l))<=h*bpow radix2 (-104)).
  { assert(Inv : 0<=/(1-(h+l))<=2)by(split;interval with(i_prec 80)).
    assert(Cube : 0<=(h+l)^3<=8*h*h*h).
    { split;[apply pow_le;lra|].
      replace(8*h*h*h)with((2*h)^3)by ring;apply pow_incr;split;lra. }
    assert(Square : h*h<=h*bpow radix2 (-54))by(bpow_num_all;nra).
    assert(Third : h*h*h<=h*bpow radix2 (-108)).
    { assert(h*h*h<=h*h*bpow radix2 (-54))by nra;bpow_num_all;nra. }
    change((h+l)^3/(1-(h+l))<=h*bpow radix2 (-104));unfold Rdiv;bpow_num_all;nra. }
  assert(Correction : Rabs(((h+l)*(h+l)-h*h)/2)<=h*bpow radix2 (-103)).
  { replace(((h+l)*(h+l)-h*h)/2)with(h*l+l*l/2)by field.
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite Rabs_mult,(Rabs_pos_eq h)by lra.
    replace(l*l/2)with(l*l*(/2))by field;rewrite !Rabs_mult,Rabs_Rinv,(Rabs_pos_eq 2)by lra.
    pose proof(Rabs_pos l);bpow_num_all;nra. }
  replace(ln(1-h-l)-(-h-l-h*h/2))with
    (-(-ln(1-(h+l))-((h+l)+(h+l)*(h+l)/2))-(((h+l)*(h+l)-h*h)/2))by
    (replace(1-h-l)with(1-(h+l))by ring;field).
  eapply Rle_trans;[apply Rabs_triang|];rewrite !Rabs_Ropp;bpow_num_all;lra.
Qed.
