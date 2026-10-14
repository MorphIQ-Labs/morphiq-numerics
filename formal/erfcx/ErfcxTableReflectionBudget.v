(** The table bounds needed by reflected subtraction, from the exact
    polynomial range, the composed errors, and final normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add.
Require Import StageGappa ErfcxRounding ErfcxTableFast.
Open Scope R_scope.
Lemma table_reflection_budget p f y h l : 0.034<=p<=0.616 -> 0<f ->
  Rabs((p-f)/f)<=bpow radix2 (-69) ->
  Rabs((y-p)/p)<=/2^67 -> y=h+l -> h=rndF y ->
  0<=f<=1 /\ /32<=h<=0.617 /\ Rabs l<=bpow radix2 (-53) /\
  Rabs(y-f)<=bpow radix2 (-67).
Proof.
  intros P F Approx Eval Sum Norm.
  assert (Fp : 0.033<=f<=0.617).
  { pose proof(Rabs_le_inv _ _ Approx) as Bound.
    assert (Identity : p=f*(1+(p-f)/f)) by (field;lra).
    set(a:=(p-f)/f) in *. bpow_num_all;split;nra. }
  assert (Y : 0.0339<=y<=0.6161).
  { pose proof(Rabs_le_inv _ _ Eval) as Bound.
    assert (Identity : y=p*(1+(y-p)/p)) by (field;lra).
    set(e:=(y-p)/p) in *. bpow_num_all;split;nra. }
  destruct(rounding_decomposition y) as [d [a [D [A Round]]]].
  rewrite <- Norm in Round.
  assert (H : /32<=h<=0.617) by (bpow_num_all;split;nra).
  assert (L : Rabs l<=bpow radix2 (-53)).
  { apply Rabs_le. bpow_num_all;split;nra. }
  pose proof(table_composed_error y p f F Approx Eval) as Error.
  rewrite (Rabs_pos_eq f) in Error by lra. rewrite Rabs_minus_sym in Error.
  split;[lra|]. split;[exact H|]. split;[exact L|]. bpow_num_all;nra.
Qed.
