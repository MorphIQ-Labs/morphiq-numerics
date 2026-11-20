(** Accurate sine/cosine: finite binary64 conversion and the final ULP bound.
    The rounded value's binade may differ from the exact result's. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 RelativeUlp.
From Interval Require Import Tactic.
Require Import TrigQuadrant ErfcxAccurateInputs.
Open Scope R_scope.

Definition trig_accurate_result bits negative cosine :=
  Q256.to_f64 (trig_accurate64 bits negative cosine).

Lemma trig_accurate_round q v : valid q -> Rabs v<=1 ->
  Rabs(qval q-v)<=bpow radix2 (-198)*Rabs v ->
  finite (Q256.to_f64 q) /\ B(Q256.to_f64 q)=rndF(qval q).
Proof.
  intros V Mag Error. apply q_to_float_round; [exact V|].
  assert (Small:0<=bpow radix2 (-198)<1) by (split; [apply bpow_ge_0|change 1 with (bpow radix2 0); apply bpow_lt; lia]).
  assert (Bound:Rabs(qval q)<=2).
  { pose proof (Rabs_triang (qval q-v) v) as T.
    replace (qval q-v+v) with (qval q) in T by ring.
    pose proof (Rabs_pos v); nra. }
  apply Rle_lt_trans with 2.
  - apply abs_round_le_generic; [exact _|exact _| |exact Bound].
    change 2 with (bpow radix2 1). apply generic_format_bpow. unfold FLT_exp,emin,prec; lia.
  - change 2 with (bpow radix2 1). apply bpow_lt; lia.
Qed.

Theorem trig_accurate_ulp x negative cosine : finite x -> 0<=B x ->
  let y:=trig_accurate_result (bits_of_b64 x) negative cosine in
  let v:=if cosine then cos(if negative then -B x else B x)
                    else sin(if negative then -B x else B x) in
  finite y /\ Rabs(B y-v)<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros F X. cbv zeta.
  pose proof (trig_accurate_value_correct x negative cosine F X) as Value. cbv zeta in Value.
  set (q:=trig_accurate64 (bits_of_b64 x) negative cosine) in *.
  set (v:=if cosine then cos(if negative then -B x else B x)
                    else sin(if negative then -B x else B x)) in *.
  destruct Value as [V Err].
  assert (Mag:Rabs v<=1) by (unfold v; destruct cosine; apply Rabs_le; [apply COS_bound|apply SIN_bound]).
  destruct (trig_accurate_round q v V Mag Err) as [Fy By].
  unfold trig_accurate_result. fold q. split; [exact Fy|]. rewrite By.
  pose proof (relative_ulp_error (bpow radix2 (-198)) v (qval q)
    ltac:(split; [apply bpow_ge_0|apply bpow_lt; lia]) Err) as Bound.
  rewrite <-bpow_plus in Bound. exact Bound.
Qed.
