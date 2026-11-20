(** Finite accurate tangent conversion and ULP error at the exact result. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 RelativeUlp.
Require Import TrigQuadrant TrigReduction TrigTanDomain TrigTanAccurate ErfcxAccurateInputs.
Open Scope R_scope.

Lemma trig_tan_magnitude x (negative:bool) : finite x -> 0<=B x ->
  Rabs(tan(if negative then -B x else B x))<=bpow radix2 63.
Proof.
  intros F X.
  destruct (trig_reduce_correct x F X) as [n [q [_ [_ [_ [Near _]]]]]].
  pose proof (trig_nearest_nonnegative (B x) n X Near) as N.
  pose proof (trig_tan_denominator_bound x n F X Near) as Lower.
  cbv zeta in Lower. set (t:=B x-IZR n*(PI/2)) in *.
  assert (Nonzero:trig_tan_den (n mod 4) (sin t) (cos t)<>0).
  { intro Zero. rewrite Zero,Rabs_R0 in Lower. pose proof (bpow_gt_0 radix2 (-63)); lra. }
  pose proof (trig_tan_analytic n t negative N Nonzero) as Value.
  replace (t+IZR n*(PI/2)) with (B x) in Value by (unfold t; ring).
  rewrite <-Value. unfold trig_tan_real.
  assert (Num:Rabs(trig_tan_num (n mod 4) (sin t) (cos t))<=1).
  { unfold trig_tan_num. destruct (Z.odd (n mod 4)); apply Rabs_le; [apply COS_bound|apply SIN_bound]. }
  assert (Inv:/Rabs(trig_tan_den (n mod 4) (sin t) (cos t))<=bpow radix2 63).
  { replace (bpow radix2 63) with (/bpow radix2 (-63)) by (rewrite <-bpow_opp; reflexivity).
    apply Rinv_le_contravar; [apply bpow_gt_0|exact (proj1 Lower)]. }
  assert (Bound:Rabs(trig_tan_num (n mod 4) (sin t) (cos t)/trig_tan_den (n mod 4) (sin t) (cos t))<=bpow radix2 63).
  { unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact Nonzero.
    apply Rle_trans with (1*bpow radix2 63); [|right; ring].
    apply Rmult_le_compat; try apply Rabs_pos; try exact Num; try exact Inv.
    left; apply Rinv_0_lt_compat,Rabs_pos_lt; exact Nonzero. }
  destruct (xorb (Z.odd (n mod 4)) negative); [rewrite Rabs_Ropp|]; exact Bound.
Qed.

Definition trig_tan_accurate_result bits negative :=
  Q256.to_f64(trig_tan_accurate64 bits negative).

Lemma trig_tan_round q v : valid q -> Rabs v<=bpow radix2 63 ->
  Rabs(qval q-v)<=bpow radix2 (-196)*Rabs v ->
  finite(Q256.to_f64 q) /\ B(Q256.to_f64 q)=rndF(qval q).
Proof.
  intros V Mag Error. apply q_to_float_round; [exact V|].
  assert (Small:0<=bpow radix2 (-196)<1) by
    (split; [apply bpow_ge_0|change 1 with (bpow radix2 0); apply bpow_lt; lia]).
  assert (Bound:Rabs(qval q)<=bpow radix2 64).
  { pose proof (Rabs_triang (qval q-v) v) as T.
    replace (qval q-v+v) with (qval q) in T by ring.
    assert (Scale:bpow radix2 64=2*bpow radix2 63).
    { change 2 with (bpow radix2 1). rewrite <-bpow_plus; reflexivity. }
    pose proof (Rabs_pos v). rewrite Scale; nra. }
  apply Rle_lt_trans with (bpow radix2 64).
  - apply abs_round_le_generic; [exact _|exact _| |exact Bound].
    apply generic_format_bpow. unfold FLT_exp,emin,prec; lia.
  - apply bpow_lt; lia.
Qed.

Theorem trig_tan_accurate_ulp x negative : finite x -> 0<=B x ->
  let y:=trig_tan_accurate_result (bits_of_b64 x) negative in
  let v:=tan(if negative then -B x else B x) in
  finite y /\ Rabs(B y-v)<=(/2+bpow radix2 (-143))*ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros F X. cbv zeta.
  pose proof (trig_tan_accurate_value_correct x negative F X) as Value. cbv zeta in Value.
  pose proof (trig_tan_magnitude x negative F X) as Mag.
  set (q:=trig_tan_accurate64 (bits_of_b64 x) negative) in *.
  set (v:=tan(if negative then -B x else B x)) in *.
  destruct Value as [V Err].
  destruct (trig_tan_round q v V Mag Err) as [Fy By].
  unfold trig_tan_accurate_result. fold q. split; [exact Fy|]. rewrite By.
  pose proof (relative_ulp_error (bpow radix2 (-196)) v (qval q)
    ltac:(split; [apply bpow_ge_0|apply bpow_lt; lia]) Err) as Bound.
  rewrite <-bpow_plus in Bound. exact Bound.
Qed.
