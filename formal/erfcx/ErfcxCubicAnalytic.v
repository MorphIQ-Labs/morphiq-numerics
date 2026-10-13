(** The actual cubic-tail remainder and its accepted IEEE result. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa Expm1Series ErfcxTailIntegral ErfcxAsymptotic.
Require Import ErfcxTailCorrection ErfcxTailFast ErfcxScaledAnalytic.
Open Scope R_scope.

Lemma asym_cubic_polynomial t : asym_polynomial 3 t=1+tail_polynomial t.
Proof.
  unfold asym_polynomial, asym_coefficient, tail_polynomial.
  cbn [sum_f_R0]. factorial_reals. small_numerals. simpl pow. field.
Qed.
Lemma asym_cubic_next t : asym_next_coefficient 3 t*INR(fact(2*S 3))=(105/16)*t^4.
Proof.
  unfold asym_next_coefficient. factorial_reals. small_numerals. simpl pow. field.
Qed.

Theorem tail_cubic_remainder t : 0<=t ->
  0<=tail_integral t-(1+tail_polynomial t)<=(105/16)*t^4.
Proof.
  intros T. pose proof (tail_integral_asymptotic 3 t T) as R.
  replace ((-1)^S 3) with 1 in R by (simpl pow; ring).
  rewrite Rmult_1_l, asym_cubic_polynomial, asym_cubic_next in R. exact R.
Qed.

Lemma tail_cubic_analytic_bound x : 512<=x ->
  0<=tail_integral ((1/x)*(1/x))-(1+tail_polynomial ((1/x)*(1/x)))<=7/2^72.
Proof.
  intros X.
  assert (Y : 0<=1/x<=/512).
  { unfold Rdiv. rewrite Rmult_1_l. split; [apply Rlt_le,Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
  set (t := (1/x)*(1/x)).
  assert (T : 0<=t<=/262144) by (unfold t; nra).
  destruct (tail_cubic_remainder t (proj1 T)) as [Low High].
  assert (Square : 0<=t*t<=/68719476736) by nra.
  assert (Fourth : t^4<=/4722366482869645213696).
  { replace (t^4) with ((t*t)*(t*t)) by (simpl pow; ring). nra. }
  split; [exact Low | ]. replace (7/2^72) with (7/4722366482869645213696) by (simpl; field). nra.
Qed.

Theorem tail_unscaled_fast_analytic_ieee x v : finite x -> 512<=B x<=bpow radix2 897 ->
  tail_unscaled_fast64 x=Some v -> finite v /\ B v=rndF (positive_erfcx (B x)).
Proof.
  intros Fx X Decision.
  pose proof (tail_cubic_analytic_bound (B x) (proj1 X)) as Bound.
  destruct (tail_unscaled_fast_ieee x
    (tail_integral ((1/B x)*(1/B x))-(1+tail_polynomial ((1/B x)*(1/B x)))) v Fx X Bound Decision)
    as [Fv V].
  replace (1+tail_polynomial ((1/B x)*(1/B x))+
    (tail_integral ((1/B x)*(1/B x))-(1+tail_polynomial ((1/B x)*(1/B x)))))
    with (tail_integral ((1/B x)*(1/B x))) in V by ring.
  split; [exact Fv | ]. unfold positive_erfcx.
  replace (1/B x) with (/B x) in V by (unfold Rdiv; ring). exact V.
Qed.
