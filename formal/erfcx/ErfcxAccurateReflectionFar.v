(** The far-negative Q256 subtraction against the finite Gaussian definition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64 IEEE64Add.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxGaussianReflection
  ErfcxGaussianFar ErfcxTailIntegral ErfcxScaledAnalytic ErfcxAccurateProduct
  ErfcxAccurateExponential ErfcxReflectionSquare.
Open Scope R_scope.
Lemma positive_erfcx_large_bound x : 16<=x -> 0<=positive_erfcx x<=/16.
Proof.
  intros X. unfold positive_erfcx.
  destruct(tail_integral_limit ((/x)*(/x)) ltac:(nra)) as [_ T].
  assert (C : 0<=inv_sqrt_pi<=1) by (unfold inv_sqrt_pi;split;interval with(i_prec 80)).
  assert (I : 0<=/x<=/16).
  { split;[apply Rlt_le,Rinv_0_lt_compat;lra|apply Rinv_le_contravar;lra]. }
  assert (P : 0<=inv_sqrt_pi * /x<=/16) by nra.
  unfold Rdiv; nra.
Qed.
Lemma q_asym_large_magnitude x : finite x -> 16<=B x ->
  valid(q_asym x) /\ Rabs(qval(q_asym x))<=1.
Proof.
  intros Fx X. destruct(q_asym_error x Fx X) as [Q [e [E Value]]].
  pose proof(positive_erfcx_large_bound (B x) X) as F.
  split;[exact Q|]. rewrite Value,Rabs_mult,(Rabs_pos_eq(positive_erfcx(B x))) by lra.
  assert (Rabs(1+e)<=2) by (apply Rabs_le_inv in E;bpow_num_all;apply Rabs_le;lra).
  pose proof(Rabs_pos(1+e)); nra.
Qed.
Lemma far_reflected_subtraction_budget E G b g v :
  bpow radix2 360<=E -> Rabs G<=E*bpow radix2 (-350) ->
  Rabs(b-2*E)<=bpow radix2 (-237)*E -> Rabs g<=1 ->
  Rabs(v-(b-g))<=bpow radix2 (-254)*Rmax(Rabs b)(Rabs g) ->
  Rabs(v-(2*E-G))<=bpow radix2 (-236)*(2*E-G).
Proof.
  intros Ep Gbound Berr Gmag Verr.
  assert (Epos : 1<=E) by (bpow_num_all;lra).
  assert (Target : E<=2*E-G) by (apply Rabs_le_inv in Gbound;bpow_num_all;nra).
  assert (Bmag : Rabs b<=3*E).
  { replace b with ((b-2*E)+2*E) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite (Rabs_pos_eq (2*E)) by lra.
    bpow_num_all;nra. }
  assert (Max : Rmax(Rabs b)(Rabs g)<=4*E) by (apply Rmax_lub;lra).
  assert (Round : Rabs(v-(b-g))<=bpow radix2 (-252)*E).
  { eapply Rle_trans;[exact Verr|]. eapply Rle_trans.
    - apply Rmult_le_compat_l;[apply bpow_ge_0|exact Max].
    - bpow_num;lra. }
  assert (Small : Rabs(g-G)<=bpow radix2 (-349)*E).
  { eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp. bpow_num_all;lra. }
  replace (v-(2*E-G)) with ((v-(b-g))+(b-2*E)-(g-G)) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
  eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|]. bpow_num_all;nra.
Qed.
Definition q_reflection_asym x := add(q_reflection_big x)(neg_q(q_asym(fneg x))).
Theorem q_reflection_asym_error x : finite x ->
  B reflection_limit<B x<= -16 ->
  valid(q_reflection_asym x) /\
  Rabs(qval(q_reflection_asym x)-gaussian_erfcx(B x))<=
    bpow radix2 (-236)*gaussian_erfcx(B x).
Proof.
  intros Fx X.
  assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
  assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
  destruct(q_reflection_big_error x Fx ltac:(lra)) as [Big [e [E BigValue]]].
  destruct(q_asym_large_magnitude (fneg x) Fn ltac:(rewrite Bn;lra)) as [Small SmallMag].
  destruct(neg_any _ Small) as [Neg NegValue].
  destruct(add_any _ _ Big Neg) as [Result Error].
  split;[exact Result|]. unfold q_reflection_asym.
  rewrite NegValue,Rabs_Ropp in Error.
  assert (Identity : gaussian_erfcx(B x)=2*exp(B x*B x)-gaussian_erfcx(-B x)).
  { rewrite gaussian_erfcx_reflection;ring. }
  rewrite Identity.
  eapply far_reflected_subtraction_budget with (b:=qval(q_reflection_big x)) (g:=qval(q_asym(fneg x))).
  - assert (Lower : bpow radix2 360<=exp 256) by (bpow_num;interval with(i_prec 400)).
    eapply Rle_trans;[exact Lower|].
    destruct(Rle_lt_or_eq_dec 256 (B x*B x) ltac:(nra)) as [Lt|Eq].
    + apply Rlt_le,exp_increasing;exact Lt.
    + rewrite Eq;lra.
  - pose proof reflection_limit_value as Limit.
    pose proof(gaussian_far_bound (-B x) ltac:(lra)) as Bound.
    replace (-B x * -B x) with (B x*B x) in Bound by ring;exact Bound.
  - rewrite BigValue. replace (2*exp(B x*B x)*(1+e)-2*exp(B x*B x)) with
      (2*exp(B x*B x)*e) by ring.
    rewrite Rabs_mult,(Rabs_pos_eq (2*exp(B x*B x))) by (pose proof(exp_pos(B x*B x));lra).
    pose proof(exp_pos(B x*B x)). bpow_num_all;nra.
  - exact SmallMag.
  - exact Error.
Qed.
