(** Error propagation through the actual Q256 reflected subtraction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Eft IEEE64Add.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxGaussianReflection
  ErfcxAccurateExponential ErfcxAccurateTaylorEntry ErfcxReflectionSquare.
Open Scope R_scope.
Lemma reflected_subtraction_budget E G b g v :
  1<=E -> E<=2*E-G -> Rabs G<=512 ->
  Rabs(b-2*E)<=bpow radix2 (-237)*E ->
  Rabs(g-G)<=bpow radix2 (-124) ->
  Rabs(v-(b-g))<=bpow radix2 (-254)*Rmax(Rabs b)(Rabs g) ->
  Rabs(v-(2*E-G))<=bpow radix2 (-123)*(2*E-G).
Proof.
  intros Ep F Gbound Berr Gerr Verr.
  assert (Bmag : Rabs b<=3*E).
  { replace b with ((b-2*E)+2*E) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite (Rabs_pos_eq (2*E)) by lra.
    bpow_num_all;nra. }
  assert (Gmag : Rabs g<=513).
  { replace g with ((g-G)+G) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra. }
  assert (Max : Rmax(Rabs b)(Rabs g)<=1024*(2*E-G)).
  { apply Rmax_lub; nra. }
  assert (Round : Rabs(v-(b-g))<=bpow radix2 (-244)*(2*E-G)).
  { eapply Rle_trans;[exact Verr|]. eapply Rle_trans.
    - apply Rmult_le_compat_l;[apply bpow_ge_0|exact Max].
    - bpow_num;nra. }
  replace (v-(2*E-G)) with ((v-(b-g))+(b-2*E)-(g-G)) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
  eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|]. bpow_num_all;nra.
Qed.
Definition q_reflection_taylor x := add (q_reflection_big x) (neg_q(q_taylor(fneg x))).
Theorem q_reflection_taylor_error x : finite x ->
  B reflection_limit<B x< -/2 -> -16<B x ->
  valid(q_reflection_taylor x) /\
  Rabs(qval(q_reflection_taylor x)-gaussian_erfcx(B x))<=
    bpow radix2 (-123)*gaussian_erfcx(B x).
Proof.
  intros Fx X T.
  assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
  assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
  destruct(q_reflection_big_error x Fx X) as [Big [e [E BigValue]]].
  destruct(q_taylor_error (fneg x) Fn ltac:(rewrite Bn;lra)) as [Small SmallError].
  pose proof(table_target_bound (fneg x) Fn ltac:(rewrite Bn;lra)) as Target.
  rewrite Bn in SmallError,Target.
  destruct(neg_any _ Small) as [Neg NegValue].
  destruct(add_any _ _ Big Neg) as [Result Error].
  split;[exact Result|]. unfold q_reflection_taylor.
  rewrite NegValue,Rabs_Ropp in Error.
  assert (Identity : gaussian_erfcx(B x)=2*exp(B x*B x)-gaussian_erfcx(-B x)).
  { rewrite gaussian_erfcx_reflection;ring. }
  rewrite Identity.
  eapply reflected_subtraction_budget with (b:=qval(q_reflection_big x)) (g:=qval(q_taylor(fneg x))).
  - destruct(Req_dec (B x) 0) as [Zero|Nonzero];[lra|].
    rewrite <- exp_0. apply Rlt_le,exp_increasing;nra.
  - rewrite <- Identity;apply gaussian_negative_lower;lra.
  - exact Target.
  - rewrite BigValue. replace (2*exp(B x*B x)*(1+e)-2*exp(B x*B x)) with
      (2*exp(B x*B x)*e) by ring.
    rewrite Rabs_mult,(Rabs_pos_eq (2*exp(B x*B x))) by (pose proof(exp_pos(B x*B x));lra).
    pose proof(exp_pos(B x*B x)). bpow_num_all;nra.
  - exact SmallError.
  - exact Error.
Qed.
