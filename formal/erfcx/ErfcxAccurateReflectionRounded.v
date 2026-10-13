(** The accurate reflected result remains finite and has a composed binary64
    error bound; this does not assert correct rounding of the fallback. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxRounding ErfcxAccurateInputs
  ErfcxAccurateReflectionEntry ErfcxAccurateReflectionRange ErfcxReflectionSquare.
Open Scope R_scope.
Lemma accurate_reflection_round_range F v d a :
  1<=F<=bpow radix2 1024*(1-bpow radix2 (-46)) ->
  Rabs(v-F)<=bpow radix2 (-123)*F ->
  -bpow radix2 (-53)<=d<=bpow radix2 (-53) ->
  -bpow radix2 (-1075)<=a<=bpow radix2 (-1075) ->
  Rabs(v*(1+d)+a)<bpow radix2 1024.
Proof.
  intros Fr Error D A. apply Rabs_le_inv in Error.
  assert (V : /2<=v<=bpow radix2 1024*(1-bpow radix2 (-47))) by (bpow_num_all;nra).
  assert (P : /4<=v*(1+d)<=bpow radix2 1024*(1-bpow radix2 (-48))).
  { assert (Factor : /2<=1+d<=1+bpow radix2 (-53)) by (bpow_num_all;lra).
    assert (Upper : v*(1+d)<=bpow radix2 1024*(1-bpow radix2 (-47))*(1+bpow radix2 (-53))).
    { apply Rmult_le_compat;[lra|lra|apply V|apply Factor]. }
    bpow_num_all;split;nra. }
  apply Rabs_lt. bpow_num_all;split;lra.
Qed.
Lemma accurate_reflection_relative_round e d : Rabs e<=bpow radix2 (-123) ->
  -bpow radix2 (-53)<=d<=bpow radix2 (-53) ->
  Rabs(e+d+e*d)<=bpow radix2 (-53)+bpow radix2 (-122).
Proof.
  intros E D. apply Rabs_le_inv in E.
  replace (e+d+e*d) with (d+e*(1+d)) by ring.
  bpow_num_all;interval with(i_prec 200).
Qed.
Theorem q_negative_rounded x : finite x -> B reflection_limit<B x< -/2 ->
  finite(Q256.to_f64(q_negative x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-122) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(q_negative x))=gaussian_erfcx(B x)*(1+d)+a.
Proof.
  intros Fx X. destruct(q_negative_error x Fx X) as [Q Error].
  pose proof(accurate_reflection_target_range x Fx X) as F.
  destruct(rounding_decomposition(qval(q_negative x))) as [d [a [D [A Round]]]].
  assert (Range : Rabs(rndF(qval(q_negative x)))<bpow radix2 1024).
  { rewrite Round;apply accurate_reflection_round_range with (F:=gaussian_erfcx(B x));assumption. }
  destruct(q_to_float_round _ Q Range) as [Finite Rounded].
  set (e:=(qval(q_negative x)-gaussian_erfcx(B x))/gaussian_erfcx(B x)).
  assert (E : Rabs e<=bpow radix2 (-123)).
  { unfold e,Rdiv. rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx(B x))) by lra.
    apply (Rmult_le_reg_r (gaussian_erfcx(B x)));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Error. }
  assert (Value : qval(q_negative x)=gaussian_erfcx(B x)*(1+e)) by (unfold e;field;lra).
  split;[exact Finite|]. exists (e+d+e*d),a.
  split;[apply accurate_reflection_relative_round;assumption|].
  split;[apply Rabs_le;exact A|]. rewrite Rounded,Round,Value;ring.
Qed.
