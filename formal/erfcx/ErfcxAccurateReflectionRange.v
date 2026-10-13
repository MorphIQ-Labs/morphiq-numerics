(** Binary64 discreteness leaves much more headroom than Q256 error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64 IEEE64Add Encodings.
Require Import StageGappa ErfcxGaussianTarget ErfcxGaussianReflection ErfcxGaussianFar
  ErfcxAccurateTaylorEntry ErfcxReflectionSquare ErfcxReflectionOverflow.
Open Scope R_scope.
Lemma accurate_reflection_boundary :
  2*exp((B reflection_limit+bpow radix2 (-48))^2)<=
    bpow radix2 1024*(1-bpow radix2 (-45)).
Proof.
  unfold reflection_limit.
  rewrite (bits_val 13851560577301767119 true 7495322764862415 48 eq_refl).
  bpow_num. simpl. interval with(i_prec 200).
Qed.
Theorem accurate_reflection_target_range x : finite x ->
  B reflection_limit<B x< -/2 ->
  1<=gaussian_erfcx(B x)<=bpow radix2 1024*(1-bpow radix2 (-46)).
Proof.
  intros Fx X. split;[apply gaussian_negative_at_least_one;lra|].
  assert (Identity : gaussian_erfcx(B x)=2*exp(B x*B x)-gaussian_erfcx(-B x))
    by (rewrite gaussian_erfcx_reflection;ring).
  destruct(Rlt_dec (-16) (B x)) as [Near|Far].
  - assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
    assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
    pose proof(table_target_bound (fneg x) Fn ltac:(rewrite Bn;lra)) as T.
    rewrite Bn in T. apply Rabs_le_inv in T.
    assert (E : exp(B x*B x)<=exp 256).
    { apply exp_le;nra. }
    rewrite Identity. eapply Rle_trans with (2*exp 256+512);[lra|].
    bpow_num;interval with(i_prec 200).
  - pose proof(reflection_next_input x Fx (proj1 X)) as Next.
    pose proof reflection_limit_value as Limit.
    pose proof(gaussian_far_bound (-B x) ltac:(lra)) as T.
    replace (-B x * -B x) with (B x*B x) in T by ring.
    apply Rabs_le_inv in T.
    assert (E : 2*exp(B x*B x)<=bpow radix2 1024*(1-bpow radix2 (-45))).
    { eapply Rle_trans;[|apply accurate_reflection_boundary].
      apply Rmult_le_compat_l;[lra|]. apply exp_le.
      change (bpow radix2 (-48)) with (/281474976710656) in *; nra. }
    rewrite Identity. bpow_num_all;nra.
Qed.
