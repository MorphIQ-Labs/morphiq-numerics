(** Both positive corrections in the accurate negative dispatch. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add Encodings.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxGaussianReflection ErfcxAccurateTaylorEntry
  ErfcxAccurateProduct ErfcxAccurateExponential ErfcxAccurateReflection
  ErfcxAccurateReflectionFar ErfcxReflectionSquare.
Open Scope R_scope.
Definition reflection_sixteen : f64 := b64_of_bits 4625196817309499392.
Lemma reflection_sixteen_ok : finite reflection_sixteen /\ B reflection_sixteen=16.
Proof.
  split;[exact(bits_finite 4625196817309499392 false 4503599627370496 (-48) eq_refl)|].
  change (4503599627370496*bpow radix2 (-48)=16). bpow_num;field.
Qed.
Definition q_negative x :=
  let g := match Bcompare 53 1024 (fneg x) reflection_sixteen with
    | Some Lt => q_taylor(fneg x)
    | _ => q_asym(fneg x)
    end in
  add(q_reflection_big x)(neg_q g).
Local Opaque Q256.add neg_q q_reflection_big q_taylor q_asym.
Theorem q_negative_error x : finite x -> B reflection_limit<B x< -/2 ->
  valid(q_negative x) /\ Rabs(qval(q_negative x)-gaussian_erfcx(B x))<=
    bpow radix2 (-123)*gaussian_erfcx(B x).
Proof.
  intros Fx X.
  assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
  assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
  destruct reflection_sixteen_ok as [F16 B16].
  unfold q_negative. rewrite (Bcompare_correct 53 1024 (fneg x) reflection_sixteen Fn F16),Bn,B16.
  destruct(Rcompare_spec (-B x) 16) as [Lt|Eq|Gt].
  - fold(q_reflection_taylor x). exact(q_reflection_taylor_error x Fx X ltac:(lra)).
  - fold(q_reflection_asym x). destruct(q_reflection_asym_error x Fx ltac:(lra)) as [Q Error].
    split;[exact Q|]. eapply Rle_trans;[exact Error|].
    apply Rmult_le_compat_r;[pose proof(gaussian_negative_at_least_one (B x) ltac:(lra));lra|apply bpow_le;lia].
  - fold(q_reflection_asym x). destruct(q_reflection_asym_error x Fx ltac:(lra)) as [Q Error].
    split;[exact Q|]. eapply Rle_trans;[exact Error|].
    apply Rmult_le_compat_r;[pose proof(gaussian_negative_at_least_one (B x) ltac:(lra));lra|apply bpow_le;lia].
Qed.
