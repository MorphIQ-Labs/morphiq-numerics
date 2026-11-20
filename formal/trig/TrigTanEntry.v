(** Complete scalar tangent entry: finite guard, identity screen, checked
    quotient decision, and accurate fallback. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest RelativeUlp.
Require Import TrigInputContract TrigEntry TrigTanScreenConstants TrigTanScreen
 TrigTanFastValue TrigTanAccurate TrigTanRounding.
Open Scope R_scope.

Definition trig_tan_identity x :=
 match Bcompare 53 1024 (b64_abs x) trig_tan_is_x with
 | Some Eq | Some Lt => true | _ => false end.
Definition trig_tan_decision bits negative :=
 match trig_tan_fast64 bits negative with
 | Some(h,l) => decide_with h l trig_tan_eps
 | None => None end.
Definition trig_tan_finish bits negative :=
 match trig_tan_decision bits negative with
 | Some y => y
 | None => trig_tan_accurate_result bits negative end.
Definition trig_tan_public_finish x :=
 trig_tan_finish (bits_of_b64(b64_abs x)) (trig_negative x).
Definition trig_tan_entry x :=
 if is_finite 53 1024 x then
  if trig_tan_identity x then x else trig_tan_public_finish x
 else trig_nan.

Lemma trig_tan_identity_correct x : finite x ->
 (trig_tan_identity x=true <-> Rabs(B x)<=B trig_tan_is_x) /\
 (trig_tan_identity x=false <-> B trig_tan_is_x<Rabs(B x)).
Proof.
 intro F;unfold trig_tan_identity.
 rewrite (Bcompare_correct 53 1024 _ _ (trig_abs_finite x F) trig_tan_is_x_finite),B_abs.
 destruct (Rcompare_spec (Rabs(B x)) (B trig_tan_is_x));split;split;intros;try reflexivity;try discriminate;lra.
Qed.

Lemma trig_tan_decision_correct x negative y : finite x -> bpow radix2 (-63)<=B x ->
 trig_tan_decision (bits_of_b64 x) negative=Some y ->
 finite y /\ B y=rndF(tan(if negative then -B x else B x)).
Proof.
 intros F X;unfold trig_tan_decision.
 destruct (trig_tan_fast64 (bits_of_b64 x) negative) as [[h l]|] eqn:Fast;[|discriminate].
 apply trig_tan_fast_decision_correct;assumption.
Qed.

Lemma trig_tan_round_error v :
 Rabs(rndF v-v)<=(/2+bpow radix2 (-143))*ulp radix2 (FLT_exp emin prec) v.
Proof.
 pose proof (relative_ulp_error 0 v v ltac:(split;[lra|apply bpow_gt_0])
  ltac:(rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;lra)) as Error.
 apply Rle_trans with (1:=Error).
 apply Rmult_le_compat_r;[apply ulp_ge_0|]. pose proof (bpow_ge_0 radix2 (-143));nra.
Qed.

Theorem trig_tan_finish_ulp x negative : finite x -> bpow radix2 (-63)<=B x ->
 let y:=trig_tan_finish (bits_of_b64 x) negative in
 let v:=tan(if negative then -B x else B x) in
 finite y /\ Rabs(B y-v)<=(/2+bpow radix2 (-143))*ulp radix2 (FLT_exp emin prec) v.
Proof.
 intros F X;cbv zeta;unfold trig_tan_finish.
 destruct (trig_tan_decision (bits_of_b64 x) negative) as [y|] eqn:Decision.
 - destruct (trig_tan_decision_correct x negative y F X Decision) as [Y Value].
   split;[exact Y|];rewrite Value;apply trig_tan_round_error.
 - apply trig_tan_accurate_ulp;[exact F|pose proof (bpow_gt_0 radix2 (-63));lra].
Qed.

Theorem trig_tan_public_finish_ulp x : finite x -> bpow radix2 (-63)<=Rabs(B x) ->
 finite(trig_tan_public_finish x) /\
 Rabs(B(trig_tan_public_finish x)-tan(B x))<=
 (/2+bpow radix2 (-143))*ulp radix2 (FLT_exp emin prec) (tan(B x)).
Proof.
 intros F X.
 pose proof (trig_tan_finish_ulp (b64_abs x) (trig_negative x)
  (trig_abs_finite x F) ltac:(rewrite B_abs;exact X)) as Result.
 cbv zeta in Result;rewrite (trig_public_argument x F) in Result;exact Result.
Qed.

Theorem trig_tan_entry_ulp x : finite x ->
 finite(trig_tan_entry x) /\
 Rabs(B(trig_tan_entry x)-tan(B x))<=
 (/2+bpow radix2 (-143))*ulp radix2 (FLT_exp emin prec) (tan(B x)).
Proof.
 intro F;unfold trig_tan_entry;rewrite F.
 destruct (trig_tan_identity x) eqn:Screen.
 - apply (proj1 (trig_tan_identity_correct x F)) in Screen.
   split;[exact F|].
   pose proof (trig_tan_screen_round (B x) (B_fmt x) Screen) as Round.
   rewrite <-Round at 1;apply trig_tan_round_error.
 - apply (proj2 (trig_tan_identity_correct x F)) in Screen.
   apply (trig_tan_public_finish_ulp x F).
   pose proof trig_tan_is_x_bounds as Cutoff.
   assert (bpow radix2 (-63)<=bpow radix2 (-27)) by (apply bpow_le;lia);lra.
Qed.

Theorem trig_tan_entry_nonfinite x : is_finite 53 1024 x=false ->
 trig_tan_entry x=trig_nan /\ is_nan 53 1024 trig_nan=true.
Proof. intro F;unfold trig_tan_entry;rewrite F;split;reflexivity. Qed.
Theorem trig_tan_entry_zeros :
 bits_of_b64(trig_tan_entry(b64_of_bits 0))=0%Z /\
 bits_of_b64(trig_tan_entry(b64_of_bits 9223372036854775808))=9223372036854775808%Z.
Proof. vm_compute;split;reflexivity. Qed.

Theorem trig_tan_entry_decided x y : finite x -> trig_tan_identity x=false ->
 trig_tan_decision (bits_of_b64(b64_abs x)) (trig_negative x)=Some y ->
 trig_tan_entry x=y /\ finite y /\ B y=rndF(tan(B x)).
Proof.
 intros F Screen Decision.
 split;[unfold trig_tan_entry,trig_tan_public_finish,trig_tan_finish;rewrite F,Screen,Decision;reflexivity|].
 assert (Floor:bpow radix2 (-63)<=B(b64_abs x)).
 { apply (proj2 (trig_tan_identity_correct x F)) in Screen.
   rewrite B_abs;pose proof trig_tan_is_x_bounds as Cutoff.
   assert (bpow radix2 (-63)<=bpow radix2 (-27)) by (apply bpow_le;lia);lra. }
 pose proof (trig_tan_decision_correct (b64_abs x) (trig_negative x) y
  (trig_abs_finite x F) Floor Decision) as Result.
 rewrite (trig_public_argument x F) in Result;exact Result.
Qed.
