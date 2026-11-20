(** Public sine/cosine entry screens and finite-input composition. The
    negative flag is the runtime comparison x < 0, not the sign bit. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingTest RelativeUlp.
From Interval Require Import Tactic.
Require Import TrigScreenConstants TrigSinScreen TrigCosScreen TrigInputContract TrigFastDecision.
Open Scope R_scope.

Definition trig_nan := b64_of_bits 9221120237041090560.
Definition trig_cos_small_limit := b64_of_bits 4494592428115755008.
Lemma trig_cos_small_limit_finite : finite trig_cos_small_limit.
Proof. exact (bits_finite 4494592428115755008 _ _ _ eq_refl). Qed.
Lemma trig_cos_small_limit_value : B trig_cos_small_limit=bpow radix2 (-25).
Proof. unfold trig_cos_small_limit;rewrite (bits_val 4494592428115755008 false 4503599627370496 77 eq_refl). change (4503599627370496/2^77=/33554432);field. Qed.

Definition trig_sin_identity x :=
 match Bcompare 53 1024 (b64_abs x) trig_sin_is_x with
 | Some Eq | Some Lt => true | _ => false end.
Definition trig_cos_screen x :=
 match Bcompare 53 1024 (b64_abs x) trig_cos_small_limit with
 | Some Lt => true | _ => false end.
Definition trig_public_finish x cosine :=
 trig_finish (bits_of_b64(b64_abs x)) (trig_negative x) cosine.
Definition trig_sin_entry x :=
 if is_finite 53 1024 x then
  if trig_sin_identity x then x else trig_public_finish x false
 else trig_nan.
Definition trig_cos_entry x :=
 if is_finite 53 1024 x then
  if trig_cos_screen x then trig_cos_small (b64_abs x) else trig_public_finish x true
 else trig_nan.
Definition trig_sincos_entry x :=
 if negb(is_finite 53 1024 x) || trig_sin_identity x || trig_cos_screen x
 then (trig_sin_entry x,trig_cos_entry x)
 else (trig_public_finish x false,trig_public_finish x true).

Lemma trig_abs_finite x : finite x -> finite(b64_abs x).
Proof. intro F;unfold b64_abs;rewrite is_finite_Babs;exact F. Qed.
Lemma trig_public_argument x : finite x ->
 (if trig_negative x then -B(b64_abs x) else B(b64_abs x))=B x.
Proof.
 intro F;destruct (trig_negative_correct x F) as [Negative Nonnegative].
 destruct (trig_negative x) eqn:N;rewrite B_abs.
 - pose proof (proj1 Negative eq_refl) as Neg;rewrite Rabs_left by exact Neg;lra.
 - pose proof (proj1 Nonnegative eq_refl) as Pos;rewrite Rabs_pos_eq by exact Pos;reflexivity.
Qed.
Lemma trig_sin_identity_correct x : finite x ->
 (trig_sin_identity x=true <-> Rabs(B x)<=B trig_sin_is_x) /\
 (trig_sin_identity x=false <-> B trig_sin_is_x<Rabs(B x)).
Proof.
 intro F;unfold trig_sin_identity.
 rewrite (Bcompare_correct 53 1024 _ _ (trig_abs_finite x F) trig_sin_is_x_finite),B_abs.
 destruct (Rcompare_spec (Rabs(B x)) (B trig_sin_is_x));split;split;intros;try reflexivity;try discriminate;lra.
Qed.
Lemma trig_cos_screen_correct x : finite x ->
 (trig_cos_screen x=true <-> Rabs(B x)<bpow radix2 (-25)) /\
 (trig_cos_screen x=false <-> bpow radix2 (-25)<=Rabs(B x)).
Proof.
 intro F;unfold trig_cos_screen.
 rewrite (Bcompare_correct 53 1024 _ _ (trig_abs_finite x F) trig_cos_small_limit_finite),B_abs,trig_cos_small_limit_value.
 destruct (Rcompare_spec (Rabs(B x)) (bpow radix2 (-25)));split;split;intros;try reflexivity;try discriminate;lra.
Qed.

Lemma trig_public_round_error v :
 Rabs(rndF v-v)<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) v.
Proof.
 pose proof (relative_ulp_error 0 v v ltac:(split;[lra|apply bpow_gt_0])
  ltac:(rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;lra)) as Error.
 apply Rle_trans with (1:=Error).
 apply Rmult_le_compat_r;[apply ulp_ge_0|]. pose proof (bpow_ge_0 radix2 (-145));nra.
Qed.
Theorem trig_public_finish_ulp x cosine : finite x -> bpow radix2 (-63)<=Rabs(B x) ->
 let y:=trig_public_finish x cosine in
 let v:=if cosine then cos(B x) else sin(B x) in
 finite y /\ Rabs(B y-v)<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) v.
Proof.
 intros F X;cbv zeta.
 pose proof (trig_finish_ulp (b64_abs x) (trig_negative x) cosine
   (trig_abs_finite x F) ltac:(rewrite B_abs;exact X)) as Result.
 cbv zeta in Result. rewrite (trig_public_argument x F) in Result;exact Result.
Qed.
Theorem trig_sin_entry_ulp x : finite x ->
 finite(trig_sin_entry x) /\
 Rabs(B(trig_sin_entry x)-sin(B x))<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) (sin(B x)).
Proof.
 intro F;unfold trig_sin_entry;rewrite F.
 destruct (trig_sin_identity x) eqn:Screen.
 - apply (proj1 (trig_sin_identity_correct x F)) in Screen.
   split;[exact F|].
   pose proof (trig_sin_screen_round (B x) (B_fmt x) Screen) as Round.
   rewrite <-Round at 1;apply trig_public_round_error.
 - apply (proj2 (trig_sin_identity_correct x F)) in Screen.
   apply (trig_public_finish_ulp x false F).
   pose proof trig_sin_is_x_bounds as Cutoff.
   assert (bpow radix2 (-63)<=bpow radix2 (-26)) by (apply bpow_le;lia);lra.
Qed.
Theorem trig_cos_entry_ulp x : finite x ->
 finite(trig_cos_entry x) /\
 Rabs(B(trig_cos_entry x)-cos(B x))<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) (cos(B x)).
Proof.
 intro F;unfold trig_cos_entry;rewrite F.
 destruct (trig_cos_screen x) eqn:Screen.
 - apply (proj1 (trig_cos_screen_correct x F)) in Screen.
   destruct (trig_cos_abs_small_correct x F Screen) as [Y Value].
   split;[exact Y|];rewrite Value;apply trig_public_round_error.
 - apply (proj2 (trig_cos_screen_correct x F)) in Screen.
   apply (trig_public_finish_ulp x true F).
   apply Rle_trans with (2:=Screen);apply bpow_le;lia.
Qed.

Theorem trig_sincos_entry_pair x : trig_sincos_entry x=(trig_sin_entry x,trig_cos_entry x).
Proof.
 unfold trig_sincos_entry,trig_sin_entry,trig_cos_entry.
 destruct (is_finite 53 1024 x),(trig_sin_identity x),(trig_cos_screen x);reflexivity.
Qed.
Theorem trig_entry_nonfinite x : is_finite 53 1024 x=false ->
 trig_sin_entry x=trig_nan /\ trig_cos_entry x=trig_nan /\
 trig_sincos_entry x=(trig_nan,trig_nan) /\ is_nan 53 1024 trig_nan=true.
Proof.
 intro F;rewrite trig_sincos_entry_pair;unfold trig_sin_entry,trig_cos_entry;rewrite F.
 repeat split;reflexivity.
Qed.
Theorem trig_entry_zeros :
 bits_of_b64(trig_sin_entry(b64_of_bits 0))=0%Z /\
 bits_of_b64(trig_sin_entry(b64_of_bits 9223372036854775808))=9223372036854775808%Z /\
 bits_of_b64(trig_cos_entry(b64_of_bits 0))=4607182418800017408%Z /\
 bits_of_b64(trig_cos_entry(b64_of_bits 9223372036854775808))=4607182418800017408%Z.
Proof. vm_compute;repeat split;reflexivity. Qed.
