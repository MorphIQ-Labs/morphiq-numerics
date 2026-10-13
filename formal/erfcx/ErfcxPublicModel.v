(** The scalar public dispatch, including special values and Q256 fallback. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Encodings.
From Q Require Q256.
Require Import StageGappa ErfcxReciprocal ErfcxOneThreshold ErfcxReflectionSquare
  ErfcxAccurateReflectionEntry ErfcxAccurateTaylorEntry ErfcxAccurateProduct
  ErfcxTableFast ErfcxMiddleFast ErfcxTailFast ErfcxScaledFast ErfcxScaledAnalytic
  ErfcxReflectionFast.
Open Scope R_scope.
Definition erfcx_negative_half : f64 := b64_of_bits 13826050856027422720.
Definition erfcx_five_twelve : f64 := b64_of_bits 4647714815446351872.
Definition erfcx_infinity : f64 := b64_of_bits 9218868437227405312.
Definition erfcx_zero : f64 := b64_of_bits 0.
Definition erfcx_lt x y := match Bcompare 53 1024 x y with Some Lt=>true | _=>false end.
Definition erfcx_le x y := match Bcompare 53 1024 x y with Some Lt|Some Eq=>true | _=>false end.
Definition erfcx_eq x y := match Bcompare 53 1024 x y with Some Eq=>true | _=>false end.
Definition erfcx_special64 x :=
  if is_nan 53 1024 x then Some x else
  if erfcx_le x reflection_limit then Some erfcx_infinity else
  if erfcx_eq x erfcx_infinity then Some erfcx_zero else
  if erfcx_le erfcx_one_neg x && erfcx_le x erfcx_one_pos then Some one else None.
Definition erfcx_fallback fast accurate :=
  match fast with Some y=>y | None=>Q256.to_f64 accurate end.
Definition erfcx_regular64 x :=
  if erfcx_lt x erfcx_negative_half then erfcx_fallback (reflection_fast64 x)(q_negative x) else
  if erfcx_lt x reflection_sixteen then erfcx_fallback (table_fast64 x)(q_taylor x) else
  if erfcx_lt x erfcx_five_twelve then erfcx_fallback (middle_fast64 x)(q_asym x) else
  if erfcx_lt erfcx_scaled_limit x then erfcx_fallback (tail_scaled_fast64 x)(q_asym x) else
    erfcx_fallback (tail_unscaled_fast64 x)(q_asym x).
Definition erfcx_entry64 x := match erfcx_special64 x with Some y=>y | None=>erfcx_regular64 x end.
Lemma erfcx_negative_half_ok : finite erfcx_negative_half /\ B erfcx_negative_half= -/2.
Proof.
  split;[exact(bits_finite 13826050856027422720 true 4503599627370496 (-53) eq_refl)|].
  unfold erfcx_negative_half;rewrite(bits_val 13826050856027422720 true 4503599627370496 53 eq_refl);simpl;field.
Qed.
Lemma erfcx_five_twelve_ok : finite erfcx_five_twelve /\ B erfcx_five_twelve=512.
Proof.
  split;[exact(bits_finite 4647714815446351872 false 4503599627370496 (-43) eq_refl)|].
  change (4503599627370496*bpow radix2 (-43)=512);bpow_num;field.
Qed.
Lemma erfcx_lt_true x y : finite x -> finite y -> (erfcx_lt x y=true <-> B x<B y).
Proof.
  intros Fx Fy;unfold erfcx_lt;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec (B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma erfcx_lt_false x y : finite x -> finite y -> (erfcx_lt x y=false <-> B y<=B x).
Proof.
  intros Fx Fy;unfold erfcx_lt;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec (B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma erfcx_le_true x y : finite x -> finite y -> (erfcx_le x y=true <-> B x<=B y).
Proof.
  intros Fx Fy;unfold erfcx_le;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec (B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma erfcx_le_false x y : finite x -> finite y -> (erfcx_le x y=false <-> B y<B x).
Proof.
  intros Fx Fy;unfold erfcx_le;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec (B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
