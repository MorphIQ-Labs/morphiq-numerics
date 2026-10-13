(** Public scalar guarantees, including screens and nonfinite inputs. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import StageGappa ErfcxReciprocal ErfcxGaussianTarget ErfcxScaledAnalytic
  ErfcxReflectionSquare ErfcxGaussianOverflow ErfcxOneThreshold ErfcxPublicModel ErfcxPublicBounds.
Open Scope R_scope.
Lemma erfcx_limit_finite : finite reflection_limit.
Proof. exact(bits_finite 13851560577301767119 true 7495322764862415 (-48) eq_refl). Qed.
Lemma erfcx_finite_screen x : finite x ->
  is_nan 53 1024 x=false /\ erfcx_eq x erfcx_infinity=false.
Proof. intros F;destruct x;try discriminate;split;reflexivity. Qed.
Lemma erfcx_one_range : -/2<B erfcx_one_neg /\ B erfcx_one_pos<16.
Proof.
  destruct erfcx_one_pos_ok as [_ P];destruct erfcx_one_neg_ok as [_ N].
  rewrite P,N;bpow_num;split;lra.
Qed.
Lemma erfcx_regular_special x : finite x -> B reflection_limit<B x ->
  erfcx_special64 x=
    if erfcx_le erfcx_one_neg x && erfcx_le x erfcx_one_pos then Some one else None.
Proof.
  intros Fx X. destruct(erfcx_finite_screen x Fx) as [Nan Inf].
  assert (Overflow : erfcx_le x reflection_limit=false)
    by (apply erfcx_le_false;[exact Fx|apply erfcx_limit_finite|exact X]).
  unfold erfcx_special64;rewrite Nan,Overflow,Inf;reflexivity.
Qed.
Theorem erfcx_entry_table x : finite x -> -/2<=B x<16 ->
  erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53))
    (bpow radix2 (-123)+bpow radix2 (-1075)) (erfcx_entry64 x).
Proof.
  intros Fx X. pose proof reflection_limit_value as Limit.
  unfold erfcx_entry64;rewrite erfcx_regular_special by (assumption||lra).
  destruct(erfcx_le erfcx_one_neg x && erfcx_le x erfcx_one_pos) eqn:Small.
  - apply andb_true_iff in Small as [Lower Upper].
    destruct erfcx_one_pos_ok as [Fp _];destruct erfcx_one_neg_ok as [Fn _].
    apply erfcx_le_true in Lower,Upper;try assumption.
    pose proof(erfcx_one_round (B x) ltac:(split;assumption)) as Round.
    destruct one_ok as [Fone Vone].
    apply erfcx_exact_bounded;[exact Fone|rewrite Vone,Round;reflexivity|lra|pose proof(bpow_ge_0 radix2 (-123));lra].
  - apply erfcx_regular_table;assumption.
Qed.
Theorem erfcx_entry_negative x : finite x -> B reflection_limit<B x< -/2 ->
  erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-122))
    (bpow radix2 (-1075)) (erfcx_entry64 x).
Proof.
  intros Fx X. destruct erfcx_one_range as [N P].
  destruct erfcx_one_neg_ok as [Fn _].
  assert (Small : erfcx_le erfcx_one_neg x=false)
    by (apply erfcx_le_false;[exact Fn|exact Fx|lra]).
  unfold erfcx_entry64;rewrite erfcx_regular_special by (assumption||lra).
  rewrite Small;cbn [andb]. apply erfcx_regular_negative;assumption.
Qed.
Theorem erfcx_entry_tail x : finite x -> 16<=B x ->
  erfcx_bounded (positive_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-223))
    (bpow radix2 (-1075)) (erfcx_entry64 x).
Proof.
  intros Fx X. destruct erfcx_one_range as [N P]. pose proof reflection_limit_value as Limit.
  destruct erfcx_one_pos_ok as [Fp _].
  assert (Small : erfcx_le x erfcx_one_pos=false)
    by (apply erfcx_le_false;[exact Fx|exact Fp|lra]).
  unfold erfcx_entry64;rewrite erfcx_regular_special by (assumption||lra).
  rewrite Small,andb_false_r. apply erfcx_regular_tail;assumption.
Qed.
Theorem erfcx_entry_overflow x : finite x -> B x<=B reflection_limit ->
  erfcx_entry64 x=erfcx_infinity /\
  bpow radix2 1024-bpow radix2 970<=gaussian_erfcx(B x).
Proof.
  intros Fx X. split;[|apply gaussian_overflow_magnitude;exact X].
  destruct(erfcx_finite_screen x Fx) as [Nan _].
  assert (Overflow : erfcx_le x reflection_limit=true)
    by (apply erfcx_le_true;[exact Fx|apply erfcx_limit_finite|exact X]).
  unfold erfcx_entry64,erfcx_special64;rewrite Nan,Overflow;reflexivity.
Qed.
Theorem erfcx_entry_nan x : is_nan 53 1024 x=true -> erfcx_entry64 x=x.
Proof. intros Nan;unfold erfcx_entry64,erfcx_special64;rewrite Nan;reflexivity. Qed.
Theorem erfcx_entry_infinities :
  erfcx_entry64 (B754_infinity 53 1024 false)=erfcx_zero /\
  erfcx_entry64 (B754_infinity 53 1024 true)=erfcx_infinity.
Proof. split;reflexivity. Qed.
Theorem erfcx_entry_zeros : erfcx_entry64 (B754_zero 53 1024 false)=one /\ erfcx_entry64 (B754_zero 53 1024 true)=one.
Proof. split;reflexivity. Qed.

Definition erfcx_finite_contract x y :=
  if Rle_dec (B x)(B reflection_limit) then
    y=erfcx_infinity /\ bpow radix2 1024-bpow radix2 970<=gaussian_erfcx(B x)
  else if Rlt_dec (B x)(-/2) then
    erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-122)) (bpow radix2 (-1075)) y
  else if Rlt_dec (B x)16 then
    erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53)) (bpow radix2 (-123)+bpow radix2 (-1075)) y
  else erfcx_bounded (positive_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-223)) (bpow radix2 (-1075)) y.
Theorem erfcx_finite_entry_contract x : finite x -> erfcx_finite_contract x (erfcx_entry64 x).
Proof.
  intros Fx;unfold erfcx_finite_contract.
  destruct(Rle_dec (B x)(B reflection_limit));[apply erfcx_entry_overflow;assumption|].
  destruct(Rlt_dec (B x)(-/2));[apply erfcx_entry_negative;[exact Fx|lra]|].
  destruct(Rlt_dec (B x)16);[apply erfcx_entry_table;[exact Fx|lra]|].
  apply erfcx_entry_tail;[exact Fx|lra].
Qed.
Definition erfcx_contract x y :=
  match x with
  | B754_nan _ _ _ => y=x
  | B754_infinity sign => y=if sign then erfcx_infinity else erfcx_zero
  | _ => erfcx_finite_contract x y
  end.
Theorem erfcx_public_contract x : erfcx_contract x (erfcx_entry64 x).
Proof.
  destruct x;cbn [erfcx_contract];try(apply erfcx_finite_entry_contract;reflexivity);try reflexivity.
  match goal with sign:bool|-_=>destruct sign;reflexivity end.
Qed.
