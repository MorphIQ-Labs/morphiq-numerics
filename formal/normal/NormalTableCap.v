(** The lookup immediately below 16 when an extended input rounds to 16. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64 Encodings.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxTableReduction ErfcxAccurateInputs
  ErfcxAccurateTaylorReduction ErfcxAccurateCenterModel NormalResidualGrid
  NormalTableLookup NormalErfcxTaylor.
Open Scope R_scope.

Definition normal_table_cap := b64_of_bits 4625196817309499391.
Definition normal_table_last_center := b64_of_bits 4625126448565321728.

Lemma normal_table_cap_ok : finite normal_table_cap /\ B normal_table_cap=16-bpow radix2 (-49).
Proof.
  split.
  - exact(bits_finite 4625196817309499391 false 9007199254740991 (-49) eq_refl).
  - pose proof(bits_val 4625196817309499391 false 9007199254740991 49 eq_refl)as Value.
    unfold normal_table_cap;rewrite Value;cbn[cond_Zopp];bpow_num;field.
Qed.

Theorem normal_table_cap_max h : finite h -> B h<16 -> B h<=B normal_table_cap.
Proof.
  intros F H. destruct normal_table_cap_ok as[_ Cap]. rewrite Cap.
  assert (P : pred radix2 (FLT_exp (-1074) 53) 16=16-bpow radix2 (-49)).
  { change 16 with(bpow radix2 4);rewrite pred_bpow;reflexivity. }
  rewrite <-P;apply pred_ge_gt;try exact _.
  - apply FLT_exp_valid;unfold Prec_gt_0;lia.
  - apply B_fmt.
  - change 16 with(bpow radix2 4);apply generic_format_bpow;unfold FLT_exp;lia.
  - exact H.
Qed.

Lemma normal_table_last_center_ok : finite normal_table_last_center /\ B normal_table_last_center=127/8.
Proof.
  split.
  - exact(bits_finite 4625126448565321728 false 8936830510563328 (-49) eq_refl).
  - pose proof(bits_val 4625126448565321728 false 8936830510563328 49 eq_refl)as Value.
    unfold normal_table_last_center;rewrite Value;cbn[cond_Zopp];field.
Qed.

Lemma normal_table_cap_reduction : table_reduce64 normal_table_cap=
  (176%Z,normal_table_last_center,fsub normal_table_cap normal_table_last_center,3%Z).
Proof.
  destruct normal_table_cap_ok as[F Value],ErfcxReciprocal.one_ok as[Fo Bo].
  assert (Above : 1<B normal_table_cap).
  { rewrite Value;assert(bpow radix2 (-49)<1)by(interval with(i_prec 80));lra. }
  unfold table_reduce64;rewrite(Bcompare_correct 53 1024 normal_table_cap ErfcxReciprocal.one F Fo),Bo.
  destruct(Rcompare_spec(B normal_table_cap)1)as[Low|Equal|High];try lra.
  assert (Bits : bits_of_b64 normal_table_cap=4625196817309499391%Z)by(vm_compute;reflexivity).
  unfold table_binade64;rewrite Bits.
  change ((176%Z,normal_table_last_center,fsub normal_table_cap normal_table_last_center,3%Z)=
    (176%Z,normal_table_last_center,fsub normal_table_cap normal_table_last_center,3%Z)).
  reflexivity.
Qed.

Theorem normal_extended_cap_radius x : valid x -> /4<=qval x<16 ->
  B(Q256.to_f64 x)=16 ->
  Rabs(qval(normal_q_erfcx_residual x normal_table_last_center))<=/8.
Proof.
  intros X Range Rounded.
  destruct(normal_table_input_round x X ltac:(split;lra))as[_ [_ [_ Difference]]].
  rewrite Rounded in Difference;apply Rabs_le_inv in Difference.
  destruct normal_table_last_center_ok as[Fc Center].
  apply normal_extended_residual_radius;try assumption;[split;lra|rewrite Center;split;lra|].
  rewrite Center;apply Rabs_le;split.
  - assert(Small : bpow radix2 (-49)<=/4)by(interval with(i_prec 80));lra.
  - lra.
Qed.

Definition normal_q_erfcx_capped_table x :=
  normal_q_erfcx_taylor_at x normal_table_last_center 176.

Theorem normal_q_erfcx_capped_table_error x : valid x -> /4<=qval x<16 ->
  B(Q256.to_f64 x)=16 ->
  valid(normal_q_erfcx_capped_table x) /\
  Rabs(qval(normal_q_erfcx_capped_table x)-ErfcxGaussianTarget.gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range Rounded. destruct normal_table_last_center_ok as[Fc Center].
  unfold normal_q_erfcx_capped_table;apply normal_q_erfcx_taylor_at_error;try assumption.
  - split;lra.
  - lia.
  - replace 176%nat with(Z.to_nat 176)by reflexivity.
    rewrite accurate_binade_center with(e:=3%Z)by lia.
    rewrite Center;change(bpow radix2 3)with 8.
    change(176-49-32*3)%Z with 31%Z;field.
  - apply normal_extended_cap_radius;assumption.
Qed.
