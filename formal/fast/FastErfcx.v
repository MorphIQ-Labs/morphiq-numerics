(** Bounded erfcx: sum the existing normalized table pair, without a Ziv
    decision, and retain the strong owner on every screened input. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
Require Import StageGappa ErfcxDecision ErfcxGaussianTarget ErfcxTableEntry
  ErfcxTableBound ErfcxTableFast ErfcxTableAnalyticEntry ErfcxPublicModel
  ErfcxPublicEntry.
Open Scope R_scope.

Definition fast_erfcx_table64 x := let '(h,l):=table_eval64 x in fadd h l.
Definition fast_erfcx_screen64 x :=
  erfcx_le erfcx_negative_half x && erfcx_lt x (erfcx_pow2 4) &&
  erfcx_le (erfcx_pow2 (-33)) (b64_abs x).
Definition fast_erfcx_entry64 x :=
  if fast_erfcx_screen64 x then fast_erfcx_table64 x else erfcx_entry64 x.

(** This lemma also covers tiny positive arguments produced by the CDF's
    scaling. Its domain is the table's domain, not the public fast screen. *)
Theorem fast_erfcx_table_ok x : finite x -> -/2<=B x<16 ->
  finite(fast_erfcx_table64 x) /\
  bpow radix2 (-9)<=B(fast_erfcx_table64 x)<=8 /\
  Rabs(B(fast_erfcx_table64 x)-gaussian_erfcx(B x))<=
    bpow radix2 (-51)*gaussian_erfcx(B x).
Proof.
  intros Fx X.
  destruct(table_approximation_ieee x Fx X)as[Positive Approx].
  pose proof(table_evaluation_error x Fx X)as Eval.
  pose proof(table_eval_normalized_ieee x Fx X)as Words.
  unfold fast_erfcx_table64;destruct(table_eval64 x)as[h l].
  destruct Eval as[_ [_ Eval]].
  destruct Words as[Fh [Fl [Value [Norm High]]]].
  pose proof(table_composed_error (B h+B l)(table_exact x)
    (gaussian_erfcx(B x)) Positive Approx Eval)as Error.
  rewrite(Rabs_pos_eq(gaussian_erfcx(B x)))in Error by lra.
  assert(Sum : bpow radix2 (-10)<B h+B l<16).
  { split.
    - destruct(Rlt_le_dec (bpow radix2(-10))(B h+B l));[assumption|].
      assert(rndF(B h+B l)<=bpow radix2(-10)).
      { apply round_le_generic;[exact _|exact _| |assumption].
        apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
      rewrite <-Norm in H;bpow_num_all;lra.
    - destruct(Rlt_le_dec (B h+B l)16);[assumption|].
      assert(16<=rndF(B h+B l)).
      { change 16 with(bpow radix2 4);apply round_ge_generic;[exact _|exact _| |assumption].
        apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
      rewrite <-Norm in H;lra. }
  assert(SumPositive : 0<B h+B l)by(pose proof(bpow_gt_0 radix2(-10));lra).
  assert(SumBound : bnd 1 4 (B h+B l)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;change(bpow radix2 4)with 16;lra. }
  destruct(fadd_bnd 1 4 h l Fh Fl ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)SumBound)
    as[Fout [Out _]].
  assert(Normal : bpow radix2(-1022)<=Rabs(B h+B l)).
  { rewrite Rabs_pos_eq by lra;eapply Rle_trans with(bpow radix2(-10));[apply bpow_le;lia|lra]. }
  pose proof(rnd_rel (B h+B l)Normal)as Round.
  change(Rabs(rndF(B h+B l)-(B h+B l))<=bpow radix2(-53)*Rabs(B h+B l))in Round.
  rewrite Rabs_pos_eq in Round by lra.
  assert(Combined : Rabs(B(fadd h l)-gaussian_erfcx(B x))<=
    bpow radix2(-51)*gaussian_erfcx(B x)).
  { rewrite Out.
    replace(rndF(B h+B l)-gaussian_erfcx(B x))with
      ((rndF(B h+B l)-(B h+B l))+((B h+B l)-gaussian_erfcx(B x)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite Rabs_minus_sym in Error.
    pose proof(Rabs_le_inv _ _ Error)as Interval.
    bpow_num_all;nra. }
  split;[exact Fout|];split;[rewrite Out,<-Norm;exact High|exact Combined].
Qed.

Theorem fast_erfcx_screen_finite x : finite x ->
  (fast_erfcx_screen64 x=true <->
    -/2<=B x<16 /\ bpow radix2(-33)<=Rabs(B x)).
Proof.
  intros Fx.
  destruct erfcx_negative_half_ok as[Fn N].
  destruct(erfcx_pow2_ok 4 ltac:(lia))as[F16 V16].
  destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fmin Vmin].
  assert(Fabs : finite(b64_abs x))by(unfold b64_abs;rewrite is_finite_Babs;exact Fx).
  unfold fast_erfcx_screen64;rewrite !andb_true_iff.
  rewrite(erfcx_le_true _ _ Fn Fx),(erfcx_lt_true _ _ Fx F16),
    (erfcx_le_true _ _ Fmin Fabs),N,V16,Vmin,B2R_Babs.
  change((-/2<=B x /\ B x<16) /\ bpow radix2(-33)<=Rabs(B x) <-> _).
  tauto.
Qed.

Theorem fast_erfcx_entry_ok x : finite x ->
  -/2<=B x<16 -> bpow radix2(-33)<=Rabs(B x) ->
  finite(fast_erfcx_entry64 x) /\
  bpow radix2(-9)<=B(fast_erfcx_entry64 x)<=8 /\
  Rabs(B(fast_erfcx_entry64 x)-gaussian_erfcx(B x))<=
    bpow radix2(-51)*gaussian_erfcx(B x).
Proof.
  intros Fx X Min;unfold fast_erfcx_entry64.
  rewrite(proj2(fast_erfcx_screen_finite x Fx)(conj X Min)).
  apply fast_erfcx_table_ok;assumption.
Qed.

Theorem fast_erfcx_fallback x : fast_erfcx_screen64 x=false ->
  fast_erfcx_entry64 x=erfcx_entry64 x.
Proof. intros Screen;unfold fast_erfcx_entry64;rewrite Screen;reflexivity. Qed.

Theorem fast_erfcx_fallback_contract x : fast_erfcx_screen64 x=false ->
  erfcx_contract x (fast_erfcx_entry64 x).
Proof. intros Screen;rewrite fast_erfcx_fallback by exact Screen;apply erfcx_public_contract. Qed.

Theorem fast_erfcx_nonfinite x : is_finite 53 1024 x=false ->
  fast_erfcx_entry64 x=erfcx_entry64 x.
Proof.
  destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;reflexivity.
  - reflexivity.
Qed.

Theorem fast_erfcx_zeros :
  fast_erfcx_entry64(B754_zero 53 1024 false)=one /\
  fast_erfcx_entry64(B754_zero 53 1024 true)=one.
Proof. split;reflexivity. Qed.
