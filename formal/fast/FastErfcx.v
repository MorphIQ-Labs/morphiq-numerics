(** Bounded erfcx: paired high-word table polynomial and strong fallback. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
Require Import StageGappa ErfcxReciprocal ErfcxDecision ErfcxGaussianTarget ErfcxTableEntry
  ErfcxTableBound ErfcxTableFast ErfcxTableAnalyticEntry ErfcxPublicModel
  ErfcxPublicEntry ErfcxTableReduction ErfcxTableCertificateModel
  FastErfcxEvaluation FastErfcxCertificates.
Open Scope R_scope.

Definition fast_erfcx_table64 x :=
 let '(i,c,h,e):=table_reduce64 x in fast_table_polynomial64 (Z.to_nat i) h.
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
  destruct (table_approximation_ieee x Fx X) as [Positive Approx].
  pose proof (table_reduce_ieee x Fx X) as Reduce.
  pose proof (table_reduce_exponent x Fx X) as Exponent.
  unfold fast_erfcx_table64,table_exact in *.
  destruct (table_reduce64 x) as [[[i c] h] e].
  destruct Reduce as [I [E [Fc [Fh [Exact H]]]]].
  assert (Hm : Rabs (B h)<=/8).
  { apply Rle_trans with (1:=H). change (/8) with (bpow radix2 (-3));apply bpow_le;lia. }
  destruct (fast_table_ieee (Z.to_nat i) h ltac:(lia) (conj Fh Hm)) as [Fy Value].
  destruct (fast_table_certificate (Z.to_nat i) (B h) ltac:(lia) (B_fmt h)
    ltac:(rewrite <-Exponent;exact H)) as [Eval Range].
  split;[exact Fy|]. rewrite Value. split;[bpow_num_all;lra|].
  set (p:=table_polynomial_exact (Z.to_nat i) (B h)) in *.
  set (y:=fast_table_value (Z.to_nat i) (B h)) in *.
  set (f:=gaussian_erfcx (B x)) in *.
  assert (Pid : (p-f)/f*f=p-f) by (field;lra).
  assert (Pbounds : (1-bpow radix2(-69))*f<=p<=(1+bpow radix2(-69))*f).
  { apply Rabs_le_inv in Approx. nra. }
  assert (Ppositive : 0<p) by (bpow_num_all;nra).
  assert (Yid : (y-p)/p*p=y-p) by (field;lra).
  apply Rabs_le. clear - Positive Pbounds Eval Pid Yid Ppositive.
  bpow_num_all;split;nra.

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
    (erfcx_le_true _ _ Fmin Fabs),N,V16,Vmin,B_abs.
  change((-/2<=B x /\ B x<16) /\ bpow radix2(-33)<=Rabs(B x) <->
    -/2<=B x<16 /\ bpow radix2(-33)<=Rabs(B x)).
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
  intros Nonfinite;destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;reflexivity.
  - reflexivity.
Qed.

Theorem fast_erfcx_zeros :
  fast_erfcx_entry64(B754_zero 53 1024 false)=one /\
  fast_erfcx_entry64(B754_zero 53 1024 true)=one.
Proof. split;reflexivity. Qed.
