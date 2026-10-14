(** Linear centered-CDF branch: the omitted Gaussian terms and the actual
    normalized double-word product, including its input-domain obligations. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul IEEE64NormalizedMul.
Require Import StageGappa ErfcxGaussianSeries NormalCentered NormalConstants NormalDensityMantissa.
Open Scope R_scope.

Lemma normal_density_constant_exact :
  normal_density_constant64=(normal_density_hi,normal_density_lo).
Proof.
  assert (Codes : let '(h,l):=normal_density_constant64 in
    (bits_of_b64 h,bits_of_b64 l)=(bits_of_b64 normal_density_hi,bits_of_b64 normal_density_lo)).
  { vm_compute;reflexivity. }
  destruct normal_density_constant64 as[h l];injection Codes as H L.
  assert (Injective : forall a b,bits_of_b64 a=bits_of_b64 b -> a=b).
  { intros a b Same.
    pose proof(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl a)as A.
    pose proof(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl b)as Bv.
    change(b64_of_bits(bits_of_b64 a)=a)in A;change(b64_of_bits(bits_of_b64 b)=b)in Bv.
    rewrite <-A,<-Bv,Same;reflexivity. }
  f_equal;apply Injective;assumption.
Qed.

Theorem normal_center_linear_error x : Rabs x<=bpow radix2 (-33) ->
  Rabs(normal_center x-normal_density_constant*x)<=normal_density_constant*Rabs x*bpow radix2 (-67).
Proof.
  intros X;pose proof(normal_center_polynomial_error 0 x)as Error.
  assert (Poly : normal_center_polynomial 0 x=normal_density_constant*x).
  { unfold normal_center_polynomial,gaussian_sum;cbn;field. }
  rewrite Poly in Error.
  replace((x*x/2)^1/INR(fact 1))with(x*x/2)in Error by(cbn;field).
  eapply Rle_trans;[exact Error|];apply Rmult_le_compat_l.
  - apply Rmult_le_pos;[unfold normal_density_constant;left;interval with(i_prec 80)|apply Rabs_pos].
  - apply Rabs_le_inv in X;bpow_num_all;nra.
Qed.

Lemma normal_center_small_product_error a b : Rabs a<=bpow radix2 (-105) ->
  Rabs b<=bpow radix2 (-105) -> Rabs((1+a)*(1+b)-1)<=bpow radix2 (-103).
Proof.
  intros A Bv;apply Rabs_le_inv in A,Bv;bpow_num_all;apply Rabs_le;split;interval with(i_prec 240).
Qed.

Definition normal_center_small64 x :=
  let '(h,l):=normal_density_constant64 in mul_f64_64 h l x.

Theorem normal_center_small_ieee x : finite x ->
  bpow radix2 (-450)<=Rabs(B x)<=bpow radix2 (-33) ->
  let '(h,l):=normal_center_small64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs((B h+B l)-normal_density_constant*B x)<=normal_density_constant*Rabs(B x)*bpow radix2 (-103) /\
  Rabs((B h+B l)-normal_center(B x))<=normal_density_constant*Rabs(B x)*bpow radix2 (-66).
Proof.
  intros Fx X;pose proof normal_density_constant_words as Words;rewrite normal_density_constant_exact in Words.
  destruct Words as[Fh [Fl [High [Low [Value Norm]]]]].
  destruct normal_density_hi_ok as[_ Hvalue];destruct normal_density_lo_ok as[_ Lvalue].
  assert (Constant : 0<normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
  assert (Xpositive : 0<Rabs(B x))by(pose proof(bpow_gt_0 radix2 (-450));lra).
  assert (Xsmall : Rabs(B x)<=1)by(eapply Rle_trans;[exact(proj2 X)|interval with(i_prec 80)]).
  assert (LowerLow : bpow radix2 (-56)<=Rabs(B normal_density_lo)).
  { rewrite Lvalue;bpow_num;interval with(i_prec 100). }
  assert (Domain : in_two_prod_domain(B normal_density_hi)(B x)).
  { right;rewrite Rabs_mult,(Rabs_pos_eq(B normal_density_hi))by lra.
    eapply Rle_trans with(bpow radix2 (-452));[apply bpow_le;lia|].
    replace(bpow radix2 (-452))with(bpow radix2 (-2)*bpow radix2 (-450))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_le_compat;[apply bpow_ge_0|apply bpow_ge_0|change(bpow radix2 (-2))with(/4);lra|exact(proj1 X)]. }
  assert (Cross : normal_or_zero(B normal_density_lo*B x)).
  { right;rewrite Rabs_mult;eapply Rle_trans with(bpow radix2 (-506));[apply bpow_le;lia|].
    replace(bpow radix2 (-506))with(bpow radix2 (-56)*bpow radix2 (-450))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_le_compat;[apply bpow_ge_0|apply bpow_ge_0|exact LowerLow|exact(proj1 X)]. }
  assert (Hbound : Rabs(B normal_density_hi)<=bpow radix2 508)by(rewrite Hvalue;interval with(i_prec 80)).
  assert (Lbound : Rabs(B normal_density_lo)<=bpow radix2 508)by(rewrite Lvalue;interval with(i_prec 80)).
  assert (Xbound : Rabs(B x)<=bpow radix2 508)by(eapply Rle_trans;[exact Xsmall|interval with(i_prec 80)]).
  pose proof(mul_f64_ieee normal_density_hi normal_density_lo x Fh Fl Fx Norm Hbound Lbound Xbound Domain Cross)as Product.
  pose proof(mul_f64_normalized_ieee normal_density_hi normal_density_lo x Fh Fl Fx Norm Hbound Lbound Xbound Domain Cross)as Normalized.
  unfold normal_center_small64;rewrite normal_density_constant_exact;destruct(mul_f64_64 normal_density_hi normal_density_lo x)as[h l].
  destruct Product as[Fhigh [Flow Relative]];destruct Normalized as[_ [_ Normal]].
  assert (Eval : Rabs(((B h+B l)-(B normal_density_hi+B normal_density_lo)*B x)/
      ((B normal_density_hi+B normal_density_lo)*B x))<=bpow radix2 (-105)).
  { eapply Rle_trans;[exact Relative|];unfold prec;bpow_num;interval with(i_prec 240). }
  pose proof normal_density_dw_error as Coefficient.
  change(Rabs((B normal_density_hi+B normal_density_lo)/normal_density_constant-1)<=bpow radix2 (-105))in Coefficient.
  set(a:=(B normal_density_hi+B normal_density_lo)/normal_density_constant-1)in *.
  set(b:=((B h+B l)-(B normal_density_hi+B normal_density_lo)*B x)/
    ((B normal_density_hi+B normal_density_lo)*B x))in *.
  pose proof(normal_center_small_product_error a b Coefficient Eval)as Combined.
  assert (Cpositive : 0<B normal_density_hi+B normal_density_lo)by(rewrite Hvalue,Lvalue;interval with(i_prec 100)).
  assert (Nonzero : B x<>0)by(intros Z;rewrite Z,Rabs_R0 in Xpositive;lra).
  assert (Exact : B h+B l=normal_density_constant*B x*((1+a)*(1+b))).
  { unfold a,b;field;repeat split;lra. }
  assert (Linear : Rabs((B h+B l)-normal_density_constant*B x)<=normal_density_constant*Rabs(B x)*bpow radix2 (-103)).
  { rewrite Exact;replace(normal_density_constant*B x*((1+a)*(1+b))-normal_density_constant*B x)with
      (normal_density_constant*B x*((1+a)*(1+b)-1))by ring.
    rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra.
    apply Rmult_le_compat_l;[apply Rmult_le_pos;[lra|apply Rabs_pos]|exact Combined]. }
  split;[exact Fhigh|];split;[exact Flow|];split;[exact Normal|];split;[exact Linear|].
  pose proof(normal_center_linear_error (B x)(proj2 X))as Approximation.
  replace((B h+B l)-normal_center(B x))with
    (((B h+B l)-normal_density_constant*B x)+(normal_density_constant*B x-normal_center(B x)))by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_minus_sym(normal_density_constant*B x)(normal_center(B x))).
  assert(Budget : bpow radix2 (-103)+bpow radix2 (-67)<=bpow radix2 (-66))by(bpow_num;interval with(i_prec 200)).
  assert(Scale : 0<=normal_density_constant*Rabs(B x))by nra.
  nra.
Qed.
