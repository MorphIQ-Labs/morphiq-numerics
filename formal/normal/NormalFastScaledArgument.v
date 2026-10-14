(** The fast tail's actual double-word x/sqrt(2) reduction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64NormalizedMul IEEE64Eft RoundingConstant.
Require Import StageGappa NormalConstants NormalCenterSmall NormalCenterFastTail.
Open Scope R_scope.

Definition normal_inv_sqrt2_constant64 := two_sum64 normal_inv_sqrt2_hi normal_inv_sqrt2_lo.
Lemma normal_inv_sqrt2_constant_exact :
  normal_inv_sqrt2_constant64=(normal_inv_sqrt2_hi,normal_inv_sqrt2_lo).
Proof.
  assert (Codes : let '(h,l):=normal_inv_sqrt2_constant64 in
    (bits_of_b64 h,bits_of_b64 l)=(bits_of_b64 normal_inv_sqrt2_hi,bits_of_b64 normal_inv_sqrt2_lo)).
  { vm_compute;reflexivity. }
  destruct normal_inv_sqrt2_constant64 as[h l];injection Codes as H L.
  assert (Injective : forall a b,bits_of_b64 a=bits_of_b64 b -> a=b).
  { intros a b Same.
    pose proof(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl a)as A.
    pose proof(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl b)as Bv.
    change(b64_of_bits(bits_of_b64 a)=a)in A;change(b64_of_bits(bits_of_b64 b)=b)in Bv.
    rewrite <-A,<-Bv,Same;reflexivity. }
  f_equal;apply Injective;assumption.
Qed.


Definition normal_fast_scaled_argument64 x :=
  let '(h,l):=normal_inv_sqrt2_constant64 in mul_f64_64 h l x.

Theorem normal_fast_scaled_argument_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_fast_scaled_argument64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  /4<=B h<=32 /\ Rabs(B l)<=bpow radix2 (-49) /\
  Rabs((B h+B l)-B x/sqrt 2)<=B x/sqrt 2*bpow radix2 (-103).
Proof.
  intros Fx X;destruct normal_inv_sqrt2_hi_ok as[Fh Hvalue],normal_inv_sqrt2_lo_ok as[Fl Lvalue].
  pose proof(two_sum_ieee normal_inv_sqrt2_hi normal_inv_sqrt2_lo Fh Fl
    ltac:(rewrite Hvalue;interval with(i_prec 80))ltac:(rewrite Lvalue;interval with(i_prec 80)))as Sum.
  fold normal_inv_sqrt2_constant64 in Sum.
  rewrite normal_inv_sqrt2_constant_exact in Sum;cbn[fst snd]in Sum.
  destruct Sum as[_ [_ [Norm Total]]].
  assert(Domain : in_two_prod_domain(B normal_inv_sqrt2_hi)(B x)).
  { right;rewrite Rabs_mult,(Rabs_pos_eq(B normal_inv_sqrt2_hi)),(Rabs_pos_eq(B x))by(rewrite ?Hvalue;lra).
    rewrite Hvalue;bpow_num;nra. }
  assert(Cross : normal_or_zero(B normal_inv_sqrt2_lo*B x)).
  { right;rewrite Rabs_mult,(Rabs_left1(B normal_inv_sqrt2_lo)),(Rabs_pos_eq(B x))by(rewrite ?Lvalue;lra).
    rewrite Lvalue;bpow_num;nra. }
  assert(Hbound : Rabs(B normal_inv_sqrt2_hi)<=bpow radix2 508)by(rewrite Hvalue;interval with(i_prec 80)).
  assert(Lbound : Rabs(B normal_inv_sqrt2_lo)<=bpow radix2 508)by(rewrite Lvalue;interval with(i_prec 80)).
  assert(Xbound : Rabs(B x)<=bpow radix2 508)by(rewrite Rabs_pos_eq by lra;eapply Rle_trans;[exact(proj2 X)|interval with(i_prec 80)]).
  pose proof(mul_f64_ieee normal_inv_sqrt2_hi normal_inv_sqrt2_lo x Fh Fl Fx Norm Hbound Lbound Xbound Domain Cross)as Product.
  pose proof(mul_f64_normalized_ieee normal_inv_sqrt2_hi normal_inv_sqrt2_lo x Fh Fl Fx Norm Hbound Lbound Xbound Domain Cross)as Normalized.
  unfold normal_fast_scaled_argument64;rewrite normal_inv_sqrt2_constant_exact;destruct(mul_f64_64 normal_inv_sqrt2_hi normal_inv_sqrt2_lo x)as[h l].
  destruct Product as[Fhigh [Flow Relative]];destruct Normalized as[_ [_ Normal]].
  assert(Eval : Rabs(((B h+B l)-(B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)*B x)/
    ((B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)*B x))<=bpow radix2 (-105)).
  { eapply Rle_trans;[exact Relative|];unfold prec;bpow_num;interval with(i_prec 240). }
  pose proof normal_inv_sqrt2_dw_error as Coefficient.
  set(a:=(B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)/(/sqrt 2)-1)in *.
  set(b:=((B h+B l)-(B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)*B x)/
    ((B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)*B x))in *.
  pose proof(normal_center_small_product_error a b Coefficient Eval)as Combined.
  assert(Cpositive : 0<B normal_inv_sqrt2_hi+B normal_inv_sqrt2_lo)by(rewrite Hvalue,Lvalue;interval with(i_prec 80)).
  assert(Sqrt : 1<sqrt 2<2)by(split;interval with(i_prec 80)).
  assert(Exact : B h+B l=(B x/sqrt 2)*((1+a)*(1+b))).
  { unfold a,b;field;repeat split;lra. }
  assert(Target : /3<=B x/sqrt 2<=27)by(split;interval with(i_prec 80)).
  assert(Error : Rabs((B h+B l)-B x/sqrt 2)<=B x/sqrt 2*bpow radix2 (-103)).
  { rewrite Exact;replace(B x/sqrt 2*((1+a)*(1+b))-B x/sqrt 2)with
      (B x/sqrt 2*((1+a)*(1+b)-1))by ring.
    rewrite Rabs_mult,(Rabs_pos_eq(B x/sqrt 2))by lra.
    apply Rmult_le_compat_l;[lra|exact Combined]. }
  assert(Range : /4<=B h+B l<=32).
  { apply Rabs_le_inv in Error;bpow_num_all;split;nra. }
  assert(High : /4<=B h<=32).
  { rewrite Normal;split.
    - change(/4)with(bpow radix2 (-2));apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 32 with(bpow radix2 5);apply round_le_generic;[exact _|exact _| |exact(proj2 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_err_below(B h+B l)5 ltac:(lia)ltac:(change(bpow radix2 5)with 32;rewrite Rabs_pos_eq;lra))as Rounded.
  rewrite <-Normal in Rounded;change(5-54)%Z with(-49)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-49)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;tauto.
Qed.
