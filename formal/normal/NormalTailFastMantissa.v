(** The unscaled fast normal tail combines the original Gaussian with the
    low-word-corrected erfcx factor before applying its external exponent. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxProduct ErfcxGaussianTarget NormalGaussianKernel NormalGaussianRange
  NormalErfcxFastScaled NormalErfcxFastRange NormalTailAnalytic.
Open Scope R_scope.

Lemma normal_tail_fast_product_error a b c :
  Rabs a<=bpow radix2 (-69) -> Rabs b<=bpow radix2 (-66) -> Rabs c<=bpow radix2 (-77) ->
  Rabs((1+a)*(1+b)*(1+c)-1)<=(5*bpow radix2 (-68)).
Proof.
  intros A B C;apply Rabs_le_inv in A,B,C;bpow_num_all;apply Rabs_le;split;interval with(i_prec 240).
Qed.

Definition normal_tail_fast_mantissa64 x :=
  let '(gh,gl,k):=normal_gaussian64 x in
  let '(fh,fl):=normal_erfcx_fast_scaled64 x in
  let '(h,l):=product64 gh gl fh fl in(h,l,k-1)%Z.

Theorem normal_tail_fast_mantissa_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l,k):=normal_tail_fast_mantissa64 x in
  finite h /\ finite l /\ (-991<=k<= -1)%Z /\ B h=rndF(B h+B l) /\
  bpow radix2 (-10)<=B h<=4 /\ -/2^51<=B l/B h<=/2^51 /\
  Rabs((B h+B l)-normal_tail(B x)/bpow radix2 k)<=(5*bpow radix2 (-68))*(normal_tail(B x)/bpow radix2 k).
Proof.
  intros Fx X;assert(Domain : bpow radix2 (-33)<=B x<=37)by(bpow_num;split;lra).
  pose proof(normal_gaussian_regular_ieee x Fx Domain)as Gaussian.
  pose proof(normal_gaussian_mantissa_range x Fx Domain)as GaussianWords.
  pose proof(normal_gaussian_exponent_range x Fx Domain)as Exponent.
  pose proof(normal_erfcx_fast_scaled_ieee x Fx X)as Erfcx.
  pose proof(normal_erfcx_fast_scaled_words x Fx X)as ErfcxWords.
  unfold normal_tail_fast_mantissa64;destruct(normal_gaussian64 x)as[[gh gl]k].
  destruct(normal_erfcx_fast_scaled64 x)as[fh fl].
  destruct Gaussian as[Fgh [Fgl [_ [Gnorm Gerror]]]].
  destruct GaussianWords as[_ [_ [Gh Gl]]].
  destruct Erfcx as[Ffh [Ffl [Fnorm [_ [_ Ferror]]]]].
  destruct ErfcxWords as[Fh Flo].
  assert(Glo : -/2^51<=B gl/B gh<=/2^51).
  { apply Rabs_le_inv in Gl;unfold Rdiv;bpow_num_all;split;interval with(i_prec 100). }
  pose proof(product_bounded_ieee gh gl fh fl Fgh Fgl Ffh Ffl
    ltac:(split;lra)ltac:(bpow_num_all;split;lra)ltac:(nra)Glo Flo)as Product.
  destruct(product64 gh gl fh fl)as[h l];destruct Product as[Fhigh [Flow [Perror [_ [Low [Ratio Norm]]]]]].
  set(g:=exp(-B x*B x/2)/bpow radix2 k)in *;set(f:=gaussian_erfcx(B x/sqrt 2))in *.
  assert(Gsum : 0.998<=B gh+B gl<=2.002).
  { apply Rabs_le_inv in Gl;bpow_num_all;split;lra. }
  assert(G : 0.99<=g<=2.01).
  { apply Rabs_le_inv in Gerror;bpow_num_all;split;lra. }
  assert(TailExponent : (-990<=k)%Z).
  { destruct(Z_le_gt_dec (-990)k);[assumption|].
    assert(Power : bpow radix2 k<=bpow radix2 (-991))by(apply bpow_le;lia).
    assert(Lower : bpow radix2 (-988)<exp(-37*37/2))by(interval with(i_prec 160)).
    assert(Monotone : exp(-37*37/2)<=exp(-B x*B x/2))by(apply exp_le;nra).
    assert(Identity : exp(-B x*B x/2)=g*bpow radix2 k)by(unfold g;field;apply Rgt_not_eq,bpow_gt_0).
    pose proof(bpow_gt_0 radix2 k);bpow_num_all;nra. }
  assert(Z : /3<=B x/sqrt 2<=27)by(split;interval with(i_prec 80)).
  assert(F : /256<=f<=7/8).
  { unfold f;split;[apply normal_erfcx_compact_lower;split;lra|apply normal_erfcx_tail_upper;exact(proj1 Z)]. }
  assert(Fsum : 0<B fh+B fl).
  { apply Rabs_le_inv in Ferror;bpow_num_all;nra. }
  assert(Aerror : Rabs(((B gh+B gl)-g)/g)<=bpow radix2 (-69)).
  { unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq g),Rabs_minus_sym by lra.
    apply(Rmult_le_reg_r g);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
  assert(Berror : Rabs(((B fh+B fl)-f)/f)<=bpow radix2 (-66)).
  { unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f)by lra.
    apply(Rmult_le_reg_r f);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
  assert(Cerror : Rabs(((B h+B l)-(B gh+B gl)*(B fh+B fl))/((B gh+B gl)*(B fh+B fl)))<=bpow radix2 (-77)).
  { replace(bpow radix2 (-77))with(/2^77)by(bpow_num;field);apply Rabs_le;exact Perror. }
  pose proof(normal_tail_fast_product_error _ _ _ Aerror Berror Cerror)as Combined.
  assert(Identity : B h+B l=g*f*((1+((B gh+B gl)-g)/g)*(1+((B fh+B fl)-f)/f)*
    (1+((B h+B l)-(B gh+B gl)*(B fh+B fl))/((B gh+B gl)*(B fh+B fl))))).
  { field;repeat split;lra. }
  assert(Error : Rabs((B h+B l)-g*f)<=(5*bpow radix2 (-68))*(g*f)).
  { rewrite Identity;replace(g*f*((1+((B gh+B gl)-g)/g)*(1+((B fh+B fl)-f)/f)*
      (1+((B h+B l)-(B gh+B gl)*(B fh+B fl))/((B gh+B gl)*(B fh+B fl))))-g*f)with
      ((g*f)*((1+((B gh+B gl)-g)/g)*(1+((B fh+B fl)-f)/f)*
      (1+((B h+B l)-(B gh+B gl)*(B fh+B fl))/((B gh+B gl)*(B fh+B fl)))-1))by ring.
    rewrite Rabs_mult,(Rabs_pos_eq(g*f))by nra.
    replace((5*bpow radix2 (-68))*(g*f))with((g*f)*(5*bpow radix2 (-68)))by ring.
    apply Rmult_le_compat_l;[nra|exact Combined]. }
  assert(High : bpow radix2 (-10)<=B h<=4).
  { assert(Leading : 0<B gh*B fh)by(apply Rmult_lt_0_compat;[lra|pose proof(bpow_gt_0 radix2 (-9));lra]).
    assert(Hvalue : B h=(B h/(B gh*B fh))*(B gh*B fh))by(field;split;bpow_num_all;lra).
    assert(LeadingRange : 0.999*bpow radix2 (-9)<=B gh*B fh<=2.001).
    { split.
      - apply Rmult_le_compat;[lra|apply bpow_ge_0|exact(proj1 Gh)|exact(proj1 Fh)].
      - replace 2.001 with(2.001*1)by ring;apply Rmult_le_compat;[lra|pose proof(bpow_gt_0 radix2 (-9));lra|exact(proj2 Gh)|exact(proj2 Fh)]. }
    set(p:=B gh*B fh)in *;clear -LeadingRange Ratio Hvalue;bpow_num_all;split;nra. }
  assert(Target : normal_tail(B x)/bpow radix2 (k-1)=g*f).
  { unfold normal_tail,g,f;replace(k-1)%Z with(k+ -1)%Z by ring;rewrite bpow_plus.
    change(bpow radix2 (-1))with(/2);field;apply Rgt_not_eq,bpow_gt_0. }
  rewrite Target;repeat split;try tauto;lia.
Qed.
