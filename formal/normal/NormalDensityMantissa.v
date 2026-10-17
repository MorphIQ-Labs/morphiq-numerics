(** Fast density before final exponent scaling. Its original Gaussian,
    generated normalization constant, and actual double-word multiplication
    are composed with a quantitative absolute mantissa error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft RoundingConstant.
Require Import StageGappa NormalConstants NormalCentered NormalAccurateDensity
  NormalGaussianKernel NormalGaussianRange ErfcxProduct.
Open Scope R_scope.

Definition normal_density_constant64 := two_sum64 normal_density_hi normal_density_lo.

Lemma normal_density_constant_words : let '(h,l):=normal_density_constant64 in
  finite h /\ finite l /\ 3/8<=B h<=/2 /\ Rabs(B l)<=bpow radix2 (-54) /\
  B h+B l=B normal_density_hi+B normal_density_lo /\ B h=rndF(B h+B l).
Proof.
  destruct normal_density_hi_ok as[Fh H];destruct normal_density_lo_ok as[Fl L].
  assert (Range : 39/100<=B normal_density_hi+B normal_density_lo<=41/100).
  { rewrite H,L;split;interval with(i_prec 80). }
  pose proof(two_sum_ieee normal_density_hi normal_density_lo Fh Fl
    ltac:(rewrite H;interval with(i_prec 80))ltac:(rewrite L;interval with(i_prec 80)))as Sum.
  unfold normal_density_constant64;destruct(two_sum64 normal_density_hi normal_density_lo)as[h l].
  destruct Sum as[Fhigh [Flow [High Total]]].
  pose proof(rnd_err_below (B normal_density_hi+B normal_density_lo)0 ltac:(lia)
    ltac:(change(bpow radix2 0)with 1;apply Rabs_le;lra))as Error.
  rewrite <-High in Error;change(0-54)%Z with(-54)%Z in Error.
  assert (Low : Rabs(B l)<=bpow radix2 (-54)).
  { replace(B l)with(-(B h-(B normal_density_hi+B normal_density_lo)))by lra;rewrite Rabs_Ropp;exact Error. }
  assert (Normalized : B h=rndF(B h+B l))by(rewrite Total;exact High).
  repeat split;try assumption;apply Rabs_le_inv in Error;bpow_num_all;lra.
Qed.

Definition normal_density_mantissa64 x :=
  let '(gh,gl,k):=normal_gaussian64 x in
  let '(dh,dl):=normal_density_constant64 in
  let '(h,l):=product64 gh gl dh dl in(h,l,k).

Theorem normal_density_mantissa_ieee x : finite x -> bpow radix2 (-33)<=B x<=37 ->
  let '(h,l,k):=normal_density_mantissa64 x in
  finite h /\ finite l /\ (-1000<=k<=0)%Z /\
  /4<=B h<=2 /\ -bpow radix2 (-51)<=B l/B h<=bpow radix2 (-51) /\
  B h=rndF(B h+B l) /\
  Rabs((B h+B l)-normal_density(B x)/bpow radix2 k)<=bpow radix2 (-69).
Proof.
  intros F X;pose proof(normal_gaussian_regular_ieee x F X)as Gaussian.
  pose proof(normal_gaussian_mantissa_range x F X)as Words.
  pose proof(normal_gaussian_exponent_range x F X)as Exponent.
  pose proof normal_density_constant_words as Constant.
  unfold normal_density_mantissa64;destruct(normal_gaussian64 x)as[[gh gl]k].
  destruct normal_density_constant64 as[dh dl].
  destruct Gaussian as[Fgh [Fgl [K [Gnorm Gerror]]]].
  destruct Words as[_ [_ [Gh Gl]]];destruct Constant as[Fdh [Fdl [Dh [Dl [Dvalue Dnorm]]]]].
  assert (Glo : -/2^51<=B gl/B gh<=/2^51).
  { apply Rabs_le_inv in Gl;unfold Rdiv;bpow_num_all;split;interval with(i_prec 100). }
  assert (Dlo : -/2^51<=B dl/B dh<=/2^51).
  { apply Rabs_le_inv in Dl;unfold Rdiv;bpow_num_all;split;interval with(i_prec 100). }
  pose proof(product_bounded_ieee gh gl dh dl Fgh Fgl Fdh Fdl
    ltac:(split;lra)ltac:(split;lra)ltac:(nra)Glo Dlo)as Product.
  destruct(product64 gh gl dh dl)as[h l].
  destruct Product as[Fh [Fl [Error [High [Low [Ratio Norm]]]]]].
  assert (Hi : /4<=B h<=2).
  { assert(P : 0<B gh*B dh)by nra.
    assert(Identity : B h=(B h/(B gh*B dh))*(B gh*B dh))by(field;lra).
    assert(Lower : 3/8*0.999<=B gh*B dh)by nra.
    assert(Upper : B gh*B dh<=2.001/2)by nra.
    nra. }
  assert (Density : 3/8<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 80)).
  assert (Cerror : Rabs((B dh+B dl)-normal_density_constant)<=bpow radix2 (-105)).
  { pose proof normal_density_dw_error as Bound.
    change(Rabs((B normal_density_hi+B normal_density_lo)/normal_density_constant-1)<=bpow radix2 (-105))in Bound.
    rewrite <-Dvalue in Bound.
    replace(B dh+B dl-normal_density_constant)with
      (((B dh+B dl)/normal_density_constant-1)*normal_density_constant)by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra.
    pose proof(bpow_gt_0 radix2 (-105));nra. }
  assert (Gsum : 0<B gh+B gl<=3).
  { apply Rabs_le_inv in Gl;bpow_num_all;split;lra. }
  assert (Dsum : 0<B dh+B dl<=1).
  { apply Rabs_le_inv in Dl;bpow_num_all;split;lra. }
  assert (Multiplication : Rabs((B h+B l)-(B gh+B gl)*(B dh+B dl))<=3*bpow radix2 (-77)).
  { assert(P : 0<(B gh+B gl)*(B dh+B dl)<=3)by(split;nra).
    replace((B h+B l)-(B gh+B gl)*(B dh+B dl))with
      ((((B h+B l)-(B gh+B gl)*(B dh+B dl))/((B gh+B gl)*(B dh+B dl)))*
        ((B gh+B gl)*(B dh+B dl)))by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq((B gh+B gl)*(B dh+B dl)))by lra.
    assert(E : Rabs(((B h+B l)-(B gh+B gl)*(B dh+B dl))/((B gh+B gl)*(B dh+B dl)))<=bpow radix2 (-77)).
    { replace(bpow radix2 (-77))with(/2^77)by(bpow_num;field);apply Rabs_le;exact Error. }
    pose proof(bpow_gt_0 radix2 (-77));nra. }
  assert (Composition : Rabs((B gh+B gl)*(B dh+B dl)-normal_density(B x)/bpow radix2 k)<=
      3*bpow radix2 (-105)+209*bpow radix2 (-78)).
  { unfold normal_density.
    replace((B gh+B gl)*(B dh+B dl)-normal_density_constant*exp(-B x*B x/2)/bpow radix2 k)with
      ((B gh+B gl)*((B dh+B dl)-normal_density_constant)+
       ((B gh+B gl)-exp(-B x*B x/2)/bpow radix2 k)*normal_density_constant)by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|];rewrite !Rabs_mult,(Rabs_pos_eq(B gh+B gl)),(Rabs_pos_eq normal_density_constant)by lra.
    assert(G : Rabs((B gh+B gl)-exp(-B x*B x/2)/bpow radix2 k)<=209*bpow radix2 (-78)).
    { rewrite Rabs_minus_sym;exact Gerror. }
    pose proof(bpow_gt_0 radix2 (-105));pose proof(bpow_gt_0 radix2 (-78));nra. }
  repeat split;try assumption.
  - exact(proj1 Exponent).
  - exact(proj2 Exponent).
  - exact(proj1 Hi).
  - exact(proj2 Hi).
  - replace(bpow radix2 (-51))with(/2^51)by(bpow_num;field);exact(proj1 Low).
  - replace(bpow radix2 (-51))with(/2^51)by(bpow_num;field);exact(proj2 Low).
  - replace((B h+B l)-normal_density(B x)/bpow radix2 k)with
      (((B h+B l)-(B gh+B gl)*(B dh+B dl))+
       ((B gh+B gl)*(B dh+B dl)-normal_density(B x)/bpow radix2 k))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert(3*bpow radix2 (-77)+3*bpow radix2 (-105)+209*bpow radix2 (-78)<=bpow radix2 (-69))by(bpow_num;interval with(i_prec 120)).
    lra.
Qed.

Theorem normal_density_mantissa_extended_ieee x : finite x -> bpow radix2 (-33)<=B x<=39 ->
  let '(h,l,k):=normal_density_mantissa64 x in
  finite h /\ finite l /\ (-1100<=k<=0)%Z /\
  /4<=B h<=2 /\ -bpow radix2 (-51)<=B l/B h<=bpow radix2 (-51) /\
  B h=rndF(B h+B l) /\
  Rabs((B h+B l)-normal_density(B x)/bpow radix2 k)<=bpow radix2 (-69).
Proof.
  intros F X;pose proof(normal_gaussian_extended_ieee x F X)as Gaussian.
  pose proof(normal_gaussian_mantissa_range_extended x F X)as Words.
  pose proof(normal_gaussian_exponent_range_extended x F X)as Exponent.
  pose proof normal_density_constant_words as Constant.
  unfold normal_density_mantissa64;destruct(normal_gaussian64 x)as[[gh gl]k].
  destruct normal_density_constant64 as[dh dl].
  destruct Gaussian as[Fgh [Fgl [K [Gnorm Gerror]]]].
  destruct Words as[_ [_ [Gh Gl]]];destruct Constant as[Fdh [Fdl [Dh [Dl [Dvalue Dnorm]]]]].
  assert (Glo : -/2^51<=B gl/B gh<=/2^51).
  { apply Rabs_le_inv in Gl;unfold Rdiv;bpow_num_all;split;interval with(i_prec 100). }
  assert (Dlo : -/2^51<=B dl/B dh<=/2^51).
  { apply Rabs_le_inv in Dl;unfold Rdiv;bpow_num_all;split;interval with(i_prec 100). }
  pose proof(product_bounded_ieee gh gl dh dl Fgh Fgl Fdh Fdl
    ltac:(split;lra)ltac:(split;lra)ltac:(nra)Glo Dlo)as Product.
  destruct(product64 gh gl dh dl)as[h l].
  destruct Product as[Fh [Fl [Error [High [Low [Ratio Norm]]]]]].
  assert (Hi : /4<=B h<=2).
  { assert(P : 0<B gh*B dh)by nra.
    assert(Identity : B h=(B h/(B gh*B dh))*(B gh*B dh))by(field;lra).
    assert(Lower : 3/8*0.999<=B gh*B dh)by nra.
    assert(Upper : B gh*B dh<=2.001/2)by nra.
    nra. }
  assert (Density : 3/8<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 80)).
  assert (Cerror : Rabs((B dh+B dl)-normal_density_constant)<=bpow radix2 (-105)).
  { pose proof normal_density_dw_error as Bound.
    change(Rabs((B normal_density_hi+B normal_density_lo)/normal_density_constant-1)<=bpow radix2 (-105))in Bound.
    rewrite <-Dvalue in Bound.
    replace(B dh+B dl-normal_density_constant)with
      (((B dh+B dl)/normal_density_constant-1)*normal_density_constant)by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra.
    pose proof(bpow_gt_0 radix2 (-105));nra. }
  assert (Gsum : 0<B gh+B gl<=3).
  { apply Rabs_le_inv in Gl;bpow_num_all;split;lra. }
  assert (Dsum : 0<B dh+B dl<=1).
  { apply Rabs_le_inv in Dl;bpow_num_all;split;lra. }
  assert (Multiplication : Rabs((B h+B l)-(B gh+B gl)*(B dh+B dl))<=3*bpow radix2 (-77)).
  { assert(P : 0<(B gh+B gl)*(B dh+B dl)<=3)by(split;nra).
    replace((B h+B l)-(B gh+B gl)*(B dh+B dl))with
      ((((B h+B l)-(B gh+B gl)*(B dh+B dl))/((B gh+B gl)*(B dh+B dl)))*
        ((B gh+B gl)*(B dh+B dl)))by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq((B gh+B gl)*(B dh+B dl)))by lra.
    assert(E : Rabs(((B h+B l)-(B gh+B gl)*(B dh+B dl))/((B gh+B gl)*(B dh+B dl)))<=bpow radix2 (-77)).
    { replace(bpow radix2 (-77))with(/2^77)by(bpow_num;field);apply Rabs_le;exact Error. }
    pose proof(bpow_gt_0 radix2 (-77));nra. }
  assert (Composition : Rabs((B gh+B gl)*(B dh+B dl)-normal_density(B x)/bpow radix2 k)<=
      3*bpow radix2 (-105)+209*bpow radix2 (-78)).
  { unfold normal_density.
    replace((B gh+B gl)*(B dh+B dl)-normal_density_constant*exp(-B x*B x/2)/bpow radix2 k)with
      ((B gh+B gl)*((B dh+B dl)-normal_density_constant)+
       ((B gh+B gl)-exp(-B x*B x/2)/bpow radix2 k)*normal_density_constant)by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|];rewrite !Rabs_mult,(Rabs_pos_eq(B gh+B gl)),(Rabs_pos_eq normal_density_constant)by lra.
    assert(G : Rabs((B gh+B gl)-exp(-B x*B x/2)/bpow radix2 k)<=209*bpow radix2 (-78)).
    { rewrite Rabs_minus_sym;exact Gerror. }
    pose proof(bpow_gt_0 radix2 (-105));pose proof(bpow_gt_0 radix2 (-78));nra. }
  repeat split;try assumption.
  - exact(proj1 Exponent).
  - exact(proj2 Exponent).
  - exact(proj1 Hi).
  - exact(proj2 Hi).
  - replace(bpow radix2 (-51))with(/2^51)by(bpow_num;field);exact(proj1 Low).
  - replace(bpow radix2 (-51))with(/2^51)by(bpow_num;field);exact(proj2 Low).
  - replace((B h+B l)-normal_density(B x)/bpow radix2 k)with
      (((B h+B l)-(B gh+B gl)*(B dh+B dl))+
       ((B gh+B gl)*(B dh+B dl)-normal_density(B x)/bpow radix2 k))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert(3*bpow radix2 (-77)+3*bpow radix2 (-105)+209*bpow radix2 (-78)<=bpow radix2 (-69))by(bpow_num;interval with(i_prec 120)).
    lra.
Qed.
