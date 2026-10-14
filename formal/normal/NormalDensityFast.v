(** The regular fast density composition, including scaling of the low
    word through gradual underflow and the final TwoSum normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxDecision NormalScale NormalDensityMantissa NormalAccurateDensity.
Open Scope R_scope.

Definition normal_density_fast64 x :=
  let '(h,l,k):=normal_density_mantissa64 x in
  let '(a,b):=two_sum64 (fmul h (erfcx_pow2 k))(fmul l (erfcx_pow2 k))in(a,b,k).

Theorem normal_density_fast_ieee x : finite x -> bpow radix2 (-33)<=B x<=37 ->
  let '(h,l,k):=normal_density_fast64 x in
  finite h /\ finite l /\ (-1000<=k<=0)%Z /\
  bpow radix2 k/8<=B h<=4*bpow radix2 k /\ Rabs(B l)<=bpow radix2 (k-52) /\
  B h=rndF(B h+B l) /\
  Rabs((B h+B l)-normal_density(B x))<=bpow radix2 (k-68).
Proof.
  intros F X;pose proof(normal_density_mantissa_ieee x F X)as Mantissa.
  unfold normal_density_fast64;destruct(normal_density_mantissa64 x)as[[h l]k].
  destruct Mantissa as[Fh [Fl [K [High [Low [Norm Error]]]]]].
  assert (Li : B l=(B l/B h)*B h)by(field;lra).
  assert (L : Rabs(B l)<=bpow radix2 (-50)).
  { apply Rabs_le;bpow_num_all;split;nra. }
  pose proof(normal_scaled_word_ieee h k Fh ltac:(rewrite Rabs_pos_eq;lra)K)as Hscale.
  pose proof(normal_scaled_word_ieee l k Fl ltac:(eapply Rle_trans;[exact L|interval with(i_prec 80)])K)as Lscale.
  set(a:=fmul h (erfcx_pow2 k))in *;set(b:=fmul l (erfcx_pow2 k))in *.
  destruct Hscale as[Fa [A [Ar [Ae Aexact]]]];destruct Lscale as[Fb [Bvalue [Br [Be Bexact]]]].
  specialize(Aexact ltac:(rewrite Rabs_pos_eq by lra;eapply Rle_trans;[|exact(proj1 High)];interval with(i_prec 80))).
  set(s:=bpow radix2 k)in *.
  assert (S : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert (LowError : Rabs(B b-B l*s)<=s*bpow radix2 (-74)).
  { unfold s;replace(k-74)%Z with(k+ -74)%Z in Be by ring;rewrite bpow_plus in Be;exact Be. }
  assert (Before : s/5<=B a+B b<=3*s).
  { apply Rabs_le_inv in LowError,L;rewrite Aexact;bpow_num_all;split;nra. }
  pose proof(two_sum_ieee a b Fa Fb
    ltac:(eapply Rle_trans;[exact Ar|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Br|interval with(i_prec 80)]))as Sum.
  destruct(two_sum64 a b)as[y z];destruct Sum as[Fy [Fz [Y Total]]].
  pose proof(rnd_err_below(B a+B b)(k+2)ltac:(lia))as Rounded.
  assert (Magnitude : Rabs(B a+B b)<=bpow radix2 (k+2)).
  { rewrite bpow_plus;change(bpow radix2 2)with 4;fold s;rewrite Rabs_pos_eq;lra. }
  specialize(Rounded Magnitude);rewrite <-Y in Rounded.
  replace(k+2-54)%Z with(k-52)%Z in Rounded by ring.
  assert (Z : Rabs(B z)<=bpow radix2 (k-52)).
  { replace(B z)with(-(B y-(B a+B b)))by lra;rewrite Rabs_Ropp;exact Rounded. }
  assert (Range : s/8<=B y<=4*s).
  { apply Rabs_le_inv in Rounded;replace(k-52)%Z with(k+ -52)%Z in Rounded by ring;rewrite bpow_plus in Rounded;fold s in Rounded;bpow_num_all;split;nra. }
  assert (Composition : Rabs((B y+B z)-normal_density(B x))<=bpow radix2 (k-68)).
  { rewrite Total,Aexact.
    replace(B h*s+B b-normal_density(B x))with
      ((((B h+B l)-normal_density(B x)/s)*s)+(B b-B l*s))by(field;lra).
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult,(Rabs_pos_eq s)by lra.
    assert (Scaled : Rabs((B h+B l)-normal_density(B x)/s)*s<=bpow radix2 (-69)*s).
    { apply Rmult_le_compat_r;lra. }
    replace(k-68)%Z with(k+ -68)%Z by ring;rewrite bpow_plus;fold s.
    assert(bpow radix2 (-69)+bpow radix2 (-74)<=bpow radix2 (-68))by(bpow_num;interval with(i_prec 100)).
    nra. }
  repeat split;try tauto.
  rewrite Total;exact Y.
Qed.
