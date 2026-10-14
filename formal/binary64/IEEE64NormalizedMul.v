(** The DW-times-binary64 result retains the normalization invariant.
    IEEE64Mul already proves its error bound on these same hypotheses. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Double Require Import DWPlus DWTimesFP.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul Instances.
Open Scope R_scope.

Theorem mul_f64_normalized_ieee xh xl y :
  finite xh -> finite xl -> finite y -> B xh=rndF(B xh+B xl) ->
  Rabs(B xh)<=bpow radix2 508 -> Rabs(B xl)<=bpow radix2 508 -> Rabs(B y)<=bpow radix2 508 ->
  in_two_prod_domain(B xh)(B y) -> normal_or_zero(B xl*B y) ->
  let '(h,l):=mul_f64_64 xh xl y in finite h /\ finite l /\ B h=rndF(B h+B l).
Proof.
  intros Fxh Fxl Fy Norm H L Y Domain Cross.
  assert (Bound : forall a,Rabs(B a)<=bpow radix2 508 -> bnd 1 508 (B a)).
  { intros a A;unfold bnd;rewrite Rmult_1_l;exact A. }
  destruct(mul_f64_64_ok 508 508 xh xl y Fxh Fxl Fy (Bound xh H)(Bound xl L)(Bound y Y)
    ltac:(lia)ltac:(lia)ltac:(lia))as[Fh [Fl [Value _]]].
  pose proof(@DWTimesFP_correct prec ne eq_refl ltac:(unfold prec;lia)
    fast2mult_exact (TwoProd_Fast2Mult prec ne)(B xh)(B xl)(B y)
    (dw_of_binary64 _ _ (B_fmt xh)(B_fmt xl)Norm)(fmtF_fmtX _ (B_fmt y)))as Correct.
  rewrite <-(mul_f64_eq _ _ _ (B_fmt xh)(B_fmt xl)(B_fmt y)Domain Cross)in Correct.
  rewrite <-Value in Correct.
  destruct(mul_f64_64 xh xl y)as[h l];cbn[fst snd]in *.
  destruct Correct as[_ [_ Normalized]].
  split;[exact Fh|];split;[exact Fl|].
  rewrite(sum_round _ _ (B_fmt h)(B_fmt l));exact Normalized.
Qed.
