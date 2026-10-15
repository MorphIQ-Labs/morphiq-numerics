(** Correct the erfcx high-word kernel for the retained low argument.
    The final TwoSum is exact; the preceding scalar operations are rounded. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxGaussianTarget NormalErfcxSensitivity NormalErfcxLinear
  NormalErfcxFastBase NormalErfcxDerivative.
Open Scope R_scope.

Definition normal_erfcx_correction64 z d :=
  let '(h,l):=normal_erfcx_fast_base64 z in
  let derivative:=normal_erfcx_derivative64 z h in
  two_sum64 h (fadd l (fmul d derivative)).

Theorem normal_erfcx_correction_ieee z d : finite z -> finite d ->
  /4<=B z<=32 -> Rabs(B d)<=bpow radix2 (-49) ->
  let '(h,l):=normal_erfcx_correction64 z d in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs((B h+B l)-gaussian_erfcx(B z+B d))<=
    3*bpow radix2 (-68)*gaussian_erfcx(B z)+bpow radix2 (-87).
Proof.
  intros Fz Fd Z D;pose proof(normal_erfcx_fast_base_ieee z Fz Z)as Base.
  pose proof(normal_erfcx_fast_base_low z Fz Z)as BaseLow.
  unfold normal_erfcx_correction64;destruct(normal_erfcx_fast_base64 z)as[a b].
  destruct Base as[Fa [Fb [Anorm [A BaseError]]]].
  pose proof(normal_erfcx_compact_range(B z)ltac:(split;lra))as F.
  assert(HighError : Rabs(B a-gaussian_erfcx(B z))<=bpow radix2 (-49)).
  { replace(B a-gaussian_erfcx(B z))with(((B a+B b)-gaussian_erfcx(B z))-B b)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;bpow_num_all;nra. }
  destruct(normal_erfcx_derivative_ieee z a Fz Fa Z A HighError)as[Fder [DerRange DerError]].
  set(v:=normal_erfcx_derivative64 z a)in *.
  assert(Product : bnd 1 (-47)(B d*B v)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_mult;pose proof(Rabs_pos(B d));pose proof(Rabs_pos(B v));bpow_num_all;nra. }
  destruct(fmul_bnd 1 (-47)d v Fd Fder ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Product)as[Fp [Pvalue Prange]].
  unfold bnd in Product,Prange;rewrite Rmult_1_l in Product,Prange.
  pose proof(rnd_err_below _ (-47)ltac:(lia)Product)as Multiplication.
  rewrite <-Pvalue in Multiplication;change(-47-54)%Z with(-101)%Z in Multiplication.
  assert(Addition : bnd 1 (-46)(B b+B(fmul d v))).
  { unfold bnd;rewrite Rmult_1_l;eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  destruct(fadd_bnd 1 (-46)b (fmul d v)Fb Fp ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Addition)as[Fc [Cvalue Crange]].
  unfold bnd in Addition,Crange;rewrite Rmult_1_l in Addition,Crange.
  pose proof(rnd_err_below _ (-46)ltac:(lia)Addition)as Adding.
  rewrite <-Cvalue in Adding;change(-46-54)%Z with(-100)%Z in Adding.
  pose proof(two_sum_ieee a (fadd b (fmul d v))Fa Fc
    ltac:(rewrite Rabs_pos_eq by lra;eapply Rle_trans;[exact(proj2 A)|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Crange|interval with(i_prec 80)]))as Sum.
  destruct(two_sum64 a (fadd b (fmul d v)))as[h l].
  destruct Sum as[Fh [Fl [Norm Value]]].
  assert(Normalized : B h=rndF(B h+B l))by(rewrite Value;exact Norm).
  pose proof(normal_erfcx_linear_remainder(B z)(B d)Z D)as Taylor.
  assert(Correction : Rabs((B h+B l)-((B a+B b)+B d*normal_erfcx_derivative(B z)))<=
    bpow radix2 (-100)+bpow radix2 (-101)+bpow radix2 (-89)).
  { rewrite Value;replace(B a+B(fadd b (fmul d v))-((B a+B b)+B d*normal_erfcx_derivative(B z)))with
      ((B(fadd b (fmul d v))-(B b+B(fmul d v)))+(B(fmul d v)-B d*B v)+B d*(B v-normal_erfcx_derivative(B z)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
    rewrite Rabs_mult;pose proof(Rabs_pos(B d));pose proof(Rabs_pos(B v-normal_erfcx_derivative(B z)));bpow_num_all;nra. }
  repeat split;try assumption.
  replace((B h+B l)-gaussian_erfcx(B z+B d))with
    (((B h+B l)-((B a+B b)+B d*normal_erfcx_derivative(B z)))+
     ((B a+B b)-gaussian_erfcx(B z))-
     (gaussian_erfcx(B z+B d)-(gaussian_erfcx(B z)+B d*normal_erfcx_derivative(B z))))by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp.
  eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
  apply Rabs_le_inv in D;bpow_num_all;nra.
Qed.
