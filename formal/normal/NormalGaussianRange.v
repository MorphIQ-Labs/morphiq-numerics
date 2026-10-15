(** Range of the scaled Gaussian used by the fast normal kernels. The
    exponent keeps both final scaling and its gradual-underflow error inside
    the composition guard. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ExpStageReduction ExpStageB ErfcxReflectionReduction
  ErfcxReflectionExp NormalGaussianKernel.
Open Scope R_scope.

Theorem normal_gaussian_exponent_range x : finite x -> bpow radix2 (-33)<=B x<=37 ->
  let '(_,_,k):=normal_gaussian64 x in (-1000<=k<=0)%Z.
Proof.
  intros F X;assert (Domain : bpow radix2 (-400)<=B x<=39).
  { split;[apply Rle_trans with(bpow radix2 (-33));[apply bpow_le;lia|exact(proj1 X)]|lra]. }
  pose proof(normal_half_square_exact x F Domain)as Square.
  unfold normal_gaussian64;destruct(normal_half_square64 x)as[h l].
  destruct Square as[Fh [Fl [Exact [High Low]]]].
  assert (Small : Rabs(B h)<710).
  { apply Rabs_le_inv in Low;apply Rabs_lt;pose proof(bpow_gt_0 radix2 (-33));bpow_num_all;split;nra. }
  pose proof(reflection_reduce_ieee h l Fh Small Fl Low)as Reduction.
  unfold reflection_exp64;destruct(reflection_reduce64 h l)as[[[j k]rh]rt].
  destruct(stage_b_at rh rt (Z.to_nat j))as[eh el].
  destruct(fast_two_sum64 eh el)as[yh yl];destruct(two_sum64 yh yl)as[a b].
  destruct Reduction as[ni [Index [J [K [Frh [Frt [Grid [Rh [Rt [Residual Error]]]]]]]]]].
  assert (R : Rabs(-B x*B x/2-IZR ni*L)<=0.000677).
  { replace(-B x*B x/2-IZR ni*L)with(B h-IZR ni*L+B l)by lra;exact Residual. }
  apply Rabs_le_inv in R;pose proof L_range as Ln.
  assert (Ni : (-512000<=ni<=0)%Z).
  { split.
    - destruct(Z_le_gt_dec (-512000)ni);[assumption|].
      assert(IZR ni<= -512001)by(apply IZR_le;lia).
      pose proof(bpow_gt_0 radix2 (-33));nra.
    - destruct(Z_le_gt_dec ni 0);[assumption|].
      assert(1<=IZR ni)by(apply IZR_le;lia);nra. }
  lia.
Qed.

Theorem normal_gaussian_mantissa_range x : finite x -> bpow radix2 (-33)<=B x<=37 ->
  let '(a,b,k):=normal_gaussian64 x in
  finite a /\ finite b /\ 0.999<=B a<=2.001 /\ Rabs(B b)<=bpow radix2 (-52).
Proof.
  intros F X;assert (Domain : bpow radix2 (-400)<=B x<=39).
  { split;[apply Rle_trans with(bpow radix2 (-33));[apply bpow_le;lia|exact(proj1 X)]|lra]. }
  pose proof(normal_half_square_exact x F Domain)as Square.
  unfold normal_gaussian64;destruct(normal_half_square64 x)as[h l].
  destruct Square as[Fh [Fl [Exact [High Low]]]].
  assert (Small : Rabs(B h)<710).
  { apply Rabs_le_inv in Low;apply Rabs_lt;pose proof(bpow_gt_0 radix2 (-33));bpow_num_all;split;nra. }
  pose proof(reflection_exp_ieee h l Fh Small Fl Low)as Exp.
  destruct(reflection_exp64 h l)as[[yh yl]k].
  destruct Exp as[Fyh [Fyl [K [Yh [Yl [Norm Error]]]]]].
  pose proof(two_sum_ieee yh yl Fyh Fyl
    ltac:(rewrite Rabs_pos_eq by lra;eapply Rle_trans;[exact(proj2 Yh)|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Yl|apply bpow_le;lia]))as Sum.
  destruct(two_sum64 yh yl)as[a b];destruct Sum as[Fa [Fb [A Total]]].
  assert (Same : B a=B yh)by(rewrite A;exact(eq_sym Norm)).
  assert (SameLow : B b=B yl)by lra.
  rewrite Same,SameLow;repeat split;try assumption;lra.
Qed.
