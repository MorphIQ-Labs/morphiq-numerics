(** Rounded evaluation of F'(z)=2*z*F(z)-2/sqrt(pi). The high word
    suffices here because the derivative is multiplied by the low argument. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa ErfcxDecision ErfcxConstants ErfcxGaussianTarget
  NormalConstants NormalErfcxSensitivity.
Open Scope R_scope.

Definition normal_erfcx_derivative64 z f :=
  fsub(fmul(fmul(erfcx_pow2 1)z)f)normal_two_inv_sqrt_pi_hi.

Theorem normal_erfcx_derivative_ieee z f : finite z -> finite f ->
  /4<=B z<=32 -> 0<B f<=8 -> Rabs(B f-gaussian_erfcx(B z))<=bpow radix2 (-49) ->
  finite(normal_erfcx_derivative64 z f) /\ Rabs(B(normal_erfcx_derivative64 z f))<=4 /\
  Rabs(B(normal_erfcx_derivative64 z f)-normal_erfcx_derivative(B z))<=bpow radix2 (-40).
Proof.
  intros Fz Ff Z F Error;destruct(erfcx_pow2_ok 1 ltac:(lia))as[Ftwo Two];change(bpow radix2 1)with 2 in Two.
  destruct normal_two_inv_sqrt_pi_hi_ok as[Fc C].
  assert(Constant : Rabs(B normal_two_inv_sqrt_pi_hi-2*inv_sqrt_pi)<=bpow radix2 (-52)).
  { rewrite C;unfold inv_sqrt_pi;bpow_num;interval with(i_prec 160). }
  assert(FirstRange : bnd 1 6 (B(erfcx_pow2 1)*B z)).
  { unfold bnd;rewrite Two,Rmult_1_l;change(bpow radix2 6)with 64;rewrite Rabs_mult,(Rabs_pos_eq 2),(Rabs_pos_eq(B z))by lra;nra. }
  destruct(fmul_bnd 1 6 (erfcx_pow2 1)z Ftwo Fz ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)FirstRange)as[Fp [Pvalue Prange]].
  unfold bnd in Prange,FirstRange;rewrite Rmult_1_l in Prange,FirstRange.
  pose proof(rnd_err_below _ 6 ltac:(lia)FirstRange)as FirstError.
  rewrite <-Pvalue,Two in FirstError;change(6-54)%Z with(-48)%Z in FirstError.
  assert(SecondRange : bnd 1 9 (B(fmul(erfcx_pow2 1)z)*B f)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_mult,(Rabs_pos_eq(B f))by lra.
    pose proof(Rabs_pos(B(fmul(erfcx_pow2 1)z)));bpow_num_all;nra. }
  destruct(fmul_bnd 1 9 (fmul(erfcx_pow2 1)z)f Fp Ff ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)SecondRange)as[Fm [Mvalue Mrange]].
  unfold bnd in Mrange,SecondRange;rewrite Rmult_1_l in Mrange,SecondRange.
  pose proof(rnd_err_below _ 9 ltac:(lia)SecondRange)as SecondError.
  rewrite <-Mvalue in SecondError;change(9-54)%Z with(-45)%Z in SecondError.
  assert(SubRange : bnd 1 10 (B(fmul(fmul(erfcx_pow2 1)z)f)-B normal_two_inv_sqrt_pi_hi)).
  { unfold bnd;rewrite Rmult_1_l;eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,C;bpow_num_all;interval with(i_prec 80). }
  destruct(fsub_bnd 1 10 (fmul(fmul(erfcx_pow2 1)z)f)normal_two_inv_sqrt_pi_hi Fm Fc
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)SubRange)as[Fd [Dvalue Drange]].
  fold(normal_erfcx_derivative64 z f)in Fd,Dvalue,Drange.
  unfold bnd in SubRange;rewrite Rmult_1_l in SubRange.
  pose proof(rnd_err_below _ 10 ltac:(lia)SubRange)as ThirdError.
  rewrite <-Dvalue in ThirdError;change(10-54)%Z with(-44)%Z in ThirdError.
  assert(Bound : Rabs(B(normal_erfcx_derivative64 z f)-normal_erfcx_derivative(B z))<=bpow radix2 (-40)).
  { unfold normal_erfcx_derivative.
    replace(B(normal_erfcx_derivative64 z f)-(2*B z*gaussian_erfcx(B z)-2*inv_sqrt_pi))with
      ((B(normal_erfcx_derivative64 z f)-(B(fmul(fmul(erfcx_pow2 1)z)f)-B normal_two_inv_sqrt_pi_hi))+
       (B(fmul(fmul(erfcx_pow2 1)z)f)-B(fmul(erfcx_pow2 1)z)*B f)+
       (B(fmul(erfcx_pow2 1)z)-2*B z)*B f+2*B z*(B f-gaussian_erfcx(B z))-
       (B normal_two_inv_sqrt_pi_hi-2*inv_sqrt_pi))by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp.
    eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r;apply Rplus_le_compat_r;apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r;apply Rplus_le_compat_r;apply Rplus_le_compat_r;apply Rabs_triang|].
    rewrite !Rabs_mult,(Rabs_pos_eq 2),(Rabs_pos_eq(B z)),(Rabs_pos_eq(B f))by lra.
    pose proof(Rabs_pos(B(fmul(erfcx_pow2 1)z)-2*B z));pose proof(Rabs_pos(B f-gaussian_erfcx(B z)));bpow_num_all;nra. }
  pose proof(normal_erfcx_derivative_bounds(B z)ltac:(lra))as[Derivative _].
  assert(Pi : inv_sqrt_pi<=1)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
  pose proof(Rabs_triang_inv(B(normal_erfcx_derivative64 z f))(normal_erfcx_derivative(B z)))as Range.
  rewrite(Rabs_left1(normal_erfcx_derivative(B z)))in Range by lra.
  repeat split;try assumption;bpow_num_all;lra.
Qed.
