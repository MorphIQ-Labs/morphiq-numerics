(** The accurate tail's hardware reciprocal seed, including subnormal seeds.
    Its 2^-51 error fits the widened shared Q256 Newton certificates. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxReciprocal.
Open Scope R_scope.

Lemma binary64_round_large_reciprocal z : bpow radix2 (-1024)<=Rabs z ->
  Rabs (rndF z-z)<=bpow radix2 (-51)*Rabs z.
Proof.
  intros Z.
  pose proof (@relative_error_N radix2 (FLT_exp (-1074) 53) ltac:(exact _)
    (-1024) 51 ltac:(intros k K; unfold FLT_exp; lia) ne z Z) as E.
  change (Rabs (rndF z-z)<=/2*bpow radix2 (-50)*Rabs z) in E.
  change (/2) with (bpow radix2 (-1)) in E.
  rewrite <- bpow_plus in E. exact E.
Qed.

Theorem accurate_reciprocal_seed_ieee x : finite x -> 16<=B x ->
  finite (fdiv one x) /\ Rabs (B x*B (fdiv one x)-1)<=bpow radix2 (-51).
Proof.
  intros Fx X. destruct one_ok as [F1 B1].
  assert (Y : 0<1/B x<=/16).
  { unfold Rdiv. rewrite Rmult_1_l. split;
      [apply Rinv_0_lt_compat | apply Rinv_le_contravar]; lra. }
  destruct (fdiv_ok 1 0 one x F1 ltac:(lra) ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite B1,Rmult_1_l; change (bpow radix2 0) with 1;
      apply Rabs_le; lra)) as [Fy By].
  rewrite B1 in By. split; [exact Fy | ].
  assert (Lower : bpow radix2 (-1024)<=Rabs (1/B x)).
  { rewrite Rabs_pos_eq by lra.
    change (-1024)%Z with (- (1024))%Z. rewrite bpow_opp. unfold Rdiv. rewrite Rmult_1_l.
    apply Rinv_le_contravar; [lra | ].
    pose proof (abs_B2R_lt_emax 53 1024 x) as Upper.
    rewrite Rabs_pos_eq in Upper by lra. lra. }
  pose proof (binary64_round_large_reciprocal (1/B x) Lower) as E.
  rewrite <- By in E. rewrite (Rabs_pos_eq (1/B x)) in E by lra.
  replace (B x*B (fdiv one x)-1) with ((B (fdiv one x)-1/B x)*B x) by (field; lra).
  rewrite Rabs_mult,(Rabs_pos_eq (B x)) by lra.
  replace (bpow radix2 (-51)) with ((bpow radix2 (-51)*(1/B x))*B x) by (field; lra).
  apply Rmult_le_compat_r; lra.
Qed.
