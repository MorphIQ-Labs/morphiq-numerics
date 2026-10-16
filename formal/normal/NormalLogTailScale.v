(** Restore the huge-tail exponent without double rounding or overflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxDecision NormalLogOverflow NormalLogOverflowConstants
  NormalTailAnalytic.
Open Scope R_scope.

Lemma normal_log_tail_rounded_finite x : finite x -> /2<=B x<B normal_log_overflow ->
  Rabs(rndF(ln(normal_tail(B x))))<bpow radix2 1024.
Proof.
  intros Fx X;pose proof(normal_log_tail_square_bounds x Fx (proj1 X))as Bounds.
  pose proof(normal_log_overflow_previous_input x Fx ltac:(split;lra))as Previous.
  pose proof(proj2 normal_log_overflow_bracket)as Bracket.
  set(p:=B normal_log_overflow-bpow radix2 460)in *.
  assert(Magnitude : Rabs(ln(normal_tail(B x)))<=p*p/2+1028).
  { apply Rabs_le;split;nra. }
  assert(Bound : bnd 9007199254740991 971 (ln(normal_tail(B x)))).
  { unfold bnd;pose proof(bpow_gt_0 radix2 (-112));nra. }
  pose proof(bnd_round 9007199254740991 971 _ ltac:(lia)ltac:(lia)Bound)as Rounded.
  eapply Rle_lt_trans;[exact Rounded|apply bnd_lt;lia].
Qed.

Definition normal_log_tail_up64 h := fmul (fmul h (erfcx_pow2 480)) (erfcx_pow2 480).

Lemma normal_log_tail_up_one h : finite h -> bpow radix2 (-900)<=Rabs(B h) ->
  Rabs(B h*bpow radix2 480)<bpow radix2 1024 ->
  finite(fmul h (erfcx_pow2 480)) /\ B(fmul h (erfcx_pow2 480))=B h*bpow radix2 480.
Proof.
  intros Fh H Limit;destruct(erfcx_pow2_ok 480 ltac:(lia))as[Fc C].
  assert(M : (-899<=mag radix2(B h))%Z).
  { apply mag_ge_bpow;change(-899-1)%Z with(-900)%Z;exact H. }
  destruct(fmul_exact h (erfcx_pow2 480) Fh Fc)as[Fv V].
  - rewrite C;apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia].
  - rewrite C;exact Limit.
  - rewrite C in V;split;assumption.
Qed.

Theorem normal_log_tail_up_exact h z : finite h -> bpow radix2 (-900)<=Rabs(B h) ->
  bpow radix2 (-900)<=Rabs z -> B h=rndF z ->
  Rabs(rndF(z*bpow radix2 960))<bpow radix2 1024 ->
  finite(normal_log_tail_up64 h) /\ B(normal_log_tail_up64 h)=rndF(z*bpow radix2 960).
Proof.
  intros Fh H Z Round Limit.
  assert(Znz : z<>0)by(intros E;rewrite E,Rabs_R0 in Z;pose proof(bpow_gt_0 radix2 (-900));lra).
  assert(M : (-899<=mag radix2 z)%Z).
  { apply mag_ge_bpow;change(-899-1)%Z with(-900)%Z;exact Z. }
  assert(Full : B h*bpow radix2 960=rndF(z*bpow radix2 960)).
  { rewrite Round,round_scale by assumption || lia;reflexivity. }
  assert(LimitFull : Rabs(B h*bpow radix2 960)<bpow radix2 1024)by(rewrite Full;exact Limit).
  assert(Middle : Rabs(B h*bpow radix2 480)<bpow radix2 1024).
  { replace(B h*bpow radix2 480)with((B h*bpow radix2 960)*bpow radix2 (-480))
      by(rewrite Rmult_assoc,<-bpow_plus;reflexivity).
    rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 (-480)))by apply bpow_ge_0.
    pose proof(Rabs_pos(B h*bpow radix2 960));
      assert(P : 0<bpow radix2 (-480)<=1)by(split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]);nra. }
  destruct(normal_log_tail_up_one h Fh H Middle)as[Fm Mid].
  assert(Lower : bpow radix2 (-900)<=Rabs(B(fmul h (erfcx_pow2 480)))).
  { rewrite Mid,Rabs_mult,(Rabs_pos_eq(bpow radix2 480))by apply bpow_ge_0.
    assert(P : 1<=bpow radix2 480)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
    pose proof(Rabs_pos(B h));nra. }
  assert(End : B(fmul h (erfcx_pow2 480))*bpow radix2 480=B h*bpow radix2 960).
  { rewrite Mid,Rmult_assoc,<-bpow_plus;reflexivity. }
  destruct(normal_log_tail_up_one _ Fm Lower ltac:(rewrite End;exact LimitFull))as[Fv V].
  unfold normal_log_tail_up64;split;[exact Fv|rewrite V,End;exact Full].
Qed.
