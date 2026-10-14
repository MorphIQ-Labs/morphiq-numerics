(** Integer checks of the proved accurate tail at saturation endpoints.
    The check leaves a 2^-60 relative margin, larger than the proved 2^-115
    evaluation error. No reference value is assumed. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import QSpec Q256 Q256Real Limbs.
From Binary64 Require Import IEEE64.
Require Import StageGappa NormalAccurateTailFull NormalTailAnalytic.
Open Scope R_scope.

Definition normal_tail_threshold_check (n : Z) (below : bool) q :=
  negb(neg q) && (e q <=? -n-60)%Z &&
  (if below then
    (v(m q) <? (2^60-1)*2^(-n-60-e q))%Z
   else ((2^60+1)*2^(-n-60-e q) <? v(m q))%Z).

Lemma normal_tail_check_scale n exponent delta : (exponent<= -n-60)%Z ->
  IZR((2^60+delta)*2^(-n-60-exponent))*bpow radix2 exponent =
  bpow radix2 (-n)*(1+IZR delta*bpow radix2 (-60)).
Proof.
  intros E;rewrite mult_IZR,plus_IZR,!IZR_pow2 by lia.
  rewrite Rmult_assoc,<-bpow_plus.
  replace(-n-60-exponent+exponent)%Z with(-n-60)%Z by ring.
  replace(-n-60)%Z with(-n+ -60)%Z by ring;rewrite bpow_plus.
  assert(Unit : bpow radix2 60*bpow radix2 (-60)=1)by(rewrite <-bpow_plus;reflexivity).
  replace((bpow radix2 60+IZR delta)*(bpow radix2 (-n)*bpow radix2 (-60)))with
    (bpow radix2 (-n)*(bpow radix2 60*bpow radix2 (-60)+IZR delta*bpow radix2 (-60)))by ring.
  rewrite Unit;reflexivity.
Qed.

Theorem normal_tail_threshold_check_sound n below q :
  normal_tail_threshold_check n below q=true ->
  if below then qval q < bpow radix2 (-n)*(1-bpow radix2 (-60))
  else bpow radix2 (-n)*(1+bpow radix2 (-60)) < qval q.
Proof.
  unfold normal_tail_threshold_check;rewrite !andb_true_iff.
  intros [[Sign Exponent] Check];apply negb_true_iff in Sign;apply Z.leb_le in Exponent.
  unfold qval,QSpec.val,F2R;cbn[Fnum Fexp];rewrite Sign.
  destruct below.
  - apply Z.ltb_lt in Check.
    pose proof(IZR_lt _ _ Check)as Bound.
    apply(Rmult_lt_compat_r (bpow radix2 (e q)))in Bound;[|apply bpow_gt_0].
    replace(2^60-1)%Z with(2^60+ -1)%Z in Bound by ring.
    rewrite(normal_tail_check_scale n (e q)(-1)Exponent)in Bound;cbn[IZR]in Bound;lra.
  - apply Z.ltb_lt in Check.
    pose proof(IZR_lt _ _ Check)as Bound.
    apply(Rmult_lt_compat_r (bpow radix2 (e q)))in Bound;[|apply bpow_gt_0].
    rewrite(normal_tail_check_scale n (e q)1 Exponent)in Bound;cbn[IZR]in Bound;lra.
Qed.

Theorem normal_tail_threshold_certified x n below : finite x -> /2<=B x<=38.6 ->
  normal_tail_threshold_check n below (normal_q_tail x)=true ->
  if below then normal_tail(B x)<bpow radix2 (-n)
  else bpow radix2 (-n)<normal_tail(B x).
Proof.
  intros F X Check;pose proof(normal_tail_threshold_check_sound n below _ Check)as Bound.
  destruct(normal_q_tail_error x F X)as[_ [error [Error Value]]].
  pose proof(normal_tail_range(B x)ltac:(lra))as Positive.
  pose proof(bpow_gt_0 radix2 (-n))as P;apply Rabs_le_inv in Error;rewrite Value in Bound.
  assert(Margin : 0<bpow radix2 (-115) /\ bpow radix2 (-115)<bpow radix2 (-60) /\ bpow radix2 (-60)<1).
  { split;[apply bpow_gt_0|split;[apply bpow_lt;lia|interval with(i_prec 80)]]. }
  destruct below;[destruct(Rlt_dec (normal_tail(B x))(bpow radix2 (-n)))|destruct(Rlt_dec (bpow radix2 (-n))(normal_tail(B x)))];try assumption;exfalso;nra.
Qed.

Theorem normal_tail_threshold_margin x n below : finite x -> /2<=B x<=38.6 ->
  normal_tail_threshold_check n below (normal_q_tail x)=true ->
  if below then normal_tail(B x)<bpow radix2 (-n)*(1-bpow radix2 (-62))
  else bpow radix2 (-n)*(1+bpow radix2 (-62))<normal_tail(B x).
Proof.
  intros F X Check;pose proof(normal_tail_threshold_check_sound n below _ Check)as Bound.
  destruct(normal_q_tail_error x F X)as[_ [error [Error Value]]].
  pose proof(normal_tail_range(B x)ltac:(lra))as Positive.
  pose proof(bpow_gt_0 radix2 (-n))as P;apply Rabs_le_inv in Error;rewrite Value in Bound.
  destruct below.
  - destruct(Rlt_dec (normal_tail(B x))(bpow radix2 (-n)*(1-bpow radix2 (-62))));[assumption|].
    exfalso;bpow_num_all;nra.
  - destruct(Rlt_dec (bpow radix2 (-n)*(1+bpow radix2 (-62)))(normal_tail(B x)));[assumption|].
    exfalso;bpow_num_all;nra.
Qed.
