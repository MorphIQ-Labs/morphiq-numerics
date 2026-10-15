(** Final rounding of an expansion scaled up by 2^600. Both branches
    use the same error budget; the lower branch includes rounding to zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingTest.
Require Import StageGappa ErfcxDecision NormalUnderflowCandidate NormalComparisons NormalFiniteScale.
Open Scope R_scope.

Definition normal_finite_normal64 h l :=
  match decide_with h l (erfcx_pow2(-65))with
  | Some v=>Some(fmul v (erfcx_pow2(-600))) | None=>None end.

Theorem normal_finite_normal_ieee h l z v : finite h -> finite l ->
  3*bpow radix2(-423)<=B h<=4 ->
  Rabs(B l)<=5*bpow radix2(-54)*B h -> B h=rndF(B h+B l) ->
  Rabs(z-(B h+B l))<=3*bpow radix2(-67)*B h ->
  normal_finite_normal64 h l=Some v -> finite v /\ B v=rndF(z*bpow radix2(-600)).
Proof.
  intros Fh Fl H L Norm Error.
  assert(Hpos : 0<B h)by(pose proof(bpow_gt_0 radix2(-423));lra).
  assert(Z : bpow radix2(-422)<=z<=5).
  { apply Rabs_le_inv in L,Error;bpow_num_all;split;nra. }
  assert(Relative : Rabs(z-(B h+B l))<=7*bpow radix2(-68)*Rabs z).
  { rewrite(Rabs_pos_eq z)by(pose proof(bpow_gt_0 radix2(-422));lra).
    apply Rle_trans with(3*bpow radix2(-67)*B h);[exact Error|].
    apply Rabs_le_inv in L,Error;bpow_num_all;nra. }
  destruct(erfcx_pow2_ok(-65)ltac:(lia))as[Fe E].
  unfold normal_finite_normal64;destruct(decide_with h l (erfcx_pow2(-65)))as[r|]eqn:Decision;[|discriminate].
  intros V;injection V as <-.
  destruct(decide_with_ok h l (erfcx_pow2(-65))z (7*bpow radix2(-68)) r Fh Fl Fe
    ltac:(rewrite Rabs_pos_eq by lra;bpow_num_all;split;lra)Norm)as[Same Round].
  - split;bpow_num;field_simplify;lra.
  - rewrite E;split;bpow_num;field_simplify;lra.
  - exact Relative.
  - exact Decision.
  - subst r.
    assert(Mh : (-421<=mag radix2(B h))%Z).
    { apply mag_ge_bpow;change(bpow radix2(-422)<=Rabs(B h));rewrite Rabs_pos_eq by lra;bpow_num_all;lra. }
    assert(Mz : (-421<=mag radix2 z)%Z).
    { apply mag_ge_bpow;change(bpow radix2(-422)<=Rabs z);rewrite Rabs_pos_eq;[exact(proj1 Z)|pose proof(bpow_gt_0 radix2(-422));lra]. }
    destruct(erfcx_pow2_ok(-600)ltac:(lia))as[Fs S].
    destruct(fmul_exact h (erfcx_pow2(-600)) Fh Fs)as[Fv Value].
    + rewrite S;apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia].
    + rewrite S,Rabs_mult,(Rabs_pos_eq(B h)),(Rabs_pos_eq(bpow radix2(-600)))by lra||apply bpow_ge_0.
      apply Rle_lt_trans with(4*bpow radix2(-600));[apply Rmult_le_compat_r;[apply bpow_ge_0|lra]|].
      change 4 with(bpow radix2 2);rewrite <-bpow_plus;apply bpow_lt;lia.
    + split;[exact Fv|].
      rewrite Value,S,<-Round,round_scale by(pose proof(bpow_gt_0 radix2(-422));lra)||lia.
      reflexivity.
Qed.

Definition normal_finite_split : f64 := b64_of_bits 2708915175863353344.
Lemma normal_finite_split_ok : finite normal_finite_split /\ B normal_finite_split=3*bpow radix2(-423).
Proof.
  split;[exact(bits_finite 2708915175863353344 false 6755399441055744 (-474)eq_refl)|].
  pose proof(bits_val 2708915175863353344 false 6755399441055744 474 eq_refl)as V.
  unfold normal_finite_split;rewrite V;bpow_num;simpl;field.
Qed.

Definition normal_finite_grid64 h l :=
  if normal_le normal_finite_split h then normal_finite_normal64 h l
  else normal_underflow_fast64 h l.

Theorem normal_finite_grid_ieee h l z v : finite h -> finite l ->
  0<=B h<=4 -> Rabs(B l)<=5*bpow radix2(-54)*B h -> B h=rndF(B h+B l) ->
  Rabs(z-(B h+B l))<=3*bpow radix2(-67)*B h ->
  normal_finite_grid64 h l=Some v -> finite v /\ B v=rndF(z*bpow radix2(-600)).
Proof.
  intros Fh Fl H L Norm Error Decision.
  destruct normal_finite_split_ok as[Fs Split].
  unfold normal_finite_grid64 in Decision;destruct(normal_le normal_finite_split h)eqn:Branch.
  - apply normal_le_true in Branch;try assumption;rewrite Split in Branch.
    apply(normal_finite_normal_ieee h l z v);assumption||lra.
  - apply normal_le_false in Branch;try assumption;rewrite Split in Branch.
    apply(normal_underflow_fast_ieee h l z v);try assumption.
    + split;lra.
    + bpow_num_all;nra.
Qed.

Definition normal_finite_scaled_fast64 h l k :=
  let '(a,b):=normal_finite_scaled64 h l k in normal_finite_grid64 a b.

Theorem normal_finite_scaled_fast_ieee h l k z v : finite h -> finite l ->
  bpow radix2(-10)<=B h<=4 -> Rabs(B l)<=bpow radix2(-51)*B h ->
  B h=rndF(B h+B l) -> (-501<=k<=0)%Z ->
  Rabs(z-(B h+B l))<=11*bpow radix2(-69)*B h ->
  normal_finite_scaled_fast64 h l k=Some v ->
  finite v /\ B v=rndF(z*bpow radix2(k-600)).
Proof.
  intros Fh Fl H L Norm K Error Decision.
  pose proof(normal_finite_normalized_low _ _ H L Norm)as Low.
  pose proof(normal_finite_scaled_ieee h l k z Fh Fl H Low K Error)as Scaled.
  pose proof(normal_finite_scaled_normalized h l k Fh Fl H Low Norm K)as Normalized.
  unfold normal_finite_scaled_fast64 in Decision;destruct(normal_finite_scaled64 h l k)as[a b].
  destruct Scaled as[Fa [Fb [A [Range [Lower Approx]]]]].
  assert(High : 0<=B a<=4).
  { assert(Power : 0<bpow radix2 k<=1)by(split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]).
    rewrite A;pose proof(bpow_gt_0 radix2(-10));split;nra. }
  destruct(normal_finite_grid_ieee a b (z*bpow radix2 k)v Fa Fb High Lower Normalized Approx Decision)as[Fv Value].
  split;[exact Fv|rewrite Value,Rmult_assoc,<-bpow_plus;replace(k+ -600)%Z with(k-600)%Z by ring;reflexivity].
Qed.
