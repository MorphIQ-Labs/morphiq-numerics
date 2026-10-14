(** Final underflow-grid rounding of the scaled large-input erfcx kernel.
    The analytic omitted-correction contract is explicit. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxConstants ErfcxQuotientScale ErfcxTailValue.
Require Import ErfcxSubnormalCandidate ErfcxSubnormalValue.
Open Scope R_scope.

Lemma subnormal_error_from_relative h l z : bpow radix2 (-426)<=h ->
  Rabs l<=bpow radix2 (-473) -> 0<z ->
  - /2^68 <= ((h+l)-z)/z <= /2^68 ->
  Rabs (z-(h+l))<=bpow radix2 (-67)*h.
Proof.
  intros H L Z E.
  assert (Id : h+l=(1+((h+l)-z)/z)*z) by (field; lra).
  assert (Lr := Rabs_le_inv _ _ L).
  assert (Err : - /2^68*z <= (h+l)-z <= /2^68*z).
  { set (e := ((h+l)-z)/z) in *. clear - E Z Id. nra. }
  assert (Zb : z<=2*h).
  { clear - H Lr Err Z. bpow_num_all. nra. }
  apply Rabs_le. bpow_num_all. nra.
Qed.

Definition tail_subnormal_fast64 x :=
  let '(h,l) := scaled_quotient64 x in subnormal_fast64 h l.

Theorem tail_subnormal_fast_ieee x correction v : finite x -> bpow radix2 1021<=B x ->
  0<=correction<=bpow radix2 (-1794) ->
  tail_subnormal_fast64 x=Some v ->
  finite v /\ B v=rndF ((inv_sqrt_pi/B x)*(1-correction)).
Proof.
  intros Fx X Corr.
  assert (Large : bpow radix2 896<=B x).
  { apply Rle_trans with (bpow radix2 1021); [apply bpow_le; lia | exact X]. }
  pose proof (scaled_tail_with_pi_ieee x correction Fx Large Corr) as T.
  pose proof (subnormal_value_words_ieee x Fx X) as W.
  unfold tail_subnormal_fast64. destruct (scaled_quotient64 x) as [h l].
  destruct T as (_ & _ & Error). destruct W as (Fh & Fl & Norm & H & L).
  set (f := (inv_sqrt_pi/B x)*(1-correction)) in *.
  assert (Fpos : 0<f).
  { unfold f. apply Rmult_lt_0_compat.
    - apply Rdiv_lt_0_compat; [apply inv_sqrt_pi_positive | pose proof (bpow_gt_0 radix2 1021); lra].
    - assert (bpow radix2 (-1794)<=/2) by (change (/2) with (bpow radix2 (-1)); apply bpow_le; lia). lra. }
  assert (Zpos : 0<f*bpow radix2 600) by (apply Rmult_lt_0_compat; [exact Fpos | apply bpow_gt_0]).
  assert (Id : ((B h+B l)-f*bpow radix2 600)/(f*bpow radix2 600)=
    ((B h+B l)*bpow radix2 (-600)-f)/f).
  { replace (bpow radix2 (-600)) with (/bpow radix2 600) by (rewrite <- bpow_opp; reflexivity).
    field. pose proof (bpow_gt_0 radix2 600). split; lra. }
  rewrite <- Id in Error.
  pose proof (subnormal_error_from_relative (B h) (B l) (f*bpow radix2 600)
    (proj1 H) L Zpos Error) as Absolute.
  intros Decision. destruct (subnormal_fast_ieee h l (f*bpow radix2 600) v
    Fh Fl H L Absolute Decision) as [Fv V].
  rewrite Rmult_assoc, <- bpow_plus in V. change (bpow radix2 (600 + -600)) with 1 in V.
  rewrite Rmult_1_r in V. split; assumption.
Qed.
