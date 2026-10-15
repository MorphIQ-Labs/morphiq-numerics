(** A common invariant for the four lower-degree Horner values: the
    approximation bound, normalization, magnitude, and low-word grid travel
    together into the next multiplication. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 RoundingConstant.
Require Import StageGappa NormalCenterFastWords NormalCenterFastTail NormalCenterFastConstants.
Open Scope R_scope.

Definition normal_center_value h l target e :=
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-11)<=Rabs(B h)<=4 /\ Rabs(B l)<=bpow radix2 (-52) /\
  binary_grid e (B l) /\ Rabs((B h+B l)-target)<=bpow radix2 (-95).

Lemma normal_center_value_of_error h l target e :
  finite h -> finite l -> B h=rndF(B h+B l) ->
  bpow radix2 (-10)<=Rabs target<=2 ->
  Rabs((B h+B l)-target)<=bpow radix2 (-95) -> binary_grid e (B l) ->
  normal_center_value h l target e.
Proof.
  intros Fh Fl Norm Target Error Grid.
  assert(SumRange : bpow radix2 (-11)<=Rabs(B h+B l)<=4).
  { pose proof(Rabs_triang_inv (B h+B l)target)as A.
    pose proof(Rabs_triang_inv target (B h+B l))as D;rewrite Rabs_minus_sym in D.
    bpow_num_all;split;lra. }
  assert(Hrange : bpow radix2 (-11)<=Rabs(B h)<=4).
  { rewrite Norm;split.
    - apply abs_round_ge_generic;[exact _|exact _| |exact(proj1 SumRange)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 4 with(bpow radix2 2);apply normal_center_round_bound;[exact(proj2 SumRange)|lia]. }
  pose proof(rnd_err_below(B h+B l)2 ltac:(lia)(proj2 SumRange))as Rounded.
  rewrite <-Norm in Rounded;change(2-54)%Z with(-52)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-52)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  unfold normal_center_value;tauto.
Qed.

Lemma normal_center_value_high_grid h l target e : normal_center_value h l target e ->
  binary_grid (-63)(B h).
Proof.
  intros[_ [_ [_ [High _]]]];apply(binary_grid_binary64 h (-11));exact(proj1 High).
Qed.

Theorem normal_center_coefficient_state n : (n<4)%nat ->
  let '(h,l):=normal_center_coefficient64 n in normal_center_value h l (normal_fast_center_coefficient n)(-116).
Proof.
  intros N;pose proof(normal_center_coefficient_ieee n N)as Coefficient.
  destruct(normal_center_coefficient64 n)as[h l].
  destruct Coefficient as[Fh [Fl [Norm [High [Low [_ [Grid Error]]]]]]].
  unfold normal_center_value;repeat split;try assumption;try tauto.
  - eapply Rle_trans;[|exact(proj1 High)];apply bpow_le;lia.
  - lra.
  - eapply Rle_trans;[exact Low|];apply bpow_le;lia.
  - eapply Rle_trans;[exact Error|];apply bpow_le;lia.
Qed.
