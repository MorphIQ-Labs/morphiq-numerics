(** Normalization and binary spacing of the four double-word coefficients
    used in the lower-degree centered-CDF Horner stages. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa NormalCenterFastConstants NormalCenterFastTail.
Open Scope R_scope.

Lemma normal_center_tail_grid z : finite z -> Rabs(B z)<=/4 ->
  binary_grid (-67)(B(normal_center_tail64 z 8)).
Proof.
  intros Fz Z;pose proof(normal_center_tail_positive z Fz Z)as Range.
  apply(binary_grid_binary64 _ (-15));rewrite Rabs_pos_eq;
    [exact(proj1 Range)|pose proof(bpow_gt_0 radix2 (-15));lra].
Qed.

Lemma normal_center_low_coefficient_data n : (n<4)%nat ->
  let '(h,l):=normal_center_fast_word n in
  finite h /\ finite l /\ Rabs(B h)<=1 /\ Rabs(B l)<=bpow radix2 (-54) /\
  binary_grid (-116)(B h) /\ binary_grid (-116)(B l) /\
  bpow radix2 (-10)<=Rabs(B h+B l)<=2.
Proof.
  intros N;unfold normal_center_fast_word,normal_center_fast_words.
  destruct n as[|n].
  - cbn [List.nth];destruct normal_center_0_hi_ok as[Fh H],normal_center_0_lo_ok as[Fl L].
    assert(Gh : binary_grid (-116)(B normal_center_0_hi)).
    { apply(binary_grid_binary64 _ (-64));rewrite H;bpow_num;interval with(i_prec 160). }
    assert(Gl : binary_grid (-116)(B normal_center_0_lo)).
    { rewrite L;replace(0/1)with 0 by field;apply binary_grid_zero. }
    repeat split;try assumption;rewrite ?H,?L;bpow_num;interval with(i_prec 160).
  destruct n as[|n].
  - cbn [List.nth];destruct normal_center_1_hi_ok as[Fh H],normal_center_1_lo_ok as[Fl L].
    assert(Gh : binary_grid (-116)(B normal_center_1_hi)).
    { apply(binary_grid_binary64 _ (-64));rewrite H;bpow_num;interval with(i_prec 160). }
    assert(Gl : binary_grid (-116)(B normal_center_1_lo)).
    { apply(binary_grid_binary64 _ (-64));rewrite L;bpow_num;interval with(i_prec 160). }
    repeat split;try assumption;rewrite ?H,?L;bpow_num;interval with(i_prec 160).
  destruct n as[|n].
  - cbn [List.nth];destruct normal_center_2_hi_ok as[Fh H],normal_center_2_lo_ok as[Fl L].
    assert(Gh : binary_grid (-116)(B normal_center_2_hi)).
    { apply(binary_grid_binary64 _ (-64));rewrite H;bpow_num;interval with(i_prec 160). }
    assert(Gl : binary_grid (-116)(B normal_center_2_lo)).
    { apply(binary_grid_binary64 _ (-64));rewrite L;bpow_num;interval with(i_prec 160). }
    repeat split;try assumption;rewrite ?H,?L;bpow_num;interval with(i_prec 160).
  destruct n as[|n].
  - cbn [List.nth];destruct normal_center_3_hi_ok as[Fh H],normal_center_3_lo_ok as[Fl L].
    assert(Gh : binary_grid (-116)(B normal_center_3_hi)).
    { apply(binary_grid_binary64 _ (-64));rewrite H;bpow_num;interval with(i_prec 160). }
    assert(Gl : binary_grid (-116)(B normal_center_3_lo)).
    { apply(binary_grid_binary64 _ (-64));rewrite L;bpow_num;interval with(i_prec 160). }
    repeat split;try assumption;rewrite ?H,?L;bpow_num;interval with(i_prec 160).
  lia.
Qed.

Definition normal_center_coefficient64 n :=
  let '(h,l):=normal_center_fast_word n in two_sum64 h l.

Theorem normal_center_coefficient_ieee n : (n<4)%nat ->
  let '(h,l):=normal_center_coefficient64 n in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-10)<=Rabs(B h)<=2 /\ Rabs(B l)<=bpow radix2 (-53) /\
  binary_grid (-116)(B h) /\ binary_grid (-116)(B l) /\
  Rabs((B h+B l)-normal_fast_center_coefficient n)<=bpow radix2 (-105).
Proof.
  intros N;pose proof(normal_center_low_coefficient_data n N)as Data.
  pose proof(normal_center_fast_words_ok n ltac:(lia))as Coefficient.
  unfold normal_center_coefficient64;destruct(normal_center_fast_word n)as[a b].
  destruct Data as[Fa [Fb [A [Bl [Ga [Gb Range]]]]]];destruct Coefficient as[_ [_ Error]].
  pose proof(two_sum_ieee a b Fa Fb
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)]))as Sum.
  destruct(two_sum64 a b)as[h l];destruct Sum as[Fh [Fl [High Total]]].
  assert(Gsum : binary_grid (-116)(B a+B b))by(apply binary_grid_add;assumption).
  assert(Gh : binary_grid (-116)(B h))by(rewrite High;apply binary_grid_round;exact Gsum).
  assert(Gl : binary_grid (-116)(B l)).
  { replace(B l)with(B a+B b-B h)by lra;apply binary_grid_sub;assumption. }
  assert(Hrange : bpow radix2 (-10)<=Rabs(B h)<=2).
  { rewrite High;split.
    - apply abs_round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 2 with(bpow radix2 1);apply normal_center_round_bound;[exact(proj2 Range)|lia]. }
  pose proof(rnd_err_below(B a+B b)1 ltac:(lia)(proj2 Range))as Rounded.
  rewrite <-High in Rounded;change(1-54)%Z with(-53)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-53)).
  { replace(B l)with(-(B h-(B a+B b)))by lra;rewrite Rabs_Ropp;exact Rounded. }
  repeat split;try tauto;rewrite Total;assumption.
Qed.
