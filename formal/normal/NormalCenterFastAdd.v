(** Add a generated coefficient to a perturbed Horner product. The exact
    stage's cancellation bound justifies the shared normalized IEEE adder. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Add IEEE64Grid.
Require Import StageGappa LnFastCompose NormalCenterFastConstants NormalCenterFastWords
  NormalCenterFastHorner NormalCenterFastState NormalCenterFastProduct.
Open Scope R_scope.

Definition normal_center_add_coefficient64 count ph pl :=
  let '(ch,cl):=normal_center_coefficient64 (3-count) in add64 ch cl ph pl.

Theorem normal_center_add_coefficient_ieee z t count e ph pl :
  0<=z<=/4 -> bpow radix2 (-15)<=t<=bpow radix2 (-10) -> (count<=3)%nat -> (e<= -116)%Z ->
  finite ph -> finite pl -> B ph=rndF(B ph+B pl) -> Rabs(B ph)<=2 -> Rabs(B pl)<=bpow radix2 (-53) ->
  binary_grid e (B ph) -> binary_grid e (B pl) ->
  Rabs((B ph+B pl)-z*normal_center_fast_previous z t count)<=bpow radix2 (-96) ->
  let '(h,l):=normal_center_add_coefficient64 count ph pl in
  normal_center_value h l (normal_center_fast_horner z t count)e.
Proof.
  intros Z T Count Exponent Fph Fpl Pnorm Ph Pl Gph Gpl ProductError.
  pose proof(normal_center_coefficient_ieee (3-count)ltac:(lia))as Coefficient.
  unfold normal_center_add_coefficient64;destruct(normal_center_coefficient64(3-count))as[ch cl].
  destruct Coefficient as[Fch [Fcl [Cnorm [Ch [Cl [Gch [Gcl CoefficientError]]]]]]].
  set(target:=normal_center_fast_horner z t count).
  set(c:=normal_fast_center_coefficient(3-count))in *.
  set(p:=z*normal_center_fast_previous z t count)in *.
  assert(Target : bpow radix2 (-10)<=Rabs target<=2)by(apply normal_center_fast_horner_range;assumption).
  assert(Identity : c+p=target)by(unfold c,p,target;rewrite normal_center_fast_horner_unfold;reflexivity).
  assert(SumError : Rabs((B ch+B cl+(B ph+B pl))-target)<=bpow radix2 (-105)+bpow radix2 (-96)).
  { rewrite <-Identity;replace(B ch+B cl+(B ph+B pl)-(c+p))with((B ch+B cl-c)+(B ph+B pl-p))by ring.
    eapply Rle_trans;[apply Rabs_triang|];lra. }
  assert(Cancellation : Rabs(B ch+B cl)+Rabs(B ph+B pl)<=4*Rabs(B ch+B cl+(B ph+B pl))).
  { assert(Budget : 0<=bpow radix2 (-85)<=/100)by(bpow_num;split;interval with(i_prec 160)).
    assert(ExactCancellation : Rabs c+Rabs p<=7/2*Rabs target).
    { pose proof(normal_center_fast_horner_cancellation z t count Z T Count)as Cancel.
      fold c p target in Cancel;pose proof(Rabs_pos target);lra. }
    assert(Perturbation : Rabs(B ch+B cl-c)+Rabs(B ph+B pl-p)<=bpow radix2 (-85)*Rabs target).
    { bpow_num_all;lra. }
    exact(proj1(lf_perturbed_sum (B ch+B cl)(B ph+B pl)c p target (bpow radix2 (-85))
      Identity Budget ExactCancellation Perturbation)). }
  pose proof(lf_add_pair ch cl ph pl Fch Fcl Fph Fpl Cnorm Pnorm
    (normal_center_word_bound ch 100 ltac:(lia)ltac:(lra))
    (normal_center_word_bound cl 100 ltac:(lia)ltac:(eapply Rle_trans;[exact Cl|interval with(i_prec 80)]))
    (normal_center_word_bound ph 100 ltac:(lia)ltac:(lra))
    (normal_center_word_bound pl 100 ltac:(lia)ltac:(eapply Rle_trans;[exact Pl|interval with(i_prec 80)]))
    Cancellation)as Sum.
  pose proof(add_grid_ieee e ch cl ph pl Fch Fcl Fph Fpl
    (normal_center_word_bound ch 100 ltac:(lia)ltac:(lra))
    (normal_center_word_bound cl 100 ltac:(lia)ltac:(eapply Rle_trans;[exact Cl|interval with(i_prec 80)]))
    (normal_center_word_bound ph 100 ltac:(lia)ltac:(lra))
    (normal_center_word_bound pl 100 ltac:(lia)ltac:(eapply Rle_trans;[exact Pl|interval with(i_prec 80)]))
    (binary_grid_finer e (-116)(B ch)Exponent Gch)(binary_grid_finer e (-116)(B cl)Exponent Gcl)Gph Gpl)as Grid.
  destruct(add64 ch cl ph pl)as[h l];destruct Sum as[Fh [Fl [Norm [r [R Value]]]]];destruct Grid as[_ Gl].
  apply(normal_center_value_of_error h l target e Fh Fl Norm Target);[|exact Gl].
  assert(Actual : Rabs(B ch+B cl+(B ph+B pl))<=3).
  { pose proof(Rabs_triang_inv (B ch+B cl+(B ph+B pl))target);bpow_num_all;lra. }
  rewrite Value;replace((B ch+B cl+(B ph+B pl))*(1+r)-target)with
    (((B ch+B cl+(B ph+B pl))-target)+(B ch+B cl+(B ph+B pl))*r)by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult.
  assert(RoundError : Rabs(B ch+B cl+(B ph+B pl))*Rabs r<=3*(776/2^114)).
  { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Actual|exact R]. }
  bpow_num_all;lra.
Qed.
