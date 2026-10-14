(** The final binary64 subnormal grid. These lemmas use its absolute spacing,
    independently of a candidate's relative ulp or normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Sterbenz Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul RoundingGaps RoundingTest RoundingConstant.
Require Import StageGappa.
Require Import ErfcxDecision.
Open Scope R_scope.

Lemma binary64_minimum_ulp x :
  bpow radix2 (-1074) <= ulp radix2 (FLT_exp emin prec) x.
Proof.
  destruct (Req_dec x 0) as [Zero | Nonzero].
  - subst x. rewrite ulp_FLT_small; [apply Rle_refl | exact _ | ].
    rewrite Rabs_R0. apply bpow_gt_0.
  - rewrite ulp_neq_0 by exact Nonzero. apply bpow_le.
    unfold cexp, FLT_exp, emin, prec. lia.
Qed.

Lemma binary64_round_absolute u z : fmtF u -> 0<u ->
  Rabs (z-u) < bpow radix2 (-1075) -> rndF z=u.
Proof.
  intros Fu U Close. apply (round_within u z (bpow radix2 (-1074)) Fu U).
  - apply binary64_minimum_ulp.
  - pose proof (pred_plus_ulp radix2 (FLT_exp emin prec) u U Fu) as Pred.
    pose proof (binary64_minimum_ulp (pred radix2 (FLT_exp emin prec) u)).
    change (bpow radix2 (-1074)<=u-pred radix2 (FLT_exp emin prec) u). lra.
  - replace (bpow radix2 (-1074)/2) with (bpow radix2 (-1075)); [exact Close | ].
    unfold Rdiv. change (/2) with (bpow radix2 (-1)). rewrite <- bpow_plus. reflexivity.
Qed.

Lemma subnormal_candidate_back_ieee c : finite c ->
  bpow radix2 (-1074) <= B c <= bpow radix2 (-1021) ->
  finite (fmul c (erfcx_pow2 600)) /\
  B (fmul c (erfcx_pow2 600)) = B c*bpow radix2 600 /\
  bpow radix2 (-474) <= B (fmul c (erfcx_pow2 600)) <= bpow radix2 (-421).
Proof.
  intros Fc C. destruct (erfcx_pow2_ok 600 ltac:(lia)) as [Fs Bs].
  assert (Positive : 0<B c) by (pose proof (bpow_gt_0 radix2 (-1074)); lra).
  assert (Fmt : fmtF (B c*bpow radix2 600)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (-1073 <= mag radix2 (B c))%Z).
    { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. exact (proj1 C). }
    unfold emin, prec. lia. }
  assert (Range : bpow radix2 (-474)<=B c*bpow radix2 600<=bpow radix2 (-421)).
  { replace (bpow radix2 (-474)) with (bpow radix2 (-1074)*bpow radix2 600)
      by (rewrite <- bpow_plus; reflexivity).
    replace (bpow radix2 (-421)) with (bpow radix2 (-1021)*bpow radix2 600)
      by (rewrite <- bpow_plus; reflexivity).
    split; apply Rmult_le_compat_r; try apply bpow_ge_0; lra. }
  destruct (fmul_exact c (erfcx_pow2 600) Fc Fs) as [Fy By].
  - rewrite Bs. exact Fmt.
  - rewrite Bs, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 600); nra).
    apply Rle_lt_trans with (bpow radix2 (-421)); [lra | apply bpow_lt; lia].
  - rewrite Bs in By. rewrite By. split; [exact Fy | split; [reflexivity | exact Range]].
Qed.

(** The two roundings in the guard consume less than half its 2^-66 budget.
    The final addition needs no extra budget: its threshold is representable. *)
Lemma subnormal_guard_real h l c z :
  bpow radix2 (-426) <= h <= bpow radix2 (-421) ->
  Rabs l <= bpow radix2 (-473) ->
  Rabs (h-c*bpow radix2 600) <= bpow radix2 (-473) ->
  Rabs (z-(h+l)) <= bpow radix2 (-67)*h ->
  rndF (Rabs (rndF ((h-c*bpow radix2 600)+l)) +
    rndF (bpow radix2 (-66)*h)) < bpow radix2 (-475) ->
  Rabs (z*bpow radix2 (-600)-c) < bpow radix2 (-1075).
Proof.
  intros H L C E Guard.
  assert (Sum : Rabs ((h-c*bpow radix2 600)+l) <= bpow radix2 (-472)).
  { eapply Rle_trans; [apply Rabs_triang | ]. bpow_num_all. lra. }
  pose proof (rnd_err_below _ (-472) ltac:(lia) Sum) as Round.
  assert (Product : Rabs (bpow radix2 (-66)*h) <= bpow radix2 (-487)).
  { rewrite Rabs_mult, !Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-426));
      pose proof (bpow_gt_0 radix2 (-66)); lra).
    replace (bpow radix2 (-487)) with (bpow radix2 (-66)*bpow radix2 (-421))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
  pose proof (rnd_err_below _ (-487) ltac:(lia) Product) as Margin.
  change (-487-54)%Z with (-541)%Z in Margin.
  assert (Exact : Rabs (rndF ((h-c*bpow radix2 600)+l)) +
    rndF (bpow radix2 (-66)*h) < bpow radix2 (-475)).
  { apply Rnot_le_lt. intros Contra.
    assert (Mono := round_le radix2 (FLT_exp emin prec) ZnearestE _ _ Contra).
    assert (Half : rndF (bpow radix2 (-475)) = bpow radix2 (-475)).
    { apply round_generic; [exact _ | ].
      apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
    change (rndF (bpow radix2 (-475)) <= rndF
      (Rabs (rndF ((h-c*bpow radix2 600)+l)) + rndF (bpow radix2 (-66)*h))) in Mono.
    rewrite Half in Mono. lra. }
  assert (Budget : bpow radix2 (-67)*h + bpow radix2 (-526) <=
      rndF (bpow radix2 (-66)*h)).
  { pose proof (Rabs_le_inv _ _ Margin). bpow_num_all. lra. }
  assert (Raw : Rabs (z-c*bpow radix2 600) < bpow radix2 (-475)).
  { replace (z-c*bpow radix2 600) with
      ((z-(h+l))+(((h-c*bpow radix2 600)+l)-rndF ((h-c*bpow radix2 600)+l))+
       rndF ((h-c*bpow radix2 600)+l)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang | ].
    pose proof (Rabs_triang (z-(h+l))
      (((h-c*bpow radix2 600)+l)-rndF ((h-c*bpow radix2 600)+l))) as T.
    rewrite Rabs_minus_sym in Round. change (-472-54)%Z with (-526)%Z in Round. lra. }
  replace (z*bpow radix2 (-600)-c) with
    ((z-c*bpow radix2 600)*bpow radix2 (-600)).
  - rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-600))) by apply bpow_ge_0.
    replace (bpow radix2 (-1075)) with (bpow radix2 (-475)*bpow radix2 (-600))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Raw].
  - rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus.
    change (bpow radix2 (600 + -600)) with 1. ring.
Qed.

Definition subnormal_residual64 h l c :=
  fadd (fsub h (fmul c (erfcx_pow2 600))) l.

Lemma subnormal_residual_ieee h l c : finite h -> finite l -> finite c ->
  bpow radix2 (-426) <= B h <= bpow radix2 (-421) ->
  Rabs (B l) <= bpow radix2 (-473) ->
  bpow radix2 (-1074) <= B c <= bpow radix2 (-1021) ->
  Rabs (B h-B c*bpow radix2 600) <= bpow radix2 (-473) ->
  finite (subnormal_residual64 h l c) /\
  B (subnormal_residual64 h l c) = rndF ((B h-B c*bpow radix2 600)+B l) /\
  Rabs (B (subnormal_residual64 h l c)) <= bpow radix2 (-472).
Proof.
  intros Fh Fl Fc H L C Close.
  destruct (subnormal_candidate_back_ieee c Fc C) as (Fb & Back & Bounds).
  assert (Fmt : fmtF (B h-B (fmul c (erfcx_pow2 600)))).
  { apply sterbenz; try exact _. all: try apply B_fmt.
    rewrite Back. pose proof (Rabs_le_inv _ _ Close). bpow_num_all. lra. }
  destruct (fsub_ok 1 (-473) h (fmul c (erfcx_pow2 600)) Fh Fb
    ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite Rmult_1_l, Back; exact Close)) as [Fd D].
  rewrite round_generic in D by (exact _ || exact Fmt).
  assert (Sum : bnd 1 (-472) (B (fsub h (fmul c (erfcx_pow2 600)))+B l)).
  { unfold bnd. rewrite Rmult_1_l, D, Back.
    eapply Rle_trans; [apply Rabs_triang | ]. bpow_num_all. lra. }
  destruct (fadd_bnd 1 (-472) (fsub h (fmul c (erfcx_pow2 600))) l Fd Fl
    ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Sum) as (Fr & R & Bound).
  rewrite D, Back in R. unfold bnd in Bound. rewrite Rmult_1_l in Bound.
  split; [exact Fr | split; assumption].
Qed.

(** This is the actual final test, after selection of either adjacent candidate.
    Its safety theorem does not depend on which candidate was tried first. *)
Definition subnormal_accept64 h l c : option f64 :=
  match Bcompare 53 1024
    (fadd (b64_abs (subnormal_residual64 h l c)) (fmul erfcx_eps h))
    (erfcx_pow2 (-475)) with
  | Some Lt => Some c
  | _ => None
  end.

Local Opaque subnormal_residual64 fadd fmul erfcx_pow2 erfcx_eps.

Theorem subnormal_accept_ieee h l c z v : finite h -> finite l -> finite c ->
  bpow radix2 (-426) <= B h <= bpow radix2 (-421) ->
  Rabs (B l) <= bpow radix2 (-473) ->
  bpow radix2 (-1074) <= B c <= bpow radix2 (-1021) ->
  Rabs (B h-B c*bpow radix2 600) <= bpow radix2 (-473) ->
  Rabs (z-(B h+B l)) <= bpow radix2 (-67)*B h ->
  subnormal_accept64 h l c = Some v ->
  v=c /\ finite v /\ B v=rndF (z*bpow radix2 (-600)).
Proof.
  intros Fh Fl Fc H L C Close Error Decision.
  destruct (subnormal_residual_ieee h l c Fh Fl Fc H L C Close) as (Fr & R & Rbound).
  destruct erfcx_eps_ok as [Fe Eps].
  destruct (erfcx_pow2_ok (-475) ltac:(lia)) as [Fhalf Half].
  assert (Product : bnd 1 (-487) (B erfcx_eps*B h)).
  { unfold bnd. rewrite Rmult_1_l, Eps, Rabs_mult, !Rabs_pos_eq
      by (pose proof (bpow_gt_0 radix2 (-426)); pose proof (bpow_gt_0 radix2 (-66)); lra).
    replace (bpow radix2 (-487)) with (bpow radix2 (-66)*bpow radix2 (-421))
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
  destruct (fmul_bnd 1 (-487) erfcx_eps h Fe Fh ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia) Product) as (Fp & P & Pb).
  assert (Fa : finite (b64_abs (subnormal_residual64 h l c))).
  { assert (Abs : forall r, finite r -> finite (b64_abs r)).
    { intros r F. destruct r; exact F. }
    exact (Abs _ Fr). }
  assert (Sum : bnd 2 (-472)
    (B (b64_abs (subnormal_residual64 h l c))+B (fmul erfcx_eps h))).
  { replace 2%Z with (1+1)%Z by reflexivity. apply bnd_plus.
    - unfold bnd. rewrite B_abs, Rabs_Rabsolu, Rmult_1_l. exact Rbound.
    - apply (bnd_up 1 (-487)); [lia | lia | exact Pb]. }
  destruct (fadd_ok 2 (-472) (b64_abs (subnormal_residual64 h l c)) (fmul erfcx_eps h)
    Fa Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Sum) as [Fs S].
  unfold subnormal_accept64 in Decision.
  destruct (Bcompare 53 1024 _ _) as [[ | | ] | ] eqn:Cmp; try discriminate.
  injection Decision as <-. split; [reflexivity | split; [exact Fc | ]].
  rewrite Bcompare_correct in Cmp by assumption. injection Cmp as Cmp.
  apply Rcompare_Lt_inv in Cmp. rewrite S, Half, B_abs, R, P, Eps in Cmp.
  symmetry. apply binary64_round_absolute; [apply B_fmt | | ].
  - pose proof (bpow_gt_0 radix2 (-1074)). lra.
  - exact (subnormal_guard_real (B h) (B l) (B c) z H L Close Error Cmp).
Qed.
