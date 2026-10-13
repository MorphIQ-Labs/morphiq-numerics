(** Final normal-output scaling in the positive erfcx tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxConstants ErfcxQuotientScale ErfcxTailValue.
Require Import ErfcxDecision ErfcxScaledWords ErfcxSubnormalBoundary ErfcxSubnormalFast.
Open Scope R_scope.

Definition tail_scaled_normal_fast64 x :=
  let '(h,l) := scaled_quotient64 x in
  match erfcx_decide64 h l with
  | Some v => Some (fmul v (erfcx_pow2 (-600)))
  | None => None
  end.

Theorem tail_scaled_normal_fast_ieee x correction v : finite x -> bpow radix2 896<=B x ->
  B x<B erfcx_subnormal_limit -> 0<=correction<=bpow radix2 (-1794) ->
  tail_scaled_normal_fast64 x=Some v ->
  finite v /\ B v=rndF ((inv_sqrt_pi/B x)*(1-correction)).
Proof.
  intros Fx X Below Corr.
  pose proof (scaled_tail_with_pi_ieee x correction Fx X Corr) as T.
  pose proof (scaled_quotient_words_ieee x Fx X) as W.
  unfold tail_scaled_normal_fast64. destruct (scaled_quotient64 x) as [h l].
  destruct T as (_ & _ & Error). destruct W as (Fh & Fl & Norm & H).
  assert (Xpos : 0<B x) by (pose proof (bpow_gt_0 radix2 896); lra).
  pose proof (erfcx_normal_tail_lower x correction Fx Xpos Below Corr) as Lower.
  set (f := (inv_sqrt_pi/B x)*(1-correction)) in *.
  assert (Fpos : 0<f) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  assert (Zpos : 0<f*bpow radix2 600) by (apply Rmult_lt_0_compat; [exact Fpos | apply bpow_gt_0]).
  assert (Id : ((B h+B l)-f*bpow radix2 600)/(f*bpow radix2 600)=
    ((B h+B l)*bpow radix2 (-600)-f)/f).
  { replace (bpow radix2 (-600)) with (/bpow radix2 600) by (rewrite <- bpow_opp; reflexivity).
    field. pose proof (bpow_gt_0 radix2 600). split; lra. }
  rewrite <- Id in Error.
  set (z := f*bpow radix2 600) in *.
  assert (Absolute : Rabs (z-(B h+B l))<=bpow radix2 (-67)*Rabs z).
  { assert (Identity : B h+B l-z=(((B h+B l)-z)/z)*z) by (field; lra).
    set (err := ((B h+B l)-z)/z) in *.
    rewrite (Rabs_pos_eq z) by lra. apply Rabs_le. clear - Error Identity Zpos.
    bpow_num_all. nra. }
  assert (Hb : bpow radix2 (-900)<=Rabs (B h)<=bpow radix2 1000).
  { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-426)); lra). split.
    - apply Rle_trans with (bpow radix2 (-426)); [apply bpow_le; lia | lra].
    - apply Rle_trans with (bpow radix2 (-295)); [lra | apply bpow_le; lia]. }
  destruct (erfcx_decide64 h l) as [r | ] eqn:Decision; [ | discriminate].
  intros Output. injection Output as <-.
  destruct (erfcx_decide_ieee h l z r Fh Fl Hb Norm Absolute Decision) as [R Round]. subst r.
  assert (Zlower : bpow radix2 (-422)<=z).
  { unfold z. replace (bpow radix2 (-422)) with (bpow radix2 (-1022)*bpow radix2 600)
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Lower]. }
  assert (Hlower : bpow radix2 (-422)<=B h).
  { rewrite Round. apply round_ge_generic; [exact _ | exact _ | | exact Zlower].
    apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
  assert (Mh : (-421<=mag radix2 (B h))%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq; [exact Hlower | pose proof (bpow_gt_0 radix2 (-422)); lra]. }
  assert (Mz : (-421<=mag radix2 z)%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. exact Zlower. }
  destruct (erfcx_pow2_ok (-600) ltac:(lia)) as [Fk K].
  destruct (fmul_exact h (erfcx_pow2 (-600)) Fh Fk) as [Fv V].
  - rewrite K. apply mult_bpow_exact_FLT; [apply B_fmt | unfold emin, prec; lia].
  - rewrite K, Rabs_mult, !Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-422));
      pose proof (bpow_gt_0 radix2 (-600)); lra).
    apply Rle_lt_trans with (bpow radix2 (-895)).
    + replace (bpow radix2 (-895)) with (bpow radix2 (-295)*bpow radix2 (-600))
        by (rewrite <- bpow_plus; reflexivity).
      apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
    + apply bpow_lt; lia.
  - split; [exact Fv | ]. rewrite V,K,Round.
    rewrite <- (round_scale z (-600) ltac:(lra) ltac:(lia) ltac:(lia)).
    unfold z. rewrite Rmult_assoc, <- bpow_plus. change (bpow radix2 (600 + -600)) with 1.
    rewrite Rmult_1_r. reflexivity.
Qed.

Definition tail_scaled_fast64 x :=
  match Bcompare 53 1024 x erfcx_subnormal_limit with
  | Some Lt => tail_scaled_normal_fast64 x
  | _ => tail_subnormal_fast64 x
  end.

Local Opaque erfcx_subnormal_limit tail_scaled_normal_fast64 tail_subnormal_fast64.

Theorem tail_scaled_fast_ieee x correction v : finite x -> bpow radix2 896<=B x ->
  0<=correction<=bpow radix2 (-1794) -> tail_scaled_fast64 x=Some v ->
  finite v /\ B v=rndF ((inv_sqrt_pi/B x)*(1-correction)).
Proof.
  intros Fx X Corr Decision. destruct erfcx_subnormal_limit_ok as (Ft & T & Lower).
  unfold tail_scaled_fast64 in Decision.
  rewrite Bcompare_correct in Decision by assumption.
  destruct (Rcompare (B x) (B erfcx_subnormal_limit)) eqn:Cmp.
  - apply Rcompare_Eq_inv in Cmp. apply (tail_subnormal_fast_ieee x correction v Fx); try assumption. lra.
  - apply Rcompare_Lt_inv in Cmp. exact (tail_scaled_normal_fast_ieee x correction v Fx X Cmp Corr Decision).
  - apply Rcompare_Gt_inv in Cmp. apply (tail_subnormal_fast_ieee x correction v Fx); try assumption. lra.
Qed.
