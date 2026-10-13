(** Candidate formation and adjacent-bit adjustment on the final grid. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxSubnormal ErfcxSubnormalBits.
Open Scope R_scope.

Definition subnormal_initial64 h := fmul h (erfcx_pow2 (-600)).
Definition subnormal_candidate64 h l :=
  let c := subnormal_initial64 h in
  let residual := subnormal_residual64 h l c in
  match Bcompare 53 1024 residual (erfcx_pow2 (-475)) with
  | Some Gt => b64_of_bits (bits_of_b64 c+1)
  | _ => match Bcompare 53 1024 residual (fneg (erfcx_pow2 (-475))) with
    | Some Lt => b64_of_bits (bits_of_b64 c-1)
    | _ => c
    end
  end.
Definition subnormal_fast64 h l := subnormal_accept64 h l (subnormal_candidate64 h l).

Lemma subnormal_initial_ieee h : finite h ->
  bpow radix2 (-426)<=B h<=3*bpow radix2 (-423) ->
  finite (subnormal_initial64 h) /\
  bpow radix2 (-1027)<=B (subnormal_initial64 h)<=7*bpow radix2 (-1024) /\
  Rabs (B (subnormal_initial64 h)-B h*bpow radix2 (-600))<=bpow radix2 (-1075).
Proof.
  intros Fh H. destruct (erfcx_pow2_ok (-600) ltac:(lia)) as [Fk K].
  assert (Range : bpow radix2 (-1026)<=B h*bpow radix2 (-600)<=3*bpow radix2 (-1023)).
  { replace (bpow radix2 (-1026)) with (bpow radix2 (-426)*bpow radix2 (-600))
      by (rewrite <- bpow_plus; reflexivity).
    replace (3*bpow radix2 (-1023)) with (3*bpow radix2 (-423)*bpow radix2 (-600))
      by (rewrite Rmult_assoc, <- bpow_plus; reflexivity).
    split; apply Rmult_le_compat_r; try apply bpow_ge_0; lra. }
  assert (Bound : bnd 3 (-1023) (B h*B (erfcx_pow2 (-600)))).
  { unfold bnd. rewrite K, Rabs_pos_eq; [lra | pose proof (bpow_gt_0 radix2 (-1026)); lra]. }
  destruct (fmul_ok 3 (-1023) h (erfcx_pow2 (-600)) Fh Fk
    ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bound) as [Fc C].
  fold (subnormal_initial64 h) in Fc, C. rewrite K in C.
  assert (Error : Rabs (B (subnormal_initial64 h)-B h*bpow radix2 (-600))<=bpow radix2 (-1075)).
  { rewrite C. eapply Rle_trans; [apply error_le_half_ulp; exact _ | ].
    rewrite ulp_FLT_small; [ | exact _ | ].
    - change (/2) with (bpow radix2 (-1)). rewrite <- bpow_plus. apply Rle_refl.
    - rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-1026)); lra).
      change (emin+prec)%Z with (-1021)%Z. bpow_num_all. lra. }
  split; [exact Fc | split; [ | exact Error]].
  pose proof (Rabs_le_inv _ _ Error). bpow_num_all. lra.
Qed.

Lemma subnormal_adjacent_ieee c d : finite c ->
  bpow radix2 (-1027)<=B c<=7*bpow radix2 (-1024) -> (-1<=d<=1)%Z ->
  finite (b64_of_bits (bits_of_b64 c+d)) /\
  bpow radix2 (-1074)<=B (b64_of_bits (bits_of_b64 c+d))<=bpow radix2 (-1021) /\
  Rabs (B (b64_of_bits (bits_of_b64 c+d))-B c)<=bpow radix2 (-1074).
Proof.
  intros Fc C D.
  destruct (small_positive_encoding c Fc ltac:(bpow_num_all; lra)) as [N V].
  assert (Bits : (0<bits_of_b64 c+d<2^53)%Z).
  { assert (Inner : (2<=bits_of_b64 c<=2^53-2)%Z).
    { change (2<=bits_of_b64 c<=9007199254740990)%Z.
      split; apply le_IZR; rewrite V in C; bpow_num_all; lra. } lia. }
  destruct (small_bits_value (bits_of_b64 c+d) Bits) as [Fv Val].
  split; [exact Fv | ]. rewrite Val, plus_IZR. split.
  - split.
    + pose proof (IZR_le 1 (bits_of_b64 c+d) ltac:(lia)) as Low.
      rewrite plus_IZR in Low.
      replace (bpow radix2 (-1074)) with (1*bpow radix2 (-1074)) at 1 by ring.
      apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Low].
    + assert (Upper : IZR (bits_of_b64 c)+IZR d<=IZR (2^53)).
      { rewrite <- plus_IZR. apply IZR_le. lia. }
      apply Rle_trans with (IZR (2^53)*bpow radix2 (-1074)).
      * apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Upper].
      * change (IZR (2^53)) with (bpow radix2 53). rewrite <- bpow_plus. apply Rle_refl.
  - rewrite V. replace ((IZR (bits_of_b64 c)+IZR d)*bpow radix2 (-1074)-
      IZR (bits_of_b64 c)*bpow radix2 (-1074)) with (IZR d*bpow radix2 (-1074)) by ring.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-1074))) by apply bpow_ge_0.
    replace (bpow radix2 (-1074)) with (1*bpow radix2 (-1074)) at 2 by ring.
    apply Rmult_le_compat_r; [apply bpow_ge_0 | apply Rabs_le].
    change (IZR (-1)<=IZR d<=IZR 1). split; apply IZR_le; lia.
Qed.


Local Opaque subnormal_initial64 subnormal_residual64 erfcx_pow2 fneg.

Theorem subnormal_candidate_ieee h l : finite h ->
  bpow radix2 (-426)<=B h<=3*bpow radix2 (-423) ->
  let c := subnormal_candidate64 h l in
  finite c /\ bpow radix2 (-1074)<=B c<=bpow radix2 (-1021) /\
  Rabs (B h-B c*bpow radix2 600)<=bpow radix2 (-473).
Proof.
  intros Fh H. destruct (subnormal_initial_ieee h Fh H) as (F0 & C0 & Error).
  assert (Step : forall c, finite c ->
    bpow radix2 (-1074)<=B c<=bpow radix2 (-1021) ->
    Rabs (B c-B (subnormal_initial64 h))<=bpow radix2 (-1074) ->
    finite c /\ bpow radix2 (-1074)<=B c<=bpow radix2 (-1021) /\
    Rabs (B h-B c*bpow radix2 600)<=bpow radix2 (-473)).
  { intros c Fc C Diff. split; [exact Fc | split; [exact C | ]].
    assert (Gap : Rabs (B h*bpow radix2 (-600)-B c)<=
      bpow radix2 (-1075)+bpow radix2 (-1074)).
    { replace (B h*bpow radix2 (-600)-B c) with
        ((B h*bpow radix2 (-600)-B (subnormal_initial64 h))+
          (B (subnormal_initial64 h)-B c)) by ring.
      eapply Rle_trans; [apply Rabs_triang | ].
      rewrite Rabs_minus_sym in Error, Diff. lra. }
    replace (B h-B c*bpow radix2 600) with
      ((B h*bpow radix2 (-600)-B c)*bpow radix2 600).
    - rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 600)) by apply bpow_ge_0.
      apply Rle_trans with ((bpow radix2 (-1075)+bpow radix2 (-1074))*bpow radix2 600).
      + apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Gap].
      + rewrite Rmult_plus_distr_r, <- !bpow_plus.
        change (-1075+600)%Z with (-475)%Z. change (-1074+600)%Z with (-474)%Z. bpow_num. lra.
    - rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus.
      change (bpow radix2 (-600+600)) with 1. ring. }
  pose proof (subnormal_adjacent_ieee (subnormal_initial64 h) 1 F0 C0 ltac:(lia)) as Up.
  pose proof (subnormal_adjacent_ieee (subnormal_initial64 h) (-1) F0 C0 ltac:(lia)) as Down.
  change (bits_of_b64 (subnormal_initial64 h)+ -1)%Z with
    (bits_of_b64 (subnormal_initial64 h)-1)%Z in Down.
  assert (Stay : finite (subnormal_initial64 h) /\
    bpow radix2 (-1074)<=B (subnormal_initial64 h)<=bpow radix2 (-1021) /\
    Rabs (B h-B (subnormal_initial64 h)*bpow radix2 600)<=bpow radix2 (-473)).
  { apply Step; [exact F0 | bpow_num_all; lra | rewrite Rminus_diag_eq by reflexivity;
      rewrite Rabs_R0; apply bpow_ge_0]. }
  unfold subnormal_candidate64.
  destruct (Bcompare 53 1024 _ _) as [[ | | ] | ];
    try (destruct Up as (F & C & D); exact (Step _ F C D));
    destruct (Bcompare 53 1024 _ _) as [[ | | ] | ]; try exact Stay;
    destruct Down as (F & C & D); exact (Step _ F C D).
Qed.

Theorem subnormal_fast_ieee h l z v : finite h -> finite l ->
  bpow radix2 (-426)<=B h<=3*bpow radix2 (-423) ->
  Rabs (B l)<=bpow radix2 (-473) ->
  Rabs (z-(B h+B l))<=bpow radix2 (-67)*B h ->
  subnormal_fast64 h l=Some v -> finite v /\ B v=rndF (z*bpow radix2 (-600)).
Proof.
  intros Fh Fl H L E Decision.
  destruct (subnormal_candidate_ieee h l Fh H) as (Fc & C & Close).
  destruct (subnormal_accept_ieee h l (subnormal_candidate64 h l) z v Fh Fl Fc
    ltac:(bpow_num_all; lra) L C Close E Decision) as (_ & F & V).
  split; assumption.
Qed.
