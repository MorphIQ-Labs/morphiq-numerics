(** The largest-input quotient satisfies the final-grid test's word bounds. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxEntryTables ErfcxQuotient ErfcxQuotientScale.
Open Scope R_scope.

Lemma subnormal_quotient_words_ieee x : finite x ->
  bpow radix2 421<=B x<=bpow radix2 424 ->
  let '(h,l) := normalized_quotient64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-426)<=B h<=3*bpow radix2 (-423) /\ Rabs (B l)<=bpow radix2 (-473).
Proof.
  intros Fx X.
  assert (Domain : 512<=B x<=bpow radix2 897).
  { split.
    - apply Rle_trans with (bpow radix2 421); [change 512 with (bpow radix2 9); apply bpow_le; lia | lra].
    - apply Rle_trans with (bpow radix2 424); [lra | apply bpow_le; lia]. }
  pose proof (normalized_quotient_words_ieee x Fx Domain) as Q.
  destruct (normalized_quotient64 x) as [h l]. destruct Q as (Fh & Fl & E & Norm).
  assert (Constant : /2<=B cs+B csl<=5/8).
  { destruct cs_ok as (_ & C & _). destruct csl_ok as (_ & L & _).
    rewrite C,L. unfold cs_r,csl_r,float2R,F2R; simpl; bpow_num; lra. }
  assert (Positive : 0<B x) by (pose proof (bpow_gt_0 radix2 421); lra).
  assert (Inv : bpow radix2 (-424)<=/B x<=bpow radix2 (-421)).
  { replace (bpow radix2 (-424)) with (/bpow radix2 424) by (rewrite <- bpow_opp; reflexivity).
    replace (bpow radix2 (-421)) with (/bpow radix2 421) by (rewrite <- bpow_opp; reflexivity).
    split; apply Rinv_le_contravar; try apply bpow_gt_0; lra. }
  assert (Z : bpow radix2 (-425)<=(B cs+B csl)/B x<=5*bpow radix2 (-424)).
  { unfold Rdiv. bpow_num_all. nra. }
  set (q := (B cs+B csl)/B x) in *.
  assert (Qpos : 0<q) by (pose proof (bpow_gt_0 radix2 (-425)); lra).
  assert (Id : B h+B l=(1+((B h+B l)-q)/q)*q) by (field; lra).
  assert (Sum : bpow radix2 (-426)<=B h+B l<=3*bpow radix2 (-423)).
  { set (err := ((B h+B l)-q)/q) in *.
    clear - Id E Z. bpow_num_all. nra. }
  assert (H : bpow radix2 (-426)<=B h<=3*bpow radix2 (-423)).
  { rewrite Norm. split.
    - apply round_ge_generic; [exact _ | exact _ | | lra].
      apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - apply round_le_generic; [exact _ | exact _ | | lra].
      apply (bnd_fmt 3 (-423)); lia. }
  assert (Hb : bpow radix2 (-900)<=Rabs (B h)).
  { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-426)); lra).
    apply Rle_trans with (bpow radix2 (-426)); [apply bpow_le; lia | lra]. }
  pose proof (lo_bound (B h) (B l) Hb Norm) as Low.
  rewrite (Rabs_pos_eq (B h)) in Low by (pose proof (bpow_gt_0 radix2 (-426)); lra).
  split; [exact Fh | split; [exact Fl | split; [exact Norm | split; [exact H | ]]]].
  bpow_num_all. lra.
Qed.

Theorem subnormal_value_words_ieee x : finite x -> bpow radix2 1021<=B x ->
  let '(h,l) := scaled_quotient64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-426)<=B h<=3*bpow radix2 (-423) /\ Rabs (B l)<=bpow radix2 (-473).
Proof.
  intros Fx X.
  assert (Large : bpow radix2 896<=B x).
  { apply Rle_trans with (bpow radix2 1021); [apply bpow_le; lia | exact X]. }
  destruct (scale_input_ieee x Fx Large) as (Fs & S & Range).
  apply subnormal_quotient_words_ieee; [exact Fs | split; [ | lra]].
  rewrite S. replace (bpow radix2 421) with (bpow radix2 1021*bpow radix2 (-600))
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | exact X].
Qed.
