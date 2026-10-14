(** The full negative value kernel, with the remaining analytic table
    contract explicit. The omitted-positive-term branch needs only [0<=G<=1]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ErfcxReciprocal ErfcxReflectionSquare ErfcxReflectionExp.
Require Import ErfcxReflectionSubtract ErfcxTableEntry.
Require erfcx_reflection_omitted.
Open Scope R_scope.

Lemma reflection_omitted_bound E G sc de :
  0.999 <= E <= 2.001 -> 0 <= G <= 1 -> 0 <= sc <= bpow radix2 (-106) ->
  Rabs de <= IZR 209 * bpow radix2 (-78) ->
  Rabs (((E+de)-(E-G*sc))/(E-G*sc)) <= bpow radix2 (-69).
Proof.
  intros HE HG Hsc Hde. apply Rabs_le_inv in Hde. apply Rabs_le.
  erfcx_goal (erfcx_reflection_omitted.l1 E de G sc).
Qed.

Lemma reflection_scaled_identity v G k :
  (2*exp v-G)/bpow radix2 (k+1) = exp v/bpow radix2 k-G*bpow radix2 (-k-1).
Proof.
  replace (-k-1)%Z with (-(k+1))%Z by lia.
  rewrite bpow_opp, bpow_plus. change (bpow radix2 1) with 2.
  field. apply Rgt_not_eq, bpow_gt_0.
Qed.

Definition reflection_table_contract x G : Prop :=
  /2 < - B x < 9 ->
  let '(gh,gl) := table_eval64 (fneg x) in
  /32 <= B gh <= 0.617 /\ Rabs (B gl) <= bpow radix2 (-53) /\
  Rabs (B gh+B gl-G) <= bpow radix2 (-67).

Theorem reflection_value_ieee x G : finite x -> B reflection_limit < B x < - /2 ->
  0 <= G <= 1 -> reflection_table_contract x G ->
  let '(h,l,m) := reflection_value64 x in
  let F := (2*exp (B x*B x)-G)/bpow radix2 m in
  finite h /\ finite l /\ (1 <= m <= 1024)%Z /\ /2 <= B h <= 4 /\
  /4 <= F <= 2 /\ B h = rndF (B h+B l) /\
  Rabs ((B h+B l-F)/F) <= bpow radix2 (-67).
Proof.
  intros Fx X Gbound Table.
  pose proof (reflection_square_ieee x Fx X) as Sq.
  pose proof (reflection_square_exp_ieee x Fx X) as Exp.
  pose proof (reflection_dispatch_range x Fx X) as Dispatch.
  unfold reflection_value64.
  destruct (two_prod64 x x) as [s se]. destruct Sq as [Fs [Fse [Exact [S Low]]]].
  pose proof (reflection_exp_ideal_range s se Fs ltac:(rewrite Rabs_pos_eq; lra) Fse Low) as Ideal.
  rewrite Exact in Ideal.
  destruct (reflection_exp64 s se) as [[eh el] k].
  destruct Exp as [Feh [Fel [K0 [Eh [El [Norm Error]]]]]].
  destruct Dispatch as [K Small].
  set (E := exp (B x*B x)/bpow radix2 k) in *.
  set (de := B eh+B el-E).
  assert (De : Rabs de <= IZR 209*bpow radix2 (-78))
    by (unfold de; rewrite Rabs_minus_sym; exact Error).
  assert (Sc : 0 < bpow radix2 (-k-1) <= /2).
  { split; [apply bpow_gt_0 | ]. change (/2) with (bpow radix2 (-1)). apply bpow_le. lia. }
  assert (FRange : /4 <= E-G*bpow radix2 (-k-1) <= 2) by (split; nra).
  destruct (104 <? k)%Z eqn:Branch.
  - apply Z.ltb_lt in Branch. cbv zeta.
    pose proof (reflection_omitted_bound E G (bpow radix2 (-k-1)) de ltac:(lra) Gbound
      ltac:(split; [apply bpow_ge_0 | apply bpow_le; lia]) De) as Omitted.
    replace (E+de) with (B eh+B el) in Omitted by (unfold de; ring).
    split; [exact Feh | ]. split; [exact Fel | ]. split; [lia | ].
    split; [split; lra | ]. split.
    + rewrite reflection_scaled_identity. exact FRange.
    + split; [exact Norm | ].
      rewrite reflection_scaled_identity. fold E.
      apply Rle_trans with (1 := Omitted). apply bpow_le. lia.
  - apply Z.ltb_ge in Branch. specialize (Small Branch).
    assert (Fn : finite (fneg x)) by (unfold fneg, b64_opp; rewrite is_finite_Bopp; exact Fx).
    assert (Bn : B (fneg x) = -B x) by apply B2R_Bopp.
    pose proof (table_eval_ieee (fneg x) Fn ltac:(rewrite Bn; lra)) as T.
    unfold reflection_table_contract in Table. specialize (Table Small).
    destruct (table_eval64 (fneg x)) as [gh gl].
    destruct T as [Fgh [Fgl _]]. destruct Table as [Gh [Gl Dg]].
    pose proof (reflection_subtract_ieee eh el gh gl k de (B gh+B gl-G)
      Feh Fel Fgh Fgl Eh El Gh Gl ltac:(lia) De Dg) as Sub.
    destruct (reflection_subtract64 eh el gh gl k) as [h l].
    destruct Sub as (Fh & Fl & Hrange & N & Err). cbv zeta.
    split; [exact Fh | ]. split; [exact Fl | ]. split; [lia | ].
    split; [exact Hrange | ]. split.
    + rewrite reflection_scaled_identity. exact FRange.
    + split; [exact N | ].
      rewrite reflection_scaled_identity. fold E.
      replace (B eh+B el-de) with E in Err by (unfold de; ring).
      replace (B gh+B gl-(B gh+B gl-G)) with G in Err by ring.
      exact Err.
Qed.
