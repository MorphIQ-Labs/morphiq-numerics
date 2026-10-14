(** The unscaled large positive tail's rounding decision. Its analytic
    asymptotic remainder is explicit; IEEE normalization is discharged. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxDecision ErfcxConstants ErfcxEntryTables.
Require Import ErfcxTailCorrection ErfcxTailValue.
Open Scope R_scope.

Definition tail_unscaled_fast64 x :=
  let '(h,l) := tail64 x in erfcx_decide64 h l.

Theorem tail_unscaled_fast_ieee x rem v : finite x -> 512 <= B x <= bpow radix2 897 ->
  0 <= rem <= 7/2^72 -> tail_unscaled_fast64 x=Some v ->
  finite v /\ B v=rndF ((inv_sqrt_pi/B x)*(1+tail_polynomial ((1/B x)*(1/B x))+rem)).
Proof.
  intros Fx X Rem. unfold tail_unscaled_fast64.
  pose proof (Rabs_le_inv _ _ cs_split_bound) as C.
  pose proof (tail_normalized_ieee x inv_sqrt_pi rem Fx X inv_sqrt_pi_positive C Rem) as T.
  destruct (tail64 x) as [h l]. destruct T as (Fh & Fl & Error & Norm & H).
  set (t := (1/B x)*(1/B x)) in *.
  assert (Y : 0 <= 1/B x <= /512).
  { unfold Rdiv. rewrite Rmult_1_l. split; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
  assert (Tbound : 0<=t<=/262144) by (unfold t; nra).
  assert (P : 0<=t*(3/4-(15/8)*t)) by nra.
  assert (Spos : 0<1+tail_polynomial t+rem) by (unfold tail_polynomial; nra).
  set (z := (inv_sqrt_pi/B x)*(1+tail_polynomial t+rem)) in *.
  assert (Zpos : 0<z).
  { unfold z. apply Rmult_lt_0_compat; [apply Rdiv_lt_0_compat; [exact inv_sqrt_pi_positive | lra] | exact Spos]. }
  assert (Err : Rabs ((B h+B l-z)/z) <= bpow radix2 (-67)).
  { replace (bpow radix2 (-67)) with (/2^67) by (bpow_num; simpl; field).
    apply Rabs_le. exact Error. }
  assert (Rel : Rabs (z-(B h+B l)) <= bpow radix2 (-67)*Rabs z).
  { unfold Rdiv in Err. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq z) in Err by lra.
    rewrite Rabs_minus_sym, (Rabs_pos_eq z) by lra.
    replace (Rabs (B h+B l-z)) with ((Rabs (B h+B l-z)/z)*z) by (field; lra). nra. }
  assert (Hb : bpow radix2 (-900) <= Rabs (B h) <= bpow radix2 1000).
  { pose proof (bpow_gt_0 radix2 (-900)). rewrite Rabs_pos_eq by lra. split; [lra | ].
    apply Rle_trans with (bpow radix2 (-8)); [lra | apply bpow_le; lia]. }
  intros D. destruct (erfcx_decide_ieee h l z v Fh Fl Hb Norm Rel D) as [V Round].
  split; [rewrite V; exact Fh | exact Round].
Qed.
