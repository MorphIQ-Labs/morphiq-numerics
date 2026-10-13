(** The middle positive tail's rounding decision, with the analytic
    approximation bound explicit and the generated pi constant discharged. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxDecision ErfcxConstants ErfcxEntryTables.
Require Import ErfcxMiddlePolynomial ErfcxMiddleValue.
Open Scope R_scope.

Definition middle_fast64 x :=
  let '(h,l) := middle64 x in erfcx_decide64 h l.

Theorem middle_fast_ieee x s v : finite x -> 16 <= B x <= 512 ->
  998/1000 <= s <= 1 ->
  - /2^74 <= correction_exact ((1/B x)*(1/B x))-s <= /2^74 ->
  middle_fast64 x=Some v -> finite v /\ B v=rndF ((inv_sqrt_pi/B x)*s).
Proof.
  intros Fx X S A. unfold middle_fast64.
  pose proof (Rabs_le_inv _ _ cs_split_bound) as C.
  pose proof (middle_normalized_ieee x inv_sqrt_pi s Fx X inv_sqrt_pi_positive C S A) as M.
  destruct (middle64 x) as [h l].
  destruct M as (Fh & Fl & Error & Norm & H).
  set (z := (inv_sqrt_pi/B x)*s) in *.
  assert (Zpos : 0<z).
  { unfold z. apply Rmult_lt_0_compat; [apply Rdiv_lt_0_compat; [exact inv_sqrt_pi_positive | lra] | lra]. }
  assert (Err : Rabs ((B h+B l-z)/z) <= bpow radix2 (-67)).
  { replace (bpow radix2 (-67)) with (/2^67) by (bpow_num; simpl; field).
    apply Rabs_le. exact Error. }
  assert (Rel : Rabs (z-(B h+B l)) <= bpow radix2 (-67)*Rabs z).
  { unfold Rdiv in Err. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq z) in Err by lra.
    rewrite Rabs_minus_sym, (Rabs_pos_eq z) by lra.
    replace (Rabs (B h+B l-z)) with ((Rabs (B h+B l-z)/z)*z) by (field; lra). nra. }
  assert (Hb : bpow radix2 (-900) <= Rabs (B h) <= bpow radix2 1000).
  { rewrite Rabs_pos_eq by lra. split.
    - apply Rle_trans with (bpow radix2 (-21)); [apply bpow_le; lia | ].
      replace (bpow radix2 (-21)) with (/2^21) by (bpow_num; simpl; field). lra.
    - apply Rle_trans with (bpow radix2 3); [change (bpow radix2 3) with 8; lra | apply bpow_le; lia]. }
  intros D. destruct (erfcx_decide_ieee h l z v Fh Fl Hb Norm Rel D) as [V Round].
  split; [rewrite V; exact Fh | exact Round].
Qed.
