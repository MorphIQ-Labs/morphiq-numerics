(** The bounded early-exit loop in erfcx/accurate.rs, on Q256 fields. *)
From Coq Require Import Reals ZArith Lia List.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import ErfcxAccurateTerms ErfcxAccurateSum.
Open Scope R_scope.

Fixpoint q_asym_loop qt odd k fuel term sum :=
  match fuel with
  | O => sum
  | S remaining =>
      let next := neg_q (mul (mul term qt) (odd k)) in
      if (top next <? -262)%Z then sum
      else q_asym_loop qt odd (S k) remaining next (add sum next)
  end.

Definition q_asym_series qt odd := q_asym_loop qt odd 0 399 q_one q_one.

Lemma q_asym_loop_prefix qt odd k fuel :
  exists n, (k<=n<=k+fuel)%nat /\
    q_asym_loop qt odd k fuel (q_asym_term qt odd k) (q_asym_sum qt odd k)=q_asym_sum qt odd n /\
    (n=(k+fuel)%nat \/ (top (q_asym_term qt odd (S n)) < -262)%Z).
Proof.
  revert k. induction fuel as [ | fuel IH]; intros k.
  - exists k. split; [lia | ]. split; [reflexivity | left; lia].
  - cbn [q_asym_loop].
    change (neg_q (mul (mul (q_asym_term qt odd k) qt) (odd k))) with (q_asym_term qt odd (S k)).
    destruct (Z.ltb_spec (top (q_asym_term qt odd (S k))) (-262)) as [Stop | Continue].
    + exists k. split; [lia | ]. split; [reflexivity | right; exact Stop].
    + destruct (IH (S k)) as [n [Range [Value Exit]]].
      exists n. split; [lia | ]. split; [exact Value | ].
      destruct Exit as [Cap | Exit]; [left; lia | right; exact Exit].
Qed.

Local Opaque q_asym_loop.

Theorem q_asym_series_integral qt odd t : 0<=t<=/2^8 -> valid qt ->
  (exists d, Rabs d<=bpow radix2 (-249) /\ qval qt=(t/2)*(1+d)) ->
  (forall k, (k<400)%nat -> valid (odd k) /\ qval (odd k)=2*INR k+1) ->
  valid (q_asym_series qt odd) /\
  Rabs (qval (q_asym_series qt odd)-ErfcxTailIntegral.tail_integral t)<=bpow radix2 (-226).
Proof.
  intros T Qt Square Odd.
  destruct (q_asym_loop_prefix qt odd 0 399) as [n [Range [Value Exit]]].
  change (q_asym_series qt odd=q_asym_sum qt odd n) in Value.
  rewrite Value. apply q_asym_sum_integral; try assumption; lia.
Qed.
