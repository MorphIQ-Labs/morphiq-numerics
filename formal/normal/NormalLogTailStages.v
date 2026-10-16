(** The first interval test falls through to the normalized double-word
    candidate only when it cannot decide. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxDecision NormalComparisons NormalTailAnalytic
  NormalLogFirst NormalLogTailModerate.
Open Scope R_scope.

Definition normal_log_tail_stages64 x :=
  if normal_lt x (erfcx_pow2 6)then
    match normal_log_first_decide64 x with
    | Some v=>Some v
    | None=>normal_log_tail_moderate_decide64 x
    end
  else normal_log_tail_moderate_decide64 x.

Theorem normal_log_tail_stages_decided x v : finite x -> 37<=B x<=bpow radix2 45 ->
  normal_log_tail_stages64 x=Some v -> finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
  intros F X;unfold normal_log_tail_stages64.
  destruct(normal_lt x (erfcx_pow2 6))eqn:Small.
  - destruct(erfcx_pow2_ok 6 ltac:(lia))as[Fs S].
    apply normal_lt_true in Small;try assumption;rewrite S in Small.
    destruct(normal_log_first_decide64 x)as[r|]eqn:First.
    + intros V;injection V as <-;apply(normal_log_first_decided x r F);[change(bpow radix2 6)with 64 in Small;split;lra|exact First].
    + apply normal_log_tail_moderate_decided;assumption.
  - apply normal_log_tail_moderate_decided;assumption.
Qed.
