(** The enclosure data of each rule satisfy the data conditions of the node
    lemmas, and the per-node suprema sum to the bound stated beside each
    rule. Every statement is interval arithmetic on closed forms. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound BvnArg BvnSum BvnChain BvnQuadG BvnRule BvnTail BvnEllipse BvnRules BvnData.
Open Scope R_scope.

(** The multiplicative constant of one term: weight, [exp], product, sum,
    the constant [asr / (2 TAU)] and its multiplication, as an upper bound
    of [(1 + psi) (1 + u)^3 exp z - 1]. *)
Definition B0 : R := 73 / 10 ^ 17.

Lemma B0_ok : 0 <= B0 /\ bq ETAK <= B0.
Proof.
  split; [unfold B0; lra |].
  unfold bq, psi, ETAK, u, z. simpl. interval with (i_prec 120).
Qed.

Ltac dat_goals :=
  unfold dat_ok, theta_of, zt_of, ar0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  repeat split; try lia; interval with (i_prec 64).

Ltac all_dats := repeat (apply Forall_cons; [dat_goals |]); apply Forall_nil.

Lemma dat_ok_4 : Forall (dat_ok A4) dats_4.
Proof. unfold dats_4. Time all_dats. Qed.
