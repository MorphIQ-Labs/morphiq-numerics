From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound BvnArg BvnSum BvnChain BvnRule BvnTail BvnEllipse BvnRules BvnData.
Open Scope R_scope.

Ltac solve_dat :=
  unfold dat_ok, br_ok, theta_of, zt_of, bp, psi, ETAK, ar0, u, z; simpl;
  repeat split; first [lia | intros _; interval with (i_prec 120) | interval with (i_prec 120) | intros H; discriminate H].

Lemma dat_ok_4 : Forall (dat_ok A4) dats_4.
Proof. unfold dats_4. repeat constructor; solve_dat. Qed.
Lemma br_ok_4 : Forall (br_ok A4 ETAK) dats_4.
Proof. unfold dats_4. repeat constructor; solve_dat. Qed.
