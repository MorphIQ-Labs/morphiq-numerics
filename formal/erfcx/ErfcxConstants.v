(** Independent interval proof for the generated 1/sqrt(pi) double word. *)
From Coq Require Import Reals ZArith Lia.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxEntryTables.
Open Scope R_scope.
Definition inv_sqrt_pi : R := /sqrt PI.
Lemma inv_sqrt_pi_positive : 0<inv_sqrt_pi.
Proof. unfold inv_sqrt_pi. interval with (i_prec 64). Qed.
Lemma cs_split_bound :
 Rabs (((B cs+B csl)-inv_sqrt_pi)/inv_sqrt_pi)<=/2^110.
Proof.
 destruct cs_ok as [_ [C _]]. destruct csl_ok as [_ [L _]]. rewrite C,L.
 unfold cs_r,csl_r,float2R,F2R,inv_sqrt_pi;cbn [Fnum Fexp].
 bpow_num. interval with (i_prec 200).
Qed.
