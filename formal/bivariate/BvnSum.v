(** The double-word accumulation of the quadrature sum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Require Import BvnRound.
Open Scope R_scope.

Lemma two_sum_exact a b : fmtF a -> fmtF b ->
  fst (two_sum a b) + snd (two_sum a b) = a + b /\ fmtF (fst (two_sum a b)) /\ fmtF (snd (two_sum a b))
  /\ fst (two_sum a b) = rndF (a + b).
Proof.
  intros Fa Fb.
  pose proof (two_sum_eq a b Fa Fb) as E.
  pose proof (two_sum_fmt a b Fa Fb) as [Fs Fe].
  pose proof (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl a b (fmtF_fmtX a Fa) (fmtF_fmtX b Fb)) as C.
  rewrite E. cbn [fst snd].
  repeat split; try assumption.
  - Show. lra.
  - unfold TwoSum_sum. unfold TwoSum. simpl. symmetry. apply sum_round; assumption.
Qed.
