(** The double-word accumulation of the quadrature sum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
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
  - lra.
  - unfold TwoSum_sum. unfold TwoSum. simpl. symmetry. apply sum_round; assumption.
Qed.

Definition step (hl : R * R) (t : R) : R * R :=
  let '(h, l) := hl in
  let '(s, e) := two_sum h t in (s, rndF (l + e)).

Fixpoint acc (ts : list R) (hl : R * R) : R * R :=
  match ts with
  | nil => hl
  | t :: ts' => acc ts' (step hl t)
  end.

Fixpoint sumR (ts : list R) : R :=
  match ts with nil => 0 | t :: ts' => t + sumR ts' end.

Lemma step_spec h l t : fmtF h -> fmtF l -> fmtF t -> 0 <= h -> 0 <= t ->
  exists s e, step (h, l) t = (s, rndF (l + e)) /\ fmtF s /\ fmtF e /\ 0 <= s
    /\ s + e = h + t /\ Rabs e <= u * (h + t) /\ s <= (1 + u) * (h + t).
Proof.
  intros Fh Fl Ft Hh Ht.
  destruct (two_sum_exact h t Fh Ft) as [Hex [Fs [Fe Hs]]].
  exists (fst (two_sum h t)), (snd (two_sum h t)).
  assert (Hst : step (h, l) t = (fst (two_sum h t), rndF (l + snd (two_sum h t)))).
  { unfold step. destruct (two_sum h t) as [s e]. reflexivity. }
  destruct (rnd_add_delta h t Fh Ft) as [d [Hd Ed]].
  pose proof u_pos as Hu. apply Rabs_le_inv in Hd. destruct Hd as [Hd1 Hd2].
  assert (Hhs : 0 <= h + t) by lra.
  assert (H0s : 0 <= fst (two_sum h t)) by (rewrite Hs; apply rnd_nonneg; exact Hhs).
  assert (Hee : Rabs (snd (two_sum h t)) <= u * (h + t)).
  { assert (E : snd (two_sum h t) = (h + t) - rndF (h + t)) by (rewrite <- Hs; lra).
    rewrite Ed in E.
    assert (E2 : snd (two_sum h t) = - ((h + t) * d)) by (rewrite E; ring). rewrite E2.
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (h + t)) by exact Hhs.
    assert (Rabs d <= u) by (apply Rabs_le; lra). nra. }
  assert (Hsu : fst (two_sum h t) <= (1 + u) * (h + t)) by (rewrite Hs, Ed; nra).
  exact (conj Hst (conj Fs (conj Fe (conj H0s (conj Hex (conj Hee Hsu)))))).
Qed.
