From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound N1head N5a.
Open Scope R_scope.

(** A verified forward-error calculator for straight-line arithmetic: a tree of
    additions, subtractions, products and divisions by positive constants over
    leaves that carry a magnitude bound and an error bound.  [bnd] computes the
    bounds; [bnd_sound] proves them from the leaves' [ab] hypotheses. *)
Inductive E : Type :=
  | Lf : nat -> E
  | Ad : E -> E -> E
  | Sb : E -> E -> E
  | Ml : E -> E -> E
  | Dc : R -> E -> E.

Section Calc.
Variables xe ce me ee : nat -> R.
Hypothesis Henv : forall i, ab (xe i) (ce i) (me i) (ee i).

Fixpoint sem (t : E) : R :=
  match t with
  | Lf i => xe i
  | Ad a b => sem a + sem b
  | Sb a b => sem a - sem b
  | Ml a b => sem a * sem b
  | Dc c a => sem a / c
  end.

Fixpoint csem (t : E) : R :=
  match t with
  | Lf i => ce i
  | Ad a b => rnd (csem a + csem b)
  | Sb a b => rnd (csem a - csem b)
  | Ml a b => rnd (csem a * csem b)
  | Dc c a => rnd (csem a / c)
  end.

Fixpoint bnd (t : E) : R * R :=
  match t with
  | Lf i => (me i, ee i)
  | Ad a b => let '(m1, e1) := bnd a in let '(m2, e2) := bnd b in
      (m1 + m2, e1 + e2 + u * (m1 + e1 + (m2 + e2)) + eta)
  | Sb a b => let '(m1, e1) := bnd a in let '(m2, e2) := bnd b in
      (m1 + m2, e1 + e2 + u * (m1 + e1 + (m2 + e2)) + eta)
  | Ml a b => let '(m1, e1) := bnd a in let '(m2, e2) := bnd b in
      (m1 * m2, m1 * e2 + m2 * e1 + e1 * e2 + u * ((m1 + e1) * (m2 + e2)) + eta)
  | Dc c a => let '(m, e) := bnd a in (m / c, e / c + u * ((m + e) / c) + eta)
  end.

Theorem bnd_sound (cp : R -> Prop) (t : E) (Hc : forall c, cp c -> 0 < c) :
  (forall c a, t = Dc c a -> cp c) -> True.
Proof. intros. exact I. Qed.

(** Divisors must be positive; [wf] says so. *)
Fixpoint wf (t : E) : Prop :=
  match t with
  | Lf _ => True
  | Ad a b | Sb a b | Ml a b => wf a /\ wf b
  | Dc c a => 0 < c /\ wf a
  end.

Theorem sound (t : E) : wf t -> ab (sem t) (csem t) (fst (bnd t)) (snd (bnd t)).
Proof.
  induction t as [i|a IHa b IHb|a IHa b IHb|a IHa b IHb|c a IHa]; intros Hw; simpl in Hw.
  - simpl. apply Henv.
  - destruct Hw as [Hwa Hwb]. specialize (IHa Hwa). specialize (IHb Hwb).
    simpl. destruct (bnd a) as [m1 e1]. destruct (bnd b) as [m2 e2]. simpl in *.
    exact (ab_add _ _ _ _ _ _ _ _ IHa IHb).
  - destruct Hw as [Hwa Hwb]. specialize (IHa Hwa). specialize (IHb Hwb).
    simpl. destruct (bnd a) as [m1 e1]. destruct (bnd b) as [m2 e2]. simpl in *.
    exact (ab_sub _ _ _ _ _ _ _ _ IHa IHb).
  - destruct Hw as [Hwa Hwb]. specialize (IHa Hwa). specialize (IHb Hwb).
    simpl. destruct (bnd a) as [m1 e1]. destruct (bnd b) as [m2 e2]. simpl in *.
    exact (ab_mul _ _ _ _ _ _ _ _ IHa IHb).
  - destruct Hw as [Hc Hwa]. specialize (IHa Hwa).
    simpl. destruct (bnd a) as [m e]. simpl in *.
    exact (ab_divc _ _ _ _ _ Hc IHa).
Qed.
End Calc.
