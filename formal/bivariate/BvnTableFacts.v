(** Facts about the stored Gauss-Legendre tables (formal/bivariate/BvnTables.v)
    that the kernel's operations need to stay finite: each stored abscissa and
    weight is a finite binary64 number in [0, 1], and each panel's unit square lies
    in [1/4, 1]. They are computations on the stored encodings. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt IEEE64Div Encodings.
Require Import BvnTables BvnKernel BvnLift.
Open Scope R_scope.

(** A stored encoding is finite and its value lies in [[lo, hi]]. *)
Definition in_range (lo hi : R) (n : Z) : Prop := finite (aw n) /\ lo <= B (aw n) <= hi.

Ltac in_range_tac :=
  match goal with
  | |- in_range ?lo ?hi ?n =>
      let d := eval vm_compute in (binary_float_of_bits_aux 52 11 n) in
      match d with
      | F754_finite ?s ?m ?e =>
          unfold in_range; split;
          [ exact (bits_finite n s m e eq_refl)
          | rewrite (val_of_bits n s m e eq_refl); unfold F2R; simpl; split; lra ]
      end
  end.

(** A binary64 value, finite and within bounds. *)
Definition fin_range (lo hi : R) (x : f64) : Prop := finite x /\ lo <= B x <= hi.

Lemma in_range_fin lo hi n : in_range lo hi n -> fin_range lo hi (aw n).
Proof. intros H. exact H. Qed.

(** Every node of a panel rule has its unit square in [1/4, 1] and its weight in [0, 1]. *)
Lemma panel_nodes_ok : forall wide,
  Forall (fun xw => fin_range (1 / 4) 1 (fst xw) /\ fin_range 0 1 (snd xw)) (panel_nodes (panel_rule_of wide)).
Proof.
  intros [|]; unfold panel_nodes, panel_rule_of; cbn [combine flat_map app];
    (repeat (apply Forall_cons; [ cbn [fst snd]; split; apply in_range_fin; in_range_tac | ])); apply Forall_nil.
Qed.

(** Every stored abscissa and weight of the low-correlation rules is a finite binary64. *)
Definition all_fin (l : list Z) : bool := forallb (fun z => is_finite 53 1024 (aw z)) l.

Lemma low_rules_check : forallb (fun p => andb (all_fin (fst p)) (all_fin (snd p))) low_rules = true.
Proof. vm_compute. reflexivity. Qed.

Lemma low_rules_finite xs ws : In (xs, ws) low_rules ->
  (forall z, In z xs -> finite (aw z)) /\ (forall z, In z ws -> finite (aw z)).
Proof.
  intros H. pose proof (proj1 (forallb_forall _ _) low_rules_check (xs, ws) H) as C.
  cbn [fst snd] in C. apply andb_prop in C. destruct C as [C1 C2].
  split; intros z Hz.
  - exact (proj1 (forallb_forall _ _) C1 z Hz).
  - exact (proj1 (forallb_forall _ _) C2 z Hz).
Qed.

Lemma low_rule_index_le m limits : (low_rule_index m limits <= length limits)%nat.
Proof. induction limits as [| l r IH]; simpl; [lia |]. destruct (fle m (aw l)); [lia | lia]. Qed.

Lemma low_rule_in rho : In (low_correlation_rule rho) low_rules.
Proof.
  unfold low_correlation_rule. apply nth_In.
  pose proof (low_rule_index_le (fabs rho) low_rule_limits) as H.
  change (length low_rule_limits) with 8%nat in H. change (length low_rules) with 9%nat. lia.
Qed.

Lemma low_pairs_finite rho xs ws : low_correlation_rule rho = (xs, ws) ->
  forall xz wz, In (xz, wz) (combine xs ws) -> finite (aw xz) /\ finite (aw wz).
Proof.
  intros Hr xz wz Hin.
  pose proof (low_rule_in rho) as Hm. rewrite Hr in Hm.
  destruct (low_rules_finite xs ws Hm) as [Fx Fw].
  split; [apply Fx; exact (in_combine_l _ _ _ _ Hin) | apply Fw; exact (in_combine_r _ _ _ _ Hin)].
Qed.
