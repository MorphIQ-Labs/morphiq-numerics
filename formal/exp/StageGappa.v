(** Applying the stages' Gappa certificates (formal/exp/stage_*.g).

    Each certificate's Coq proof, which scripts/check_formal.sh builds,
    proves [l1 : s1 -> False]: its hypotheses' bounds and the negation of one
    of its goals' bounds are contradictory. A theorem restating a goal (the
    stages' [*_bound] theorems) assumes that goal false, fills [s1]'s
    hypotheses ([gappa_hyps], from bounds [lo <= v <= hi] in context, by
    [bnd_of], with the endpoints compared exactly by [lra]), and picks the false goal's disjunct ([gappa_pick]), which
    holds by conversion: each goal is stated with Gappa's own spelling of its
    bounds and terms, [float2R (Float2 m e) = IZR m * bpow radix2 e] by
    definition, so the negated statement and Gappa's are the same
    proposition. *)

From Coq Require Import Reals ZArith Lra Classical.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.

Open Scope R_scope.

(** Gappa's rounding to binary64, nearest-even. *)
Notation rn := (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE).

Lemma bnd_of (x lo hi : R) (ma ea mb eb : Z) :
  IZR ma * bpow radix2 ea <= lo -> hi <= IZR mb * bpow radix2 eb -> lo <= x <= hi ->
  BND x (makepairF (Float2 ma ea) (Float2 mb eb)).
Proof.
  intros Ha Hb [H1 H2]. split; [apply Rle_trans with lo | apply Rle_trans with hi];
    [exact Ha | exact H1 | exact H2 | exact Hb].
Qed.

Lemma bnd_to (x : R) (ma ea mb eb : Z) :
  BND x (makepairF (Float2 ma ea) (Float2 mb eb)) ->
  IZR ma * bpow radix2 ea <= x <= IZR mb * bpow radix2 eb.
Proof. intros H. exact H. Qed.

(** Powers of two as rational literals, which [lra] reads. *)
Lemma bpow_neg p : bpow radix2 (Zneg p) = / IZR (Z.pow_pos 2 p).
Proof. reflexivity. Qed.
Lemma bpow_pos p : bpow radix2 (Zpos p) = IZR (Z.pow_pos 2 p).
Proof. reflexivity. Qed.
Ltac bpow_num :=
  rewrite ?bpow_neg, ?bpow_pos; try change (bpow radix2 0) with 1;
  repeat match goal with |- context [Z.pow_pos 2 ?p] =>
    let v := eval vm_compute in (Z.pow_pos 2 p) in change (Z.pow_pos 2 p) with v end.

(** A hypothesis [BND v i] of the certificate, from a bound [lo <= v <= hi]
    in context, with [i]'s endpoints computed. *)
Ltac gappa_bnd :=
  lazymatch goal with
  | |- BND ?v _ =>
      lazymatch goal with
      | H : _ <= v <= _ |- _ =>
          refine (bnd_of _ _ _ _ _ _ _ _ _ H); bpow_num; lra
      end
  end.

(** Splits [s1] into its hypotheses' bounds, solved by [gappa_bnd], and its
    goals' disjunction, left. *)
Ltac gappa_hyps :=
  repeat lazymatch goal with
  | |- BND _ _ => gappa_bnd
  | |- not _ => fail
  | |- _ -> False => fail
  | |- _ \/ _ => fail
  | |- _ /\ _ => split
  | |- _ => hnf
  end.

(** Powers of two as literals in every hypothesis and the goal. *)
Ltac bpow_num_all :=
  rewrite ?bpow_neg, ?bpow_pos in *; try change (bpow radix2 0) with 1 in *;
  repeat match goal with H : context [Z.pow_pos 2 ?p] |- _ =>
    let v := eval vm_compute in (Z.pow_pos 2 p) in change (Z.pow_pos 2 p) with v in H end;
  repeat match goal with |- context [Z.pow_pos 2 ?p] =>
    let v := eval vm_compute in (Z.pow_pos 2 p) in change (Z.pow_pos 2 p) with v end.

(** In the goals' disjunction, the negated goal [Hn : ~ (lo <= v <= hi)]:
    the disjunct whose bound on the same [v] implies [lo <= v <= hi]. *)
Ltac gappa_close Hn :=
  let Hb := fresh "Hb" in intros Hb; apply bnd_to in Hb;
  first [exact (Hn Hb) | (apply Hn; revert Hb; clear; bpow_num_all; intros [? ?]; first [split; lra | lra])].

Ltac gappa_pick Hn :=
  lazymatch goal with
  | |- _ \/ _ => first [left; gappa_pick Hn | right; gappa_pick Hn]
  | |- not _ => gappa_close Hn
  | |- _ -> False => gappa_close Hn
  | |- _ => hnf; gappa_pick Hn
  end.

(** One goal [lo <= v <= hi] of a certificate, by its theorem [l1]. *)
Ltac gappa_goal l1 :=
  apply NNPP; let Hn := fresh "Hn" in intros Hn; apply l1; gappa_hyps; gappa_pick Hn.

(** Gappa's spellings of [1/2] and [1]. *)
Definition half_g : R := float10R (Float10 5 (-1)).
Definition one_g : R := Float1 1.

Lemma half_g_eq : half_g = / 2.
Proof. unfold half_g, float10R, F2R. simpl. field. Qed.

Lemma one_g_eq : one_g = 1.
Proof. reflexivity. Qed.
