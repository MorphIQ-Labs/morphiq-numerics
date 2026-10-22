(** atan2's fast path end to end: for positive finite [n <= d] with [n/d >= 2^-901]
    it returns the form's double-word within [2^-62] of the exact angle, normalized,
    and the start [(ph, pl)] within [2^-63 (1 + 2^-40)] of [atan (n/d)]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinPath
  Atan2Tables Atan2Kernel Atan2Ratio Atan2Within Atan2Fast Atan2Forms.
Open Scope R_scope.

(** [atan] is 1-Lipschitz on the non-negative reals. *)
Lemma atan_lip a b : 0 <= a -> a <= b -> atan b - atan a <= b - a.
Proof.
  intros Ha Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq]; [ | subst b; lra].
  destruct (atan_id_diff a b Ha Hlt) as [c [Hc E]].
  assert (Hq : 0 <= c * c / (1 + c * c)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  nra.
Qed.

(** The ratio on the unscaled operands. *)
Lemma ratio_stage n d : finite n -> finite d -> 0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  exists th tl, atan2_ratio n d = (th, tl) /\ finite th /\ finite tl /\ B th = rndF (B th + B tl) /\
    Rabs (B tl) <= bpow radix2 (-52) * B th /\ Rabs (B tl) <= bpow radix2 (-53) /\ B th <= 1 /\ bpow radix2 (-902) <= B th /\
    Rabs (B th + B tl - B n / B d) <= bpow radix2 (-104) * (B n / B d) /\
    (bpow radix2 (-8) <= B n / B d -> on_grid (-211) (B tl)).
Proof.
  intros Fn Fd Pn Hnd Hq.
  assert (Pd : 0 < B d) by lra.
  destruct (exponent_ok d Fd Pd) as [e [Hed [Hek [He1 He2]]]].
  pose proof (bpow_cancel e) as Hc. pose proof (bpow_gt_0 radix2 (-e)) as Pe.
  assert (Hds : 1 <= B d * bpow radix2 (-e) < 2).
  { split.
    - pose proof (Rmult_le_compat_r (bpow radix2 (-e)) _ _ (bpow_ge_0 radix2 (-e)) He1). lra.
    - assert (bpow radix2 (e + 1) * bpow radix2 (-e) = 2) by (rewrite <- bpow_plus; replace (e + 1 + - e)%Z with 1%Z by ring; reflexivity).
      pose proof (Rmult_lt_compat_r (bpow radix2 (-e)) _ _ Pe He2). lra. }
  assert (Hq1 : B n / B d <= 1).
  { apply Rmult_le_reg_r with (B d); [exact Pd | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (Hns : B n * bpow radix2 (-e) = (B n / B d) * (B d * bpow radix2 (-e))) by (field; lra).
  assert (Hb1000 : bpow radix2 (-1000) <= bpow radix2 (-901)) by (apply bpow_le; lia).
  assert (Hnsb : bpow radix2 (-1000) <= B n * bpow radix2 (-e) <= 2).
  { pose proof (bpow_gt_0 radix2 (-1000)) as P1000. pose proof (bpow_gt_0 radix2 (-901)) as P901. destruct Hds as [X1 X2]. rewrite Hns. split; nra. }
  destruct (scale_exact d e Fd ltac:(lra) Hek ltac:(destruct Hds; pose proof (bpow_gt_0 radix2 (-1000)); lra) ltac:(destruct Hds; lra)) as [Fds Vds].
  destruct (scale_exact n e Fn ltac:(lra) Hek (proj1 Hnsb) (proj2 Hnsb)) as [Fns Vns].
  rewrite atan2_ratio_pair. rewrite Hed.
  assert (Hq' : B (atan2_scale n e) / B (atan2_scale d e) = B n / B d).
  { rewrite Vns, Vds. field. split; lra. }
  destruct (ratio_core (atan2_scale n e) (atan2_scale d e) Fns Fds ltac:(rewrite Vds; exact Hds) ltac:(rewrite Hq'; exact Hq) ltac:(rewrite Hq'; exact Hq1))
    as [th [tl [Hr [Fth [Ftl [Dw [Rl [Rl2 [Th1 [Th2 [Er Gr]]]]]]]]]]].
  rewrite Hq' in Er, Gr. exists th, tl. repeat split; assumption.
Qed.
