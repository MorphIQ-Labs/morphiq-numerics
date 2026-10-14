(** The generated density cutoff straddles the zero midpoint at adjacent
    binary64 inputs. Monotonicity extends this check to the full half-line. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings.
Require Import StageGappa NormalConstants NormalCentered NormalAccurateDensity.
Open Scope R_scope.

Lemma normal_density_decreasing x y : 0<=x<=y ->
  normal_density y<=normal_density x.
Proof.
  intros X. unfold normal_density.
  apply Rmult_le_compat_l.
  - unfold normal_density_constant. apply Rlt_le,Rinv_0_lt_compat,sqrt_lt_R0.
    pose proof PI_RGT_0;nra.
  - apply exp_le;nra.
Qed.

Lemma normal_pdf_previous_input x : finite x -> 0<=B x<B normal_pdf_zero ->
  B x<=B normal_pdf_zero-bpow radix2 (-47).
Proof.
  intros F X. destruct normal_pdf_zero_ok as [Fc Value].
  destruct(Rle_dec 32 (B x)) as [Large|Small].
  - assert (Gx : on_grid (-47) (B x)).
    { change (-47)%Z with (5-52)%Z.
      apply(grid_fmt_bound (FLT_exp emin prec) 5).
      - intros;unfold FLT_exp,emin,prec;lia.
      - apply B_fmt.
      - right;change(bpow radix2 5)with 32;rewrite Rabs_pos_eq;lra. }
    assert (Gc : on_grid (-47) (B normal_pdf_zero)).
    { rewrite Value.
      change(on_grid (-Z.of_nat 47) (IZR 5429674482247356/2^47)).
      apply val_grid;lia. }
    pose proof(grid_nonzero (-47) (B normal_pdf_zero-B x)
      (grid_minus _ _ _ Gc Gx) ltac:(lra)) as Gap.
    rewrite Rabs_pos_eq in Gap by lra;lra.
  - rewrite Value. bpow_num;lra.
Qed.

Theorem normal_pdf_zero_midpoint x : finite x -> 0<=B x ->
  (B normal_pdf_zero<=B x -> normal_density(B x)<bpow radix2 (-1075)) /\
  (B x<B normal_pdf_zero -> bpow radix2 (-1075)<normal_density(B x)).
Proof.
  intros F X. destruct normal_pdf_zero_bracket as [Cutoff Previous].
  destruct normal_pdf_zero_ok as [_ Value].
  assert (CutoffValue : normal_density(B normal_pdf_zero)<bpow radix2 (-1075)).
  { unfold normal_density,normal_density_constant. unfold Rdiv in *.
    rewrite Rmult_comm;exact Cutoff. }
  assert (PreviousValue : bpow radix2 (-1075)<
    normal_density(B normal_pdf_zero-bpow radix2 (-47))).
  { unfold normal_density,normal_density_constant. unfold Rdiv in *.
    rewrite Rmult_comm;exact Previous. }
  split;intros Bound.
  - eapply Rle_lt_trans;[apply normal_density_decreasing|exact CutoffValue].
    split;[rewrite Value;lra|exact Bound].
  - pose proof(normal_pdf_previous_input x F ltac:(split;assumption)) as Gap.
    eapply Rlt_le_trans;[exact PreviousValue|apply normal_density_decreasing].
    split;assumption.
Qed.
