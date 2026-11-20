(** A successful radix-logarithm rounding decision returns the correctly
    rounded exact logarithm. The radix range, rather than ln's larger lower
    bound near one, discharges the decision's underflow guard. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas LnFastTables LogRadixRounding LogRadixFast
  LogRadixFastBound LogRadixReconstruct.
Open Scope R_scope.

Lemma radix_decision_ok h l v r : finite h -> finite l -> B h=rndF(B h+B l) ->
  bpow radix2 (-57)<=Rabs v<=1600 ->
  Rabs(B h+B l-v)<=/2^63*Rabs v -> decide_with h l lf_eps=Some r ->
  finite r /\ B r=rndF v.
Proof.
  intros Fh Fl D V E Decision.
  assert (Ep : 0<=/2^63<=/100) by (split; interval).
  assert (Small : Rabs(B h+B l)<=2048).
  { pose proof (Rabs_triang_inv (B h+B l) v). pose proof (Rabs_pos v); nra. }
  assert (Large : bpow radix2 (-58)<=Rabs(B h+B l)).
  { pose proof (Rabs_triang_inv v (B h+B l)) as T; rewrite Rabs_minus_sym in T.
    assert (Half : bpow radix2 (-58)=bpow radix2 (-57)/2) by (bpow_num; field).
    pose proof (bpow_gt_0 radix2 (-57)); nra. }
  assert (H : bpow radix2 (-900)<=Rabs(B h)<=bpow radix2 1000).
  { rewrite D; split.
    - apply Rle_trans with (bpow radix2 (-58)); [apply bpow_le; lia | ].
      apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-58)); lia | exact Large].
    - apply Rle_trans with (bpow radix2 11); [ | apply bpow_le; lia].
      apply abs_round_le_generic; [exact _ | exact _ | apply (fmt_pow 11); lia | exact Small]. }
  destruct (decide_with_ok h l lf_eps v (/2^63) r Fh Fl lf_eps_finite H D) as [R Value].
  - split; interval with (i_prec 100).
  - rewrite lf_eps_val; split; interval with (i_prec 180).
  - rewrite Rabs_minus_sym; exact E.
  - exact Decision.
  - subst r; split; [exact Fh | symmetry; exact Value].
Qed.

Theorem log2_fast_correct x r : finite x -> 0<B x -> B x<>1 ->
  log2_fast x=Some r -> finite r /\ B r=rndF(ln(B x)/ln 2).
Proof.
  intros Fx Px Nx. pose proof (log2_fast_value_bounded x Fx Px) as P.
  unfold log2_fast; destruct (log2_fast_value x) as [h l]. destruct P as [Fh [Fl [D E]]].
  intros Decision. apply (radix_decision_ok h l (ln(B x)/ln 2) r Fh Fl D); try assumption.
  apply radix_log_range; try assumption; split; interval.
Qed.

Theorem log10_fast_correct x r : finite x -> 0<B x -> B x<>1 ->
  log10_fast x=Some r -> finite r /\ B r=rndF(ln(B x)/ln 10).
Proof.
  intros Fx Px Nx. pose proof (log10_fast_value_bounded x Fx Px) as P.
  unfold log10_fast; destruct (log10_fast_value x) as [h l]. destruct P as [Fh [Fl [D E]]].
  intros Decision. apply (radix_decision_ok h l (ln(B x)/ln 10) r Fh Fl D); try assumption.
  apply radix_log_range; try assumption; split; interval.
Qed.
