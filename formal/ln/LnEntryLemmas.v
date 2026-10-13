(** Entry-level magnitude, finiteness, and tiny-input rounding. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest RoundingGaps.
From Interval Require Import Tactic.
Require Import LnAccurate Ln1pLemmas LnFastDecision.
Open Scope R_scope.
Theorem lf_tiny_round x : Rabs x</2^54 -> fmtF x -> rndF(ln(1+x))=x.
Proof.
 intros X Fx. destruct (Req_dec x 0) as [-> | N].
 - rewrite Rplus_0_r,ln_1. apply round_0; exact _.
 - apply round_relative_close; try assumption.
   assert (A : Rabs x<=/4) by (apply Rle_trans with (/2^54); [lra | interval with (i_prec 100)]).
   pose proof (alt_rem 1 (/4) x ltac:(lra) A) as E.
   assert (S : alt 1 x=x) by (cbn [alt INR]; field). rewrite S in E.
   apply Rle_lt_trans with (1:=E). change (1+1)%nat with 2%nat. cbn [INR pow]. pose proof (Rabs_pos_lt x N). nra.
Qed.
Lemma lf_nonzero_finite x : B x<>0 -> finite x.
Proof. intros N; destruct x; try reflexivity; exfalso; apply N; reflexivity. Qed.
Lemma lf_rounded_approx_finite y w v : B y=rndF w -> bpow radix2 (-55)<=Rabs v ->
 Rabs(w-v)<=/2^123*Rabs v -> finite y.
Proof.
 intros Y V E. assert (W : bpow radix2 (-56)<=Rabs w).
 { pose proof (Rabs_triang_inv v w). rewrite Rabs_minus_sym in H.
   assert (/2^123<=/2) by interval with (i_prec 160). pose proof (Rabs_pos v).
   apply Rle_trans with ((/2)*bpow radix2 (-55)); [interval with (i_prec 100) | nra]. }
 assert (A : bpow radix2 (-56)<=Rabs(B y)).
 { rewrite Y. apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-56)); lia | exact W]. }
 apply lf_nonzero_finite; intro Z; rewrite Z,Rabs_R0 in A; pose proof (bpow_gt_0 radix2 (-56)); lra.
Qed.
