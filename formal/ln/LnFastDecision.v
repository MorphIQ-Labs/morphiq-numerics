(** Rounding decisions after both proved fallback evaluations. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingTest.
From Interval Require Import Tactic.
Require Import LnFastTables LnFastValue Ln1pFast Ln1p Ln1pLemmas LnTableCheck.
Open Scope R_scope.
Lemma lf_ln_away x : finite x -> 0<B x -> B x<>1 -> bpow radix2 (-55)<=Rabs(ln(B x)).
Proof.
 intros Fx Px N. destruct (Rlt_le_dec (B x) (/2)) as [Small | Large].
 - pose proof (ln_le_mono (B x) (/2) Px ltac:(lra)).
   assert (ln(/2)<= -/2) by interval with (i_prec 100).
   rewrite Rabs_left by lra. apply Rle_trans with (/2); [interval with (i_prec 100) | lra].
 - assert (G : on_grid (-53) (B x-1)).
   { apply grid_minus.
     - change (-53)%Z with (-1-52)%Z. apply (grid_fmt_bound (FLT_exp emin prec) (-1)); [unfold FLT_exp,prec; lia | apply B_fmt | right; rewrite Rabs_pos_eq by lra; exact Large].
     - exists 9007199254740992%Z. change (bpow radix2 (-53)) with (/9007199254740992); field. }
   pose proof (grid_nonzero _ _ G ltac:(lra)) as A.
   replace (B x) with (1+(B x-1)) at 1 by ring.
   apply ln1p_away; [lra | apply Rle_trans with (2:=A); apply bpow_le; lia].
Qed.
Lemma lf_decision_ok h l v r : finite h -> finite l -> B h=rndF(B h+B l) ->
 Rabs(B h)<=2048 -> bpow radix2 (-55)<=Rabs v ->
 Rabs(B h+B l-v)<=/2^63*Rabs v -> decide_with h l lf_eps=Some r -> finite r /\ B r=rndF v.
Proof.
 intros Fh Fl Dw H V E D.
 assert (S : bpow radix2 (-56)<=Rabs(B h+B l)).
 { pose proof (Rabs_triang_inv v (B h+B l)) as A. rewrite Rabs_minus_sym in A.
   assert (/2^63<=/2) by interval with (i_prec 100).
   assert (P : 0<=Rabs v) by apply Rabs_pos.
   apply Rle_trans with ((/2)*bpow radix2 (-55)); [interval with (i_prec 100) | nra]. }
 assert (Lo : bpow radix2 (-900)<=Rabs(B h)).
 { rewrite Dw. apply Rle_trans with (bpow radix2 (-56)); [apply bpow_le; lia | ].
   apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-56)); lia | exact S]. }
 destruct (decide_with_ok h l lf_eps v (/2^63) r Fh Fl lf_eps_finite
  ltac:(split; [exact Lo | apply Rle_trans with 2048; [exact H | interval with (i_prec 100)]]) Dw) as [R Vv].
 - split; interval with (i_prec 100).
 - rewrite lf_eps_val; split; interval with (i_prec 180).
 - rewrite Rabs_minus_sym; exact E.
 - exact D.
 - subst r; split; [exact Fh | symmetry; exact Vv].
Qed.
Definition lf_ln_fast x := let '(h,l):=lf_ln_fast_value x in decide_with h l lf_eps.
Theorem lf_ln_fast_ok x r : finite x -> 0<B x -> B x<>1 -> lf_ln_fast x=Some r ->
 finite r /\ B r=rndF(ln(B x)).
Proof.
 intros Fx Px N. pose proof (lf_ln_fast_value_ok x Fx Px) as F.
 unfold lf_ln_fast. destruct (lf_ln_fast_value x) as [h l]. destruct F as [Fh [Fl [Dw [H [L E]]]]].
 intros D. apply (lf_decision_ok h l (ln(B x)) r Fh Fl Dw ltac:(lra) (lf_ln_away x Fx Px N)); [ | exact D].
 apply Rle_trans with (1:=E); apply Rmult_le_compat_r; [apply Rabs_pos | interval with (i_prec 100)].
Qed.
Definition lf_ln1p_fast x := let '(h,l):=lf_ln1p_fast_value x in decide_with h l lf_eps.
Theorem lf_ln1p_fast_ok x r : finite x -> -1<B x -> bpow radix2 (-54)<=Rabs(B x) ->
 lf_ln1p_fast x=Some r -> finite r /\ B r=rndF(ln(1+B x)).
Proof.
 intros Fx Px Ax. pose proof (lf_ln1p_fast_value_ok x Fx Px Ax) as F.
 unfold lf_ln1p_fast. destruct (lf_ln1p_fast_value x) as [h l]. destruct F as [Fh [Fl [Dw [H [L E]]]]].
 apply (lf_decision_ok h l (ln(1+B x)) r Fh Fl Dw H (ln1p_away (B x) Px Ax) E).
Qed.
