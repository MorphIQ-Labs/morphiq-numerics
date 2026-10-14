(** The negative branch's encoded overflow boundary. Binary64 discreteness
    leaves a full input ulp between the last finite and overflowing cases. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings Grid.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxReflectionSquare.
Open Scope R_scope.

Definition erfcx_max : f64 := b64_of_bits 9218868437227405311.
Lemma erfcx_max_ok : finite erfcx_max /\
  B erfcx_max = IZR 9007199254740991*bpow radix2 971 /\ B erfcx_max < bpow radix2 1024.
Proof.
  pose proof (join_val (2^52-1) 2046 ltac:(lia) ltac:(lia)) as [F V].
  rewrite join_eq in F, V.
  change ((2046*2^52+(2^52-1))%Z) with 9218868437227405311%Z in F, V.
  fold erfcx_max in F, V.
  change ((2^52-1+2^52)%Z) with 9007199254740991%Z in V.
  change (2046-1075)%Z with 971%Z in V.
  split; [exact F | split; [exact V | ]]. rewrite V.
  replace (bpow radix2 1024) with (bpow radix2 53*bpow radix2 971)
    by (rewrite <- bpow_plus; reflexivity).
  apply Rmult_lt_compat_r; [apply bpow_gt_0 | ].
  change (bpow radix2 53) with 9007199254740992. change (IZR 9007199254740991) with 9007199254740991. lra.
Qed.

Lemma reflection_boundary_bracket :
  2*exp ((B reflection_limit+bpow radix2 (-48))^2) <= B erfcx_max /\
  bpow radix2 1024-bpow radix2 970 <= 2*exp ((B reflection_limit)^2)-1.
Proof.
  destruct erfcx_max_ok as [_ [Max _]]. rewrite Max.
  unfold reflection_limit.
  rewrite (bits_val 13851560577301767119 true 7495322764862415 48 eq_refl).
  bpow_num. simpl.
  split; interval with (i_prec 128).
Qed.

Lemma reflection_next_input x : finite x -> B reflection_limit < B x ->
  B reflection_limit+bpow radix2 (-48) <= B x.
Proof.
  intros Fx X. pose proof reflection_limit_value as Limit.
  destruct (Rle_dec (B x) (-16)) as [Large | Small].
  - assert (Gx : on_grid (-48) (B x)).
    { change (-48)%Z with (4-52)%Z.
      apply (grid_fmt_bound (FLT_exp emin prec) 4);
        [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
      right. change (bpow radix2 4) with 16. rewrite Rabs_left; lra. }
    assert (Gl : on_grid (-48) (B reflection_limit)).
    { change (-48)%Z with (4-52)%Z.
      apply (grid_fmt_bound (FLT_exp emin prec) 4);
        [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
      right. change (bpow radix2 4) with 16. rewrite Rabs_left; lra. }
    pose proof (grid_nonzero (-48) (B x-B reflection_limit)
      (grid_minus _ _ _ Gx Gl) ltac:(lra)) as Gap.
    rewrite Rabs_pos_eq in Gap by lra. lra.
  - change (bpow radix2 (-48)) with (/281474976710656). lra.
Qed.

Theorem reflection_finite_magnitude x : finite x -> B reflection_limit < B x < - /2 ->
  2*exp (B x*B x) <= B erfcx_max.
Proof.
  intros Fx X. pose proof (reflection_next_input x Fx (proj1 X)) as Next.
  destruct reflection_boundary_bracket as [Upper _].
  pose proof reflection_limit_value as Limit.
  assert (A : B x*B x <= (B reflection_limit+bpow radix2 (-48))^2).
  { change (bpow radix2 (-48)) with (/281474976710656) in *. nra. }
  pose proof (exp_le _ _ A). lra.
Qed.

Theorem reflection_overflow_magnitude x G : B x <= B reflection_limit -> 0 <= G <= 1 ->
  bpow radix2 1024-bpow radix2 970 <= 2*exp (B x*B x)-G.
Proof.
  intros X HG. destruct reflection_boundary_bracket as [_ Lower].
  pose proof reflection_limit_value as Limit.
  assert (A : (B reflection_limit)^2 <= B x*B x) by nra.
  pose proof (exp_le _ _ A). lra.
Qed.
