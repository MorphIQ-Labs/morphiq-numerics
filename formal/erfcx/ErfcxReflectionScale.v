(** Power-of-two scaling in the reflected subtraction, including low words
    small enough to underflow. The conservative absolute budget is tiny
    compared with the reflection evaluation budget. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Encodings RoundingConstant.
Require Import StageGappa.
Open Scope R_scope.

Definition reflection_scale64 k : f64 := b64_of_bits (Z.shiftl (1022-k) 52).

Lemma reflection_scale_ok k : (0 <= k <= 104)%Z ->
  finite (reflection_scale64 k) /\ B (reflection_scale64 k) = bpow radix2 (-k-1) /\
  0 < B (reflection_scale64 k) <= /2.
Proof.
  intros K. destruct (join_val 0 (1022-k) ltac:(lia) ltac:(lia)) as [F V].
  rewrite join_eq, Z.add_0_r in F, V.
  unfold reflection_scale64. rewrite Z.shiftl_mul_pow2 by lia.
  split; [exact F | ].
  assert (E : B (b64_of_bits ((1022-k)*2^52)) = bpow radix2 (-k-1)).
  { rewrite V, Z.add_0_l. replace (IZR (2^52)) with (bpow radix2 52) by reflexivity.
    rewrite <- bpow_plus. f_equal. lia. }
  split; [exact E | ]. rewrite E. split; [apply bpow_gt_0 | ].
  change (/2) with (bpow radix2 (-1)). apply bpow_le. lia.
Qed.

Theorem reflection_scaled_word_ieee x k : finite x -> Rabs (B x) <= 1 -> (0 <= k <= 104)%Z ->
  let y := fmul x (reflection_scale64 k) in
  finite y /\ B y = rndF (B x * bpow radix2 (-k-1)) /\ Rabs (B y) <= 1 /\
  Rabs (B y - B x * bpow radix2 (-k-1)) <= bpow radix2 (-800) /\
  (bpow radix2 (-746) <= Rabs (B x) -> B y = B x * bpow radix2 (-k-1)).
Proof.
  intros Fx X K y. destruct (reflection_scale_ok k K) as [Fk [Bk Scale]].
  assert (P : Rabs (B x * B (reflection_scale64 k)) <= 1).
  { rewrite Rabs_mult, (Rabs_pos_eq (B (reflection_scale64 k))) by lra.
    pose proof (Rabs_pos (B x)). nra. }
  destruct (fmul_ok 1 0 x (reflection_scale64 k) Fx Fk ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; change (bpow radix2 0) with 1; lra)) as [Fy By].
  fold y in Fy, By. rewrite Bk in By.
  assert (Big : bpow radix2 (-746) <= Rabs (B x) -> B y = B x * bpow radix2 (-k-1)).
  { intros Large. rewrite By. apply round_generic; [exact _ | ].
    apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (-745 <= mag radix2 (B x))%Z) by (apply mag_ge_bpow; exact Large).
    unfold emin, prec. lia. }
  assert (Err : Rabs (B y - B x * bpow radix2 (-k-1)) <= bpow radix2 (-800)).
  { destruct (Rle_dec (bpow radix2 (-746)) (Rabs (B x))) as [Large | Small].
    - rewrite (Big Large), Rminus_diag_eq by reflexivity. rewrite Rabs_R0. apply bpow_ge_0.
    - rewrite By. apply (rnd_err_below _ (-746)); [lia | ].
      rewrite Rabs_mult, <- Bk, (Rabs_pos_eq (B (reflection_scale64 k))) by lra.
      pose proof (Rabs_pos (B x)). pose proof (bpow_gt_0 radix2 (-746)). nra. }
  split; [exact Fy | split; [exact By | split; [ | split; assumption]]].
  rewrite By. apply abs_round_le_generic; [exact _ | exact _ | | rewrite <- Bk; exact P].
  change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
Qed.
