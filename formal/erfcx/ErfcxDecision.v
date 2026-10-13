(** erfcx::decide uses the shared relative-error rounding test. Its encoded
    2^-66 guard accepts a normalized approximation proved within 2^-67. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingTest.
Require Import StageGappa.
Open Scope R_scope.

Definition erfcx_eps : f64 := b64_of_bits 4309944843393564672.
Lemma erfcx_eps_ok : finite erfcx_eps /\ B erfcx_eps = bpow radix2 (-66).
Proof.
  split.
  - exact (bits_finite 4309944843393564672 false 4503599627370496 (-118) eq_refl).
  - pose proof (bits_val 4309944843393564672 false 4503599627370496 118 eq_refl) as V.
    unfold erfcx_eps. rewrite V. bpow_num. simpl. field.
Qed.

Definition erfcx_decide64 h l := decide_with h l erfcx_eps.

Theorem erfcx_decide_ieee h l z v :
  finite h -> finite l -> bpow radix2 (-900) <= Rabs (B h) <= bpow radix2 1000 ->
  B h = rndF (B h+B l) ->
  Rabs (z-(B h+B l)) <= bpow radix2 (-67)*Rabs z ->
  erfcx_decide64 h l = Some v -> v=h /\ B v=rndF z.
Proof.
  intros Fh Fl H Norm Err Decision. destruct erfcx_eps_ok as [Fe Eps].
  destruct (decide_with_ok h l erfcx_eps z (bpow radix2 (-67)) v Fh Fl Fe H Norm)
    as [V Round].
  - split; apply bpow_le; lia.
  - rewrite Eps. split.
    + replace (bpow radix2 (-66)) with (2*bpow radix2 (-67))
        by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
      assert (bpow radix2 (-50) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
      pose proof (bpow_gt_0 radix2 (-67)). nra.
    + change 1 with (bpow radix2 0). apply bpow_le. lia.
  - exact Err.
  - exact Decision.
  - split; [exact V | rewrite V; symmetry; exact Round].
Qed.

Definition erfcx_pow2 e : f64 := b64_of_bits (Z.shiftl (e+1023) 52).
Lemma erfcx_pow2_ok e : (-1022 <= e <= 1023)%Z ->
  finite (erfcx_pow2 e) /\ B (erfcx_pow2 e) = bpow radix2 e.
Proof.
  intros E. destruct (join_val 0 (e+1023) ltac:(lia) ltac:(lia)) as [F V].
  rewrite join_eq, Z.add_0_r in F, V.
  unfold erfcx_pow2. rewrite Z.shiftl_mul_pow2 by lia.
  split; [exact F | ]. rewrite V, Z.add_0_l.
  replace (IZR (2^52)) with (bpow radix2 52) by reflexivity.
  rewrite <- bpow_plus. f_equal. lia.
Qed.

Lemma erfcx_positive_scale_exact h n : finite h -> /2 <= B h -> (0 <= n <= 1023)%Z ->
  B h*bpow radix2 n < bpow radix2 1024 ->
  finite (fmul h (erfcx_pow2 n)) /\ B (fmul h (erfcx_pow2 n)) = B h*bpow radix2 n.
Proof.
  intros Fh H N Ov. destruct (erfcx_pow2_ok n ltac:(lia)) as [Fn Bn].
  assert (Fmt : fmtF (B h*bpow radix2 n)).
  { apply mult_bpow_exact_FLT; [apply B_fmt | ].
    assert (M : (0 <= mag radix2 (B h))%Z).
    { apply mag_ge_bpow. change (bpow radix2 (0-1)) with (/2).
      rewrite Rabs_pos_eq; lra. }
    unfold emin, prec. lia. }
  destruct (fmul_exact h (erfcx_pow2 n) Fh Fn) as [Fy By].
  - rewrite Bn. exact Fmt.
  - rewrite Bn, Rabs_pos_eq; [exact Ov | pose proof (bpow_gt_0 radix2 n); nra].
  - rewrite Bn in By. split; assumption.
Qed.

(** The final scaling branch used by negative erfcx, where [1<=m<=1024].
    The [m=1024] multiplication order matches the Rust implementation. *)
Definition erfcx_scale_normal64 h m :=
  if (1023 <? m)%Z then fmul (fmul h (erfcx_pow2 (m-1023))) (erfcx_pow2 1023)
  else fmul h (erfcx_pow2 m).

Theorem erfcx_scale_normal_ieee h m : finite h -> /2 <= B h <= 4 -> (1 <= m <= 1024)%Z ->
  B h*bpow radix2 m < bpow radix2 1024 ->
  finite (erfcx_scale_normal64 h m) /\ B (erfcx_scale_normal64 h m) = B h*bpow radix2 m.
Proof.
  intros Fh H M Ov. unfold erfcx_scale_normal64.
  destruct (1023 <? m)%Z eqn:Branch.
  - apply Z.ltb_lt in Branch. assert (m=1024)%Z by lia. subst m.
    change (1024-1023)%Z with 1%Z.
    assert (P1 : B h*bpow radix2 1 < bpow radix2 1024).
    { apply Rle_lt_trans with (bpow radix2 3);
        [change (bpow radix2 3) with 8; change (bpow radix2 1) with 2; lra | apply bpow_lt; lia]. }
    destruct (erfcx_positive_scale_exact h 1 Fh ltac:(lra) ltac:(lia) P1) as [F2 B2].
    assert (Id : (B h*bpow radix2 1)*bpow radix2 1023 = B h*bpow radix2 1024)
      by (rewrite Rmult_assoc, <- bpow_plus; reflexivity).
    destruct (erfcx_positive_scale_exact (fmul h (erfcx_pow2 1)) 1023 F2
      ltac:(rewrite B2; change (bpow radix2 1) with 2; lra) ltac:(lia)
      ltac:(rewrite B2, Id; exact Ov)) as [Fv Bv].
    rewrite B2, Id in Bv. split; assumption.
  - apply Z.ltb_ge in Branch. apply erfcx_positive_scale_exact; try assumption; lra || lia.
Qed.

Definition erfcx_decide_scaled_normal64 h l m :=
  match erfcx_decide64 h l with
  | Some v => Some (erfcx_scale_normal64 v m)
  | None => None
  end.

Theorem erfcx_decide_scaled_normal_ieee h l m z v :
  finite h -> finite l -> /2 <= B h <= 4 -> B h = rndF (B h+B l) ->
  Rabs (z-(B h+B l)) <= bpow radix2 (-67)*Rabs z ->
  /4 <= z -> (1 <= m <= 1024)%Z -> B h*bpow radix2 m < bpow radix2 1024 ->
  erfcx_decide_scaled_normal64 h l m = Some v ->
  finite v /\ B v = rndF (z*bpow radix2 m).
Proof.
  intros Fh Fl H Norm Err Z M Ov. unfold erfcx_decide_scaled_normal64.
  destruct (erfcx_decide64 h l) as [r | ] eqn:D; [ | discriminate].
  assert (Hb : bpow radix2 (-900) <= Rabs (B h) <= bpow radix2 1000).
  { rewrite Rabs_pos_eq by lra. split.
    - apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/2); lra].
    - apply Rle_trans with (bpow radix2 2); [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  destruct (erfcx_decide_ieee h l z r Fh Fl Hb Norm Err D) as [R Round]. subst r.
  intros V. injection V as <-.
  destruct (erfcx_scale_normal_ieee h m Fh H M Ov) as [Fv Bv].
  split; [exact Fv | ]. rewrite Bv, Round.
  assert (Mag : (-1 <= mag radix2 z)%Z).
  { apply mag_ge_bpow. change (bpow radix2 (-1-1)) with (/4). rewrite Rabs_pos_eq; lra. }
  symmetry. apply round_scale; lra || lia.
Qed.
