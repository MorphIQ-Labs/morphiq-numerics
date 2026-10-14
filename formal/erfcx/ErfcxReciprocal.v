(** The corrected reciprocal in erfcx/ya_eval, including its IEEE binary64
    operations and the exact-product/subtraction hypotheses of reciprocal.g. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa.
Require erfcx_reciprocal.
Open Scope R_scope.

Definition one : f64 := b64_of_bits 4607182418800017408.
Lemma one_ok : finite one /\ B one = 1.
Proof.
  split.
  - exact (bits_finite 4607182418800017408 false 4503599627370496 (-52) eq_refl).
  - pose proof (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl) as V.
    unfold one. rewrite V. simpl. field.
Qed.

Definition reciprocal64 (x : f64) : f64 * f64 :=
  let yh := fdiv one x in
  let '(p, pe) := two_prod64 x yh in
  (yh, fmul (fsub (fsub one p) pe) yh).

Definition mx x := rn x.
Definition myh x := rn (1 / mx x).
Definition mp x := rn (mx x * myh x).
Definition mpe x := mx x * myh x - mp x.
Definition mr x := rn ((1 - mp x) - mpe x).
Definition myl x := rn (mr x * myh x).

Ltac erfcx_close Hn :=
  let Hb := fresh "Hb" in intros Hb; apply bnd_to in Hb;
  apply Hn; revert Hb; clear; bpow_num_all;
  unfold Float1; simpl; intros [? ?]; lra.
Ltac erfcx_pick Hn :=
  lazymatch goal with
  | |- _ \/ _ => first [left; erfcx_pick Hn | right; erfcx_pick Hn]
  | |- not _ => erfcx_close Hn
  | |- _ -> False => erfcx_close Hn
  | |- _ => hnf; erfcx_pick Hn
  end.
Ltac erfcx_goal lemma :=
  apply NNPP; let Hn := fresh "Hn" in intros Hn;
  apply lemma; gappa_hyps; erfcx_pick Hn.

Lemma reciprocal_bounds x : 16 <= mx x <= 512 ->
  / 512 <= myh x <= / 16 /\ / 2 <= mp x <= 2 /\
  - / 2 ^ 46 <= mpe x <= / 2 ^ 46 /\
  -1 <= mr x <= 1 /\ - / 2 ^ 56 <= myl x <= / 2 ^ 56 /\
  - (257 / 2 ^ 61) <= myl x / myh x <= 257 / 2 ^ 61 /\
  - / 2 ^ 98 <= ((myh x + myl x) - 1 / mx x) / (1 / mx x) <= / 2 ^ 98.
Proof.
  unfold myl, mr, mpe, mp, myh, mx. intros H.
  repeat split; erfcx_goal (erfcx_reciprocal.l1 x).
Qed.

(** The modeled rounded input equals a finite binary64 input exactly. *)
Lemma mx_B x : mx (B x) = B x.
Proof. unfold mx. apply round_generic; [exact _ | apply B_fmt]. Qed.

Theorem reciprocal_ieee x : finite x -> 16 <= B x <= 512 ->
  let '(yh, yl) := reciprocal64 x in
  finite yh /\ finite yl /\
  / 512 <= B yh <= / 16 /\
  - / 2 ^ 56 <= B yl <= / 2 ^ 56 /\
  - (257 / 2 ^ 61) <= B yl / B yh <= 257 / 2 ^ 61 /\
  - / 2 ^ 98 <= ((B yh + B yl) - 1 / B x) / (1 / B x) <= / 2 ^ 98.
Proof.
  intros Fx X. destruct one_ok as [F1 B1].
  assert (Y : / 512 <= 1 / B x <= / 16).
  { unfold Rdiv. rewrite Rmult_1_l. split; apply Rinv_le_contravar; lra. }
  destruct (fdiv_ok 1 0 one x F1 ltac:(lra) ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite B1; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
          apply Rabs_le; lra)) as [Fy By].
  rewrite B1 in By.
  pose proof (reciprocal_bounds (B x) ltac:(rewrite mx_B; exact X)) as C.
  destruct C as [Yh [P [Pe [R [Yl [Ratio Err]]]]]].
  assert (Yh_eq : B (fdiv one x) = myh (B x)).
  { unfold myh. rewrite mx_B. exact By. }
  rewrite <- Yh_eq in Yh.
  pose proof (two_prod_ieee 9 0 x (fdiv one x) Fx Fy
    ltac:(change (bpow radix2 9) with 512; apply Rabs_le; lra)
    ltac:(change (bpow radix2 0) with 1; apply Rabs_le; lra)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite Rabs_pos_eq by nra;
          apply Rle_trans with (bpow radix2 (-5));
          [apply bpow_le; lia | change (bpow radix2 (-5)) with (/32); nra])) as TP.
  unfold reciprocal64. destruct (two_prod64 x (fdiv one x)) as [p pe].
  destruct TP as [Fp [Fpe [Bp Epe]]].
  assert (P_eq : B p = mp (B x)).
  { unfold mp. rewrite mx_B, <- Yh_eq. exact Bp. }
  assert (Pe_eq : B pe = mpe (B x)).
  { unfold mpe. rewrite mx_B, <- Yh_eq, <- P_eq. lra. }
  rewrite <- P_eq in P. rewrite <- Pe_eq in Pe.
  assert (Fmt : fmtF (B one - B p)).
  { apply sterbenz; try exact _. all: try apply B_fmt. rewrite B1; lra. }
  destruct (fsub_ok 1 0 one p F1 Fp ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite B1; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
          apply Rabs_le; lra)) as [Fd Bd].
  rewrite round_generic in Bd by (exact _ || exact Fmt). rewrite B1 in Bd.
  destruct (fsub_ok 2 0 (fsub one p) pe Fd Fpe ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite Bd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
          apply Rabs_le; lra)) as [Fr Br].
  assert (R_eq : B (fsub (fsub one p) pe) = mr (B x)).
  { unfold mr. rewrite <- P_eq, <- Pe_eq. rewrite Br, Bd. reflexivity. }
  rewrite <- R_eq in R.
  destruct (fmul_ok 1 0 (fsub (fsub one p) pe) (fdiv one x) Fr Fy
    ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
          apply Rabs_le; nra)) as [Fl Bl].
  assert (L_eq : B (fmul (fsub (fsub one p) pe) (fdiv one x)) = myl (B x)).
  { unfold myl. rewrite <- R_eq, <- Yh_eq. exact Bl. }
  rewrite <- L_eq in Yl, Ratio, Err. rewrite <- Yh_eq in Ratio. rewrite <- Yh_eq, mx_B in Err.
  repeat split; tauto.
Qed.
