(** Doubling a double-word is exact: [mul_f64_64 xh xl 2 = (2 xh, 2 xl)] for a
    double-word number [xh = RN (xh + xl)] with [|xl| <= |xh|], which is what
    the complement's [delta = 2 asin z] relies on. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingCore RoundingTest.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal.
Open Scope R_scope.

Lemma bsc p : (0 <= p)%Z -> bpow radix2 (- p) <= 1.
Proof. intros H. change 1 with (bpow radix2 0). apply bpow_le; lia. Qed.

(** Every binary64 is on the grid [2^-1074]. *)
Lemma binary64_grid x : on_grid (-1074) (B x).
Proof.
  apply (grid_le (cexp radix2 (FLT_exp emin prec) (B x))).
  - unfold cexp, FLT_exp, emin. apply Z.le_trans with (-1074)%Z; [lia | apply Z.le_max_r].
  - apply grid_fmt. apply B_fmt.
Qed.

Lemma double_fmt x : fmtF (B x * bpow radix2 1).
Proof. apply (scaled_fmt_grid (B x) (-1074) 1); [apply B_fmt | apply binary64_grid | lia]. Qed.

Lemma mul2_exact x : finite x -> Rabs (B x) <= bpow radix2 1000 ->
  finite (fmul x asin_two) /\ B (fmul x asin_two) = 2 * B x.
Proof.
  intros Fx Bx. destruct two_val as [V2 F2].
  assert (Hb : bnd 1 1001 (B x * B asin_two)).
  { unfold bnd. rewrite V2. rewrite Rabs_mult, (Rabs_pos_eq 2) by lra.
    assert (bpow radix2 1001 = 2 * bpow radix2 1000).
    { replace 1001%Z with (1000 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
    change (IZR 1) with 1. nra. }
  destruct (fmul_bnd 1 1001 x asin_two Fx F2 ltac:(lia) ltac:(lia) (pow_room 1 (1024 - 1001) ltac:(lia) ltac:(lia)) ltac:(lia) Hb) as [F [E _]].
  split; [exact F | ].
  rewrite E, V2. replace (B x * 2) with (B x * bpow radix2 1) by (change (bpow radix2 1) with 2; ring).
  rewrite round_generic by (try exact _; apply double_fmt). change (bpow radix2 1) with 2. ring.
Qed.

Theorem mul_f64_two_exact xh xl : finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  bpow radix2 (-900) <= B xh -> B xh <= bpow radix2 900 -> Rabs (B xl) <= B xh / 2 ->
  let '(zh, zl) := mul_f64_64 xh xl asin_two in
  finite zh /\ finite zl /\ B zh = 2 * B xh /\ B zl = 2 * B xl.
Proof.
  intros Fh Fl E L U Hl. destruct two_val as [V2 F2].
  assert (Hx0 : 0 < B xh) by (apply Rlt_le_trans with (bpow radix2 (-900)); [apply bpow_gt_0 | exact L]).
  assert (H900 : bpow radix2 900 <= bpow radix2 1000) by (apply bpow_le; lia).
  assert (Hxl1000 : Rabs (B xl) <= bpow radix2 1000) by (pose proof (Rabs_pos (B xl)); lra).
  assert (Hxh1000 : Rabs (B xh) <= bpow radix2 1000) by (rewrite Rabs_pos_eq by lra; lra).
  assert (H901e : bpow radix2 901 = 2 * bpow radix2 900).
  { replace 901%Z with (900 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (H901 : bpow radix2 901 <= bpow radix2 1021) by (apply bpow_le; lia).
  destruct (mul2_exact xl Fl Hxl1000) as [Fc2 Ec2].
  pose proof (Rabs_le_inv _ _ Hl) as [Hla Hlb].
  assert (Hv : B xh / 2 <= B xh + B xl) by lra.
  assert (Hvn : bpow radix2 (-901) <= B xh + B xl).
  { assert (bpow radix2 (-901) = bpow radix2 (-900) / 2).
    { replace (-901)%Z with (-900 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
    lra. }
  assert (Hmag : (-900 <= mag radix2 (B xh + B xl))%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. replace (-900 - 1)%Z with (-901)%Z by reflexivity. exact Hvn. }
  assert (Hscale : rndF ((B xh + B xl) * bpow radix2 1) = B xh * bpow radix2 1).
  { rewrite round_scale; [ | lra | lia | lia]. rewrite <- E. reflexivity. }
  change (bpow radix2 1) with 2 in Hscale.
  assert (Hdbl : rndF (B xh * 2) = 2 * B xh).
  { replace (B xh * 2) with (B xh * bpow radix2 1) by (change (bpow radix2 1) with 2; ring).
    rewrite round_generic by (try exact _; apply double_fmt). change (bpow radix2 1) with 2. ring. }
  assert (HA : Rabs (B xh) <= bpow radix2 900) by (rewrite Rabs_pos_eq by lra; exact U).
  assert (HB : Rabs (B asin_two) <= bpow radix2 1) by (rewrite V2, Rabs_pos_eq by lra; change (bpow radix2 1) with 2; lra).
  assert (Hdom : in_two_prod_domain (B xh) (B asin_two)).
  { right. rewrite V2, Rabs_mult, (Rabs_pos_eq 2) by lra. rewrite (Rabs_pos_eq (B xh)) by lra.
    assert (bpow radix2 (-969) = bpow radix2 (-900) * bpow radix2 (-69))
      by (replace (-969)%Z with (-900 + -69)%Z by reflexivity; rewrite bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 (-900)).
    assert (bpow radix2 (-69) <= 1) by (apply (bsc 69); lia). nra. }
  pose proof (two_prod_ieee 900 1 xh asin_two Fh F2 HA HB ltac:(lia) ltac:(lia) ltac:(lia) Hdom) as TP.
  destruct (two_prod64 xh asin_two) as [p e] eqn:Etp. destruct TP as [Fp [Fe [Ep Esum]]].
  rewrite V2 in Ep, Esum. 
  assert (Bp : B p = 2 * B xh) by (rewrite Ep; exact Hdbl).
  assert (Be : B e = 0) by lra.
  assert (Hp901 : Rabs (B p) <= bpow radix2 1021) by (rewrite Bp, Rabs_pos_eq by lra; lra).
  assert (Hc : Rabs (B (fmul xl asin_two)) <= bpow radix2 1021) by (rewrite Ec2; pose proof (Rabs_le_inv _ _ Hl); apply Rabs_le; lra).
  assert (Hcp : Rabs (B (fmul xl asin_two)) <= Rabs (B p)).
  { rewrite Ec2, Bp, (Rabs_pos_eq (2 * B xh)) by lra. apply Rabs_le; lra. }
  pose proof (fast_two_sum_ieee p (fmul xl asin_two) Fp Fc2 Hp901 Hc (or_intror (or_introl Hcp))) as FS1.
  destruct (fast_two_sum64 p (fmul xl asin_two)) as [th tl1] eqn:Efs1. destruct FS1 as [Fth [Ftl1 [Eth Esum1]]].
  rewrite Bp, Ec2 in Eth, Esum1.
  assert (Bth : B th = 2 * B xh) by (rewrite Eth; replace (2 * B xh + 2 * B xl) with ((B xh + B xl) * 2) by ring; rewrite Hscale; ring).
  assert (Btl1 : B tl1 = 2 * B xl) by lra.
  assert (Hb : bnd 1 1000 (B tl1 + B e)).
  { unfold bnd. rewrite Btl1, Be. change (IZR 1) with 1. rewrite Rmult_1_l. rewrite Rplus_0_r.
    pose proof (Rabs_le_inv _ _ Hl). apply Rabs_le; lra. }
  destruct (fadd_bnd 1 1000 tl1 e Ftl1 Fe ltac:(lia) ltac:(lia) (pow_room 1 (1024 - 1000) ltac:(lia) ltac:(lia)) ltac:(lia) Hb) as [Ftl2 [Etl2 _]].
  assert (Btl2 : B (fadd tl1 e) = 2 * B xl).
  { rewrite Etl2, Btl1, Be, Rplus_0_r. replace (2 * B xl) with (B xl * bpow radix2 1) by (change (bpow radix2 1) with 2; ring).
    rewrite round_generic by (try exact _; apply double_fmt). reflexivity. }
  assert (Hth901 : Rabs (B th) <= bpow radix2 1021) by (rewrite Bth, Rabs_pos_eq by lra; lra).
  assert (Htl2 : Rabs (B (fadd tl1 e)) <= bpow radix2 1021) by (rewrite Btl2; pose proof (Rabs_le_inv _ _ Hl); apply Rabs_le; lra).
  assert (Hthtl : Rabs (B (fadd tl1 e)) <= Rabs (B th)).
  { rewrite Btl2, Bth, (Rabs_pos_eq (2 * B xh)) by lra. apply Rabs_le; lra. }
  pose proof (fast_two_sum_ieee th (fadd tl1 e) Fth Ftl2 Hth901 Htl2 (or_intror (or_introl Hthtl))) as FS2.
  unfold mul_f64_64. rewrite Etp. cbv beta iota. rewrite Efs1. cbv beta iota.
  destruct (fast_two_sum64 th (fadd tl1 e)) as [zh zl] eqn:Efs2. destruct FS2 as [Fzh [Fzl [Ezh Ezsum]]].
  rewrite Bth, Btl2 in Ezh, Ezsum.
  assert (Bzh : B zh = 2 * B xh) by (rewrite Ezh; replace (2 * B xh + 2 * B xl) with ((B xh + B xl) * 2) by ring; rewrite Hscale; ring).
  repeat split; try assumption; lra.
Qed.
