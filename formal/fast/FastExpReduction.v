(** 1024-way bounded exp reduction; all operations are binary64. *)
From Coq Require Import ZArith Reals Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings RoundingConstant.
From Interval Require Import Tactic.
Require Import ExpStageReduction StageGappa FastExpTables.
Open Scope R_scope.
Notation shifter := ExpReduction.shifter.
Definition fast_L : R := ln 2 / 1024.
Lemma fast_L_range : 0.0006769015 <= fast_L <= 0.0006769016.
Proof. unfold fast_L. split; interval with (i_prec 64). Qed.
Lemma fast_l1_eq : B fx_l1 = IZR 1488522236 * bpow radix2 (-41).
Proof. rewrite fx_l1_val. change (-41)%Z with (- Z.of_nat 41)%Z. rewrite bpow_m. field. Qed.
Lemma fast_l1_close : Rabs (fast_L - B fx_l1) <= bpow radix2 (-42).
Proof. unfold fast_L. rewrite fx_l1_val. change (-42)%Z with (- Z.of_nat 42)%Z. rewrite bpow_m. interval with (i_prec 100). Qed.
Definition fast_stage_of (x : f64) : f64 * Z * Z * f64 :=
  let t := fadd (fmul x fx_inv) shifter in
  let n := fsub t shifter in
  let ni := (bits_of_b64 t - bits_of_b64 shifter)%Z in
  (n, Z.land ni 1023, Z.shiftr ni 10, fsub x (fmul n fx_l1)).

Theorem fast_stage_of_ok x : finite x -> Rabs (B x) < 704 ->
  let '(n, j, k, r1) := fast_stage_of x in
  exists ni : Z, B n = IZR ni /\ finite n /\ (Z.abs ni <= 1040035)%Z /\
    ni = (1024 * k + j)%Z /\ (0 <= j < 1024)%Z /\ (-1016 <= k <= 1016)%Z /\
    finite r1 /\ B r1 = B x - IZR ni * B fx_l1 /\
    Rabs (B x - IZR ni * fast_L) <= 0.000338451 /\ Rabs (B r1) < bpow radix2 (-11) /\
    (ni <> 0%Z -> on_grid (-64) (B r1)) /\ (ni = 0%Z -> B r1 = B x).
Proof.
  intros Fx Hx. unfold fast_stage_of.
  pose proof fx_inv_finite as Fi. pose proof fx_l1_finite as F1.
  pose proof fast_L_range as Lr.
  assert (Iv : 1477.3196 <= B fx_inv <= 1477.3198) by (rewrite fx_inv_val; split; lra).
  (* y = RN(x·INV_N) *)
  assert (Xb : Rabs (B x * B fx_inv) <= 1040034).
  { rewrite Rabs_mult, (Rabs_pos_eq (B fx_inv)) by lra. nra. }
  destruct (fmul_ok 1 20 x fx_inv Fx Fi ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (bpow radix2 20) with 1048576; lra)) as [Fy By].
  set (y := fmul x fx_inv) in *.
  assert (Yb : Rabs (B y) <= bpow radix2 50).
  { rewrite By. apply Rle_trans with (IZR 1 * bpow radix2 20).
    - apply bnd_round; [lia | lia | unfold bnd; change (bpow radix2 20) with 1048576; lra].
    - change (bpow radix2 20) with 1048576. change (bpow radix2 50) with 1125899906842624. lra. }
  destruct (shifter_add y Fy Yb) as [Ft Bt].
  set (t := fadd y shifter) in *.
  set (ni := Znearest ne (B y)) in *.
  assert (Hk : Rabs (B y - IZR ni) <= / 2) by (unfold ni; apply Znearest_half).
  pose proof (ExpReduction.rnd_abs_err (B x * B fx_inv)) as Ey. rewrite <- By in Ey.
  change (bpow radix2 (-1074)) with (/ 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)%R in Ey.
  (* |x/fast_L − ni| <= 1/2 + 2^-31 *)
  assert (Ic : Rabs (B fx_inv - / fast_L) <= / 2 ^ 41).
  { replace (/ fast_L) with (1024 / ln 2) by (unfold fast_L; field; interval with (i_prec 64)).
    exact fx_inv_close. }
  assert (XL : Rabs (B x / fast_L - IZR ni) <= / 2 + / 2147483648).
  { replace (B x / fast_L - IZR ni) with (B x * (/ fast_L - B fx_inv) + (B x * B fx_inv - B y) + (B y - IZR ni))
      by (unfold Rdiv; ring).
    assert (A1 : Rabs (B x * (/ fast_L - B fx_inv)) <= 704 * / 2 ^ 41).
    { rewrite Rabs_mult, Rabs_minus_sym. apply Rmult_le_compat; try apply Rabs_pos; lra. }
    assert (A2 : Rabs (B x * B fx_inv - B y) <= / 9007199254740992 * 1040034 + / 1000000000000).
    { rewrite Rabs_minus_sym. apply Rle_trans with (1 := Ey).
      assert (/ 9007199254740992 * Rabs (B x * B fx_inv) <= / 9007199254740992 * 1040034) by lra.
      pose proof (Rinv_0_lt_compat 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784 ltac:(lra)).
      lra. }
    assert (P41 : / 2 ^ 41 = / 2199023255552) by (simpl; lra).
    rewrite P41 in A1.
    eapply Rle_trans; [apply Rabs_triang | ]. eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ]. lra. }
  assert (Ni : (Z.abs ni <= 1040035)%Z).
  { assert (A : Rabs (B x / fast_L) <= 1040034).
    { unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ fast_L)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
      apply Rle_trans with (704 * / 0.0006769015).
      - apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
        apply Rinv_le_contravar; lra.
      - interval with (i_prec 64). }
    assert (T : Rabs (IZR ni - B x / fast_L + B x / fast_L) <= Rabs (IZR ni - B x / fast_L) + Rabs (B x / fast_L))
      by apply Rabs_triang.
    replace (IZR ni - B x / fast_L + B x / fast_L) with (IZR ni) in T by ring.
    rewrite Rabs_minus_sym in T.
    assert (Rabs (IZR ni) <= 1040035) by lra.
    rewrite <- abs_IZR in H. apply le_IZR in H. lia. }
  (* n = t − SHIFTER *)
  destruct ExpReduction.shifter_value as [Bs Fs].
  assert (Hd : bnd 1 53 (B t - B shifter)).
  { unfold bnd. rewrite Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    rewrite <- abs_IZR. replace (IZR 1 * bpow radix2 53) with (IZR (2 ^ 53)) by (simpl; ring). apply IZR_le. lia. }
  destruct (fsub_ok 1 53 t shifter Ft Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fn Bn].
  assert (Bn' : B (fsub t shifter) = IZR ni).
  { rewrite Bn, Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    apply round_generic; auto with typeclass_instances.
    replace (IZR ni) with (IZR ni * bpow radix2 0) by (change (bpow radix2 0) with 1; ring).
    apply ExpReduction.fmt_int; lia. }
  set (n := fsub t shifter) in *.
  assert (Bits : (bits_of_b64 t - bits_of_b64 shifter)%Z = ni).
  { rewrite (shifted_bits t ni Ft Bt ltac:(lia)), shifter_bits. ring. }
  rewrite Bits.
  (* j and k *)
  assert (Jk : Z.land ni 1023 = (ni mod 1024)%Z /\ Z.shiftr ni 10 = (ni / 1024)%Z).
  { split; [change 1023%Z with (Z.ones 10); rewrite Z.land_ones by lia; reflexivity
           | rewrite Z.shiftr_div_pow2 by lia; reflexivity]. }
  destruct Jk as [J K]. rewrite J, K.
  pose proof (Z.div_mod ni 1024 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ni 1024 ltac:(lia)) as MB.
  (* r1 = x − ni·L1, exact *)
  assert (P1 : B n * B fx_l1 = IZR (ni * 1488522236) * bpow radix2 (-41)).
  { rewrite Bn', fast_l1_eq, mult_IZR. ring. }
  assert (P1f : fmtF (B n * B fx_l1)).
  { rewrite P1. apply ExpReduction.fmt_int; [ | lia]. rewrite Z.abs_mul. change (2 ^ 53)%Z with 9007199254740992%Z. lia. }
  assert (P1b : Rabs (B n * B fx_l1) <= 1024).
  { assert (C : 0 <= B fx_l1 <= 0.000677) by (rewrite fx_l1_val; split; interval with (i_prec 64)).
    rewrite Bn', Rabs_mult, <- abs_IZR. rewrite (Rabs_pos_eq (B fx_l1)) by (destruct C; assumption).
    assert (0 <= IZR (Z.abs ni) <= 1040035) by (split; apply IZR_le; lia). nra. }
  destruct (fmul_ok 1 10 n fx_l1 Fn F1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (bpow radix2 10) with 1024; lra)) as [Fm1 Bm1].
  assert (Em1 : B (fmul n fx_l1) = IZR ni * B fx_l1).
  { rewrite Bm1, round_generic by (auto with typeclass_instances || exact P1f). rewrite Bn'. reflexivity. }
  set (R := B x - IZR ni * fast_L).
  assert (HR : Rabs R <= 0.000338451).
  { replace R with (fast_L * (B x / fast_L - IZR ni)) by (unfold R; field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq fast_L) by lra.
    apply Rle_trans with (0.0006769016 * (/ 2 + / 2147483648)); [ | lra].
    apply Rmult_le_compat; try lra. apply Rabs_pos. }
  assert (Dr : Rabs (B x - IZR ni * B fx_l1) < bpow radix2 (-11)).
  { replace (B x - IZR ni * B fx_l1) with (R + IZR ni * (fast_L - B fx_l1)) by (unfold R; ring).
    pose proof fast_l1_close as C. change (bpow radix2 (-42)) with (/ 4398046511104) in C.
    change (bpow radix2 (-11)) with (/ 2048).
    apply Rle_lt_trans with (Rabs R + Rabs (IZR ni) * Rabs (fast_L - B fx_l1)).
    - rewrite <- Rabs_mult. apply Rabs_triang.
    - assert (Rabs (IZR ni) <= 1040035) by (rewrite <- abs_IZR; apply IZR_le; lia).
      assert (Rabs (IZR ni) * Rabs (fast_L - B fx_l1) <= 1040035 * / 4398046511104)
        by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
      lra. }
  (* the grids, when ni <> 0: |x| >= 2^-12 *)
  assert (Big : ni <> 0%Z -> bpow radix2 (-12) <= Rabs (B x)).
  { intros N0. assert (K1 : 1 <= Rabs (IZR ni)) by (rewrite <- abs_IZR; apply IZR_le; lia).
    assert (Q : Rabs (B x / fast_L) >= / 2 - / 2147483648).
    { pose proof (Rabs_triang_inv (IZR ni) (IZR ni - B x / fast_L)) as T.
      replace (IZR ni - (IZR ni - B x / fast_L)) with (B x / fast_L) in T by ring.
      rewrite Rabs_minus_sym in T. lra. }
    replace (B x) with (fast_L * (B x / fast_L)) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq fast_L) by lra.
    change (bpow radix2 (-12)) with (/ 4096). nra. }
  assert (Gr : ni <> 0%Z -> on_grid (-64) (B x - IZR ni * B fx_l1)).
  { intros N0. apply grid_minus.
    - apply (grid_fmt_bound (FLT_exp emin prec) (-12)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | right; exact (Big N0)].
    - apply grid_le with (-41)%Z; [lia | ]. rewrite fast_l1_eq. exists (ni * 1488522236)%Z. rewrite mult_IZR. ring. }
  assert (Fr : fmtF (B x - IZR ni * B fx_l1)).
  { destruct (Z.eq_dec ni 0) as [Z0 | N0].
    - rewrite Z0, Rmult_0_l, Rminus_0_r. apply B_fmt.
    - apply (grid_fmt_small (-64)); [lia | exact (Gr N0) | exact Dr]. }
  destruct (fsub_ok 1 0 x (fmul n fx_l1) Fx Fm1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; rewrite Em1; change (bpow radix2 0) with 1;
                    change (bpow radix2 (-11)) with (/ 2048) in Dr; lra)) as [Fr1 Br1].
  assert (Er1 : B (fsub x (fmul n fx_l1)) = B x - IZR ni * B fx_l1)
    by (rewrite Br1, Em1; apply round_generic; [auto with typeclass_instances | exact Fr]).
  exists ni. rewrite Er1.
  split; [exact Bn' | split; [exact Fn | split; [exact Ni | split; [lia | split; [lia | split; [lia | ]]]]]].
  split; [exact Fr1 | split; [reflexivity | split; [exact HR | split; [exact Dr | split; [exact Gr | ]]]]].
  intros Z0. rewrite Z0, Rmult_0_l, Rminus_0_r. reflexivity.
Qed.

Theorem fast_stage_r_ok n r1 (ni : Z) (X : R) :
  finite n -> B n = IZR ni -> (Z.abs ni <= 1040035)%Z -> finite r1 ->
  B r1 = X - IZR ni * B fx_l1 -> Rabs (X - IZR ni * fast_L) <= 0.000338451 -> Rabs (B r1) < bpow radix2 (-11) ->
  finite (fsub r1 (fmul n fx_l2d)) /\
  B (fsub r1 (fmul n fx_l2d)) = rn (B r1 - B (fmul n fx_l2d)) /\
  Rabs (B r1 - B (fmul n fx_l2d) - (X - IZR ni * fast_L)) <= bpow radix2 (-77).
Proof.
  intros Fn Bn Hn Fr1 Br1 HR Hr1.
  assert (C : Rabs (B fx_l2d) <= / 1000000000000) by (rewrite fx_l2d_val; interval with (i_prec 64)).
  assert (Ni : Rabs (IZR ni) <= 1040035) by (rewrite <- abs_IZR; apply IZR_le; lia).
  assert (Pm : Rabs (B n * B fx_l2d) <= 16).
  { rewrite Bn, Rabs_mult. apply Rle_trans with (1040035 * / 1000000000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fmul16 n fx_l2d Fn fx_l2d_finite Pm) as [Fp Bp].
  assert (Pb : Rabs (B (fmul n fx_l2d)) <= 1).
  { rewrite Bp. apply abs_round_le_generic; auto with typeclass_instances.
    - change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - rewrite Bn, Rabs_mult. apply Rle_trans with (1040035 * / 1000000000000); [ | lra].
      apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  change (bpow radix2 (-11)) with (/ 2048) in Hr1.
  destruct (fsub16 r1 (fmul n fx_l2d) Fr1 Fp) as [Fr Br].
  { apply Rle_trans with (Rabs (B r1) + Rabs (B (fmul n fx_l2d))); [ | lra].
    unfold Rminus. rewrite <- (Rabs_Ropp (B (fmul n fx_l2d))). apply Rabs_triang. }
  split; [exact Fr | split; [exact Br | ]].
  assert (Split : Rabs (fast_L-B fx_l1-B fx_l2d)<=bpow radix2 (-99)).
  { replace (fast_L-B fx_l1-B fx_l2d) with (-(B fx_l1+B fx_l2d-ln 2/1024)) by (unfold fast_L;ring).
    rewrite Rabs_Ropp. change (-99)%Z with (-Z.of_nat 99)%Z. rewrite bpow_m. exact fx_l_split_d. }
  assert (Csmall : Rabs (B fx_l2d)<=0.0000000000000411) by (rewrite fx_l2d_val;interval).
  assert (Psmall : Rabs (B n*B fx_l2d)<=1040035*0.0000000000000411).
  { rewrite Bn,Rabs_mult. apply Rmult_le_compat;try apply Rabs_pos;assumption. }
  pose proof (ExpReduction.rnd_abs_err (B n*B fx_l2d)) as Err.
  assert (Tiny : bpow radix2 (-1074)<=bpow radix2 (-100)) by (apply bpow_le;lia).
  assert (ErrSmall : Rabs (rn(B n*B fx_l2d)-B n*B fx_l2d)<=
    bpow radix2 (-53)*(1040035*0.0000000000000411)+bpow radix2 (-100)).
  { eapply Rle_trans;[exact Err|]. change (bpow radix2 (-53)) with (/9007199254740992). pose proof (bpow_gt_0 radix2 (-1074));nra. }
  change (B(fmul n fx_l2d)=rn(B n*B fx_l2d)) in Bp.
  rewrite <-Bp in ErrSmall.
  replace (B r1-B(fmul n fx_l2d)-(X-IZR ni*fast_L)) with
    (IZR ni*(fast_L-B fx_l1-B fx_l2d)+(B n*B fx_l2d-B(fmul n fx_l2d))) by (rewrite Br1,Bn;ring).
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult, (Rabs_minus_sym (B n*B fx_l2d) (B(fmul n fx_l2d))).
  assert (S : Rabs(IZR ni)*Rabs(fast_L-B fx_l1-B fx_l2d)<=1040035*bpow radix2 (-99)).
  { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
  bpow_num_all;lra.
Qed.

Lemma fast_table_facts j : (j < 1024)%nat ->
  finite (fx_t_hi j) /\ finite (fx_t_lo j) /\ 1 <= B (fx_t_hi j) <= 2 /\
  Rabs (B (fx_t_lo j)) <= bpow radix2 (-53) /\
  Rabs (B (fx_t_hi j) + B (fx_t_lo j) - exp (INR j * ln 2 / 1024)) <= bpow radix2 (-104).
Proof.
  intros Hj. destruct (fx_t_ok j Hj) as [Fh [Fl [_ [_ [_ [Th [Tl D]]]]]]].
  unfold fx_t_hi, fx_t_lo. repeat split; try assumption; try lra.
  change (-53)%Z with (- Z.of_nat 53)%Z. rewrite bpow_m. exact Tl.
Qed.

Lemma fast_exp_split k j R :
  exp (IZR (1024 * k + Z.of_nat j) * fast_L + R) = exp (INR j * ln 2 / 1024) * exp R * bpow radix2 k.
Proof.
  rewrite bpow_powerRZ, powerRZ_Rpower by (simpl; lra). unfold Rpower, fast_L.
  rewrite <- !exp_plus. f_equal.
  rewrite plus_IZR, mult_IZR, INR_IZR_INZ. simpl (IZR radix2). field.
Qed.

