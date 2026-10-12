(** Natural logarithm reciprocal stage: binary64 evaluation and rounding margin. *)
From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings RoundingTest RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pCertificates Ln1pApprox Ln1pLemmas.
Import ListNotations.

Open Scope R_scope.

Require Import Ln1pStageH Ln1pStageB LnComposition.
Require LnReduction.

(** The reciprocal reduction is shared with ln_1p. E is the total exponent,
    including the exponent returned by that reduction. *)
Definition ln_parts (E : Z) (h : f64) : f64 * f64 * f64 :=
  let i := rd_i (bits_of_b64 h) in
  let z := rd_z h in
  let ln1 := fadd (fmul (of_int E) st_l1) (st_th i) in
  let ln0 := fadd (fmul (of_int E) st_l0) (st_tl i) in
  let z2 := fmul z z in
  let t0 := fsub (fmul z (st_hc 0)) c_half in
  let t1 := fadd (fmul z (st_hc 2)) (st_hc 1) in
  let a1 := fadd (fmul z2 (st_hc 3)) t1 in
  let p := fadd (fmul z2 a1) t0 in
  let q := fmul z2 p in
  let s := fadd ln1 z in
  let e1 := fsub z (fsub s ln1) in
  let pre := fadd e1 ln0 in
  let lo := fadd pre q in
  let eps := fadd (fmul z2 c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah) in
  (s, lo, eps).

Theorem ln_eval E h : finite h -> bpow radix2 (-53) <= B h <= bpow radix2 1020 ->
  (-1100 <= E <= 1100)%Z ->
  (E = 0%Z -> B h * bpow radix2 (- rd_e (bits_of_b64 h)) <> 1) ->
  let v := IZR E * ln 2 + ln (B h * bpow radix2 (- rd_e (bits_of_b64 h))) in
  let '(s, lo, eps) := ln_parts E h in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - v) <= / 2 ^ 123 * Rabs v ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fh Hr HE Hne. cbv zeta.
  pose proof (Ln1pReduction.reduce_ok h Fh Hr) as RD. cbv zeta in RD.
  unfold ln_parts. cbv zeta.
  set (hb := bits_of_b64 h) in *. set (re := rd_e hb) in *. set (i := rd_i hb) in *.
  set (rs := rd_rs hb) in *. set (z := rd_z h) in *.
  destruct RD as [Er [Hi [RR [Yr [Yi [Frs [Brs [Fz [Bz [Zg [[zi [Zi [Zz [Zn Zf]]]] [Fth [Ftl [Gth [Ttl [Tth Terr]]]]]]]]]]]]]]]].
  set (R := B (st_r i)) in *. set (y := B h * bpow radix2 (- re)) in *.
  pose proof (bpow_gt_0 radix2 (-53)) as Pu.
  assert (U53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (Small : forall v, Rabs v <= 4096 -> Rabs v <= bpow radix2 1000).
  { intros v Hv. apply Rle_trans with 4096; [exact Hv | change 4096 with (bpow radix2 12); apply bpow_le; lia]. }
  pose proof (l_check_ok st_bounds st_l1_bits st_l0_bits st_el_bits st_l_check) as LO.
  destruct LO as [FL1 [FL0 [GL1 [[L1p L1u] [L0b [Lerr _]]]]]].
  fold st_l1 in FL1, GL1, L1p, L1u, Lerr. fold st_l0 in FL0, L0b, Lerr.
  assert (Db : forall d, dval d = IZR (fst d) * bpow radix2 (snd d)) by reflexivity.
  cbn [st_bounds b_l0_max b_l_err b_tl_max b_th_max b_t_err b_s_min] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  rewrite !Db in L0b, Lerr, Ttl, Tth, Terr, Zf. cbn [fst snd] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  bpow_num_in L0b. bpow_num_in Lerr. bpow_num_in Ttl. bpow_num_in Tth. bpow_num_in Terr. bpow_num_in Zf.
  assert (Ln2 : 0.69314718055 <= ln 2 <= 0.69314718056) by (split; interval with (i_prec 64)).
  assert (L1lo : 0.6931 <= B st_l1) by (apply Rabs_le_inv in Lerr; apply Rabs_le_inv in L0b; lra).
  assert (EI : Rabs (IZR E) <= 1100) by (rewrite <- abs_IZR; apply IZR_le; lia).
  destruct (of_int_ok E ltac:(lia)) as [Fe Ve].
  assert (L1hi : B st_l1 <= 0.7) by (apply Rabs_le_inv in Lerr; apply Rabs_le_inv in L0b; lra).
  assert (GE : on_grid 0 (IZR E)) by (exists E; simpl; ring).
  assert (Ae : Rabs (IZR E * B st_l1) <= 770).
  { rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) by lra.
    apply Rle_trans with (1100 * 0.7); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fmul_s (of_int E) st_l1 Fe FL1) as [Feh Veh].
  { apply Small. rewrite Ve. lra. }
  rewrite Ve, exact_round in Veh.
  2: { apply (grid_repr (-43)); [lia | | change (bpow radix2 (-43 + 53)) with 1024; lra].
       replace (-43)%Z with (0 + -43)%Z by reflexivity. apply grid_mult; assumption. }
  destruct (fmul_s (of_int E) st_l0 Fe FL0) as [Fel Vel0].
  { apply Small. rewrite Ve, Rabs_mult. apply Rle_trans with (1100 * / 17592186044416);
      [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  rewrite Ve in Vel0.
  assert (Vel : Rabs (B (fmul (of_int E) st_l0) - IZR E * B st_l0) <= / 2 ^ 53 * Rabs (IZR E * B st_l0)).
  { rewrite Vel0. destruct (Z.eq_dec E 0) as [E0 | En].
    - rewrite E0, Rmult_0_l, round_0, Rminus_0_r, Rabs_R0, Rmult_0_r by exact _. lra.
    - rewrite <- (bpow_m 53). apply rnd_rel.
      assert (El : 1 <= Rabs (IZR E)) by (rewrite <- abs_IZR; apply IZR_le; lia).
      assert (L0min : bpow radix2 (-100) <= Rabs (B st_l0)).
      { change (bpow radix2 (-100) <= Rabs (IZR 8711806768342832 * bpow radix2 (-97))). bpow_num. rewrite Rabs_pos_eq by lra. lra. }
      apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | ].
      rewrite Rabs_mult. replace (bpow radix2 (-100)) with (1 * bpow radix2 (-100)) at 1 by ring.
      apply Rmult_le_compat; [lra | apply bpow_ge_0 | exact El | exact L0min]. }
  (* ln1 = E L1 + TH, exactly *)
  assert (Gln1 : on_grid (-43) (B (fmul (of_int E) st_l1) + B (st_th i))).
  { rewrite Veh. apply grid_plus; [ | exact Gth]. replace (-43)%Z with (0 + -43)%Z by reflexivity. apply grid_mult; assumption. }
  assert (Ab1 : Rabs (B (fmul (of_int E) st_l1) + B (st_th i)) <= 771).
  { rewrite Veh. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) by lra.
    assert (Rabs (IZR E) * B st_l1 <= 1100 * 0.7) by (apply Rmult_le_compat; try lra; apply Rabs_pos). lra. }
  destruct (fadd_s (fmul (of_int E) st_l1) (st_th i) Feh Fth (Small (B (fmul (of_int E) st_l1) + B (st_th i)) ltac:(lra))) as [Fln1 Bln1].
  rewrite exact_round in Bln1.
  2: { apply (grid_repr (-43)); [lia | exact Gln1 | ]. apply Rle_lt_trans with 771; [exact Ab1 | change (bpow radix2 (-43 + 53)) with 1024; lra]. }
  rewrite Veh in Bln1.
  set (ln1 := fadd (fmul (of_int E) st_l1) (st_th i)) in *.
  (* ln0 = (el + tl)(1 + d0) *)
  destruct (rnd_sum_rel (B (fmul (of_int E) st_l0)) (B (st_tl i)) (B_fmt _) (B_fmt _)) as [d0 [Hd0 Ed0]].
  assert (Abel : Rabs (B (fmul (of_int E) st_l0)) <= / 2 ^ 32).
  { apply Rabs_le_inv in Vel as ?. assert (Rabs (IZR E * B st_l0) <= 1100 * / 17592186044416)
      by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; [exact EI | lra]).
    pose proof (Rabs_triang_inv (B (fmul (of_int E) st_l0)) (IZR E * B st_l0)).
    assert (/ 2 ^ 53 * Rabs (IZR E * B st_l0) <= Rabs (IZR E * B st_l0)) by (pose proof (Rabs_pos (IZR E * B st_l0)); assert (0 < / 2 ^ 53 <= 1) by (split; [apply Rinv_0_lt_compat, pow_lt; lra | rewrite <- Rinv_1; apply Rinv_le_contravar; [lra | apply pow_R1_Rle; lra]]); nra).
    assert (2 * 1100 * / 17592186044416 <= / 2 ^ 32) by (simpl; lra). lra. }
  destruct (fadd_s (fmul (of_int E) st_l0) (st_tl i) Fel Ftl) as [Fln0 Bln0].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). assert (/ 2 ^ 32 <= 1) by (simpl; lra). lra. }
  rewrite Ed0 in Bln0.
  set (ln0 := fadd (fmul (of_int E) st_l0) (st_tl i)) in *.
  assert (One : fmtF 1) by (apply (fmt_pow 0); lia).
  assert (Zb : Rabs (B z) <= / 512) by (apply Rle_trans with zi; [exact Zz | apply Rle_trans with (1 := Zi); simpl; lra]).
  apply Rabs_le_inv in Zb as Zb'.
  assert (Hzr : IZR (-1) * bpow radix2 (-9) <= B z <= IZR 1 * bpow radix2 (-9)) by (bpow_num; lra).
  (* the polynomial: q = h_q z *)
  destruct st_h3_ok as [Fh3 Bh3]. destruct st_h4_ok as [Fh4 Bh4]. destruct st_h5_ok as [Fh5 Bh5].
  destruct st_h6_ok as [Fh6 Bh6]. destruct c_half_ok as [Fhf Bhf].
  assert (Hh : Rabs h3 <= 1 /\ Rabs h4 <= 1 /\ Rabs h5 <= 1 /\ Rabs h6 <= 1).
  { unfold h3, h4, h5, h6. bpow_num. repeat split; apply Rabs_le; lra. }
  destruct Hh as [Ah3 [Ah4 [Ah5 Ah6]]].
  assert (Pr : forall a b, Rabs a <= 1 -> Rabs b <= 1 -> Rabs (a * b) <= 1)
    by (intros a b Ha Hb; rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]).
  assert (Az : Rabs (B z) <= 1) by lra.
  destruct (fmul_s z z Fz Fz) as [Fz2 Bz2]; [apply Small; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Az2 : Rabs (B (fmul z z)) <= 1) by (rewrite Bz2; apply rnd_bound; [exact One | apply Pr; lra]).
  destruct (fmul_s z (st_hc 0) Fz Fh3) as [Fm0 Bm0]; [apply Small; rewrite Bh3; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am0 : Rabs (B (fmul z (st_hc 0))) <= 1) by (rewrite Bm0, Bh3; apply rnd_bound; [exact One | apply Pr; lra]).
  destruct (fsub_s (fmul z (st_hc 0)) c_half Fm0 Fhf) as [Ft0 Bt0].
  { apply Small. rewrite Bhf. change (bpow radix2 (-1)) with (/ 2). apply Rabs_le_inv in Am0. apply Rabs_le. lra. }
  assert (At0 : Rabs (B (fsub (fmul z (st_hc 0)) c_half)) <= 2).
  { rewrite Bt0, Bhf. apply rnd_bound; [apply (fmt_pow 1); lia | ]. change (bpow radix2 1) with 2. change (bpow radix2 (-1)) with (/ 2).
    apply Rabs_le_inv in Am0. apply Rabs_le. lra. }
  destruct (fmul_s z (st_hc 2) Fz Fh5) as [Fm2 Bm2]; [apply Small; rewrite Bh5; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am2 : Rabs (B (fmul z (st_hc 2))) <= / 512).
  { rewrite Bm2, Bh5. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512).
    rewrite Rabs_mult. apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fadd_s (fmul z (st_hc 2)) (st_hc 1) Fm2 Fh4) as [Ft1 Bt1].
  { apply Small. rewrite Bh4. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  assert (Ah4' : Rabs h4 <= / 2) by (unfold h4; bpow_num; apply Rabs_le; lra).
  assert (At1 : Rabs (B (fadd (fmul z (st_hc 2)) (st_hc 1))) <= 1).
  { rewrite Bt1, Bh4. apply rnd_bound; [exact One | ]. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul_s (fmul z z) (st_hc 3) Fz2 Fh6) as [Fm3 Bm3]; [apply Small; rewrite Bh6; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am3 : Rabs (B (fmul (fmul z z) (st_hc 3))) <= / 512).
  { rewrite Bm3, Bh6. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512).
    rewrite Bz2. assert (Rabs (rndF (B z * B z)) <= / 512).
    { apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512). rewrite Rabs_mult.
      apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
    rewrite Rabs_mult. apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fadd_s (fmul (fmul z z) (st_hc 3)) (fadd (fmul z (st_hc 2)) (st_hc 1)) Fm3 Ft1) as [Fa1 Ba1].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (a1 := fadd (fmul (fmul z z) (st_hc 3)) (fadd (fmul z (st_hc 2)) (st_hc 1))) in *.
  assert (Aa1 : Rabs (B a1) <= 2).
  { rewrite Ba1. apply rnd_bound; [apply (fmt_pow 1); lia | ]. change (bpow radix2 1) with 2.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  assert (Az2' : Rabs (B (fmul z z)) <= / 512).
  { rewrite Bz2. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512). rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fmul_s (fmul z z) a1 Fz2 Fa1) as [Fm4 Bm4].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 2); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  assert (Am4 : Rabs (B (fmul (fmul z z) a1)) <= 1).
  { rewrite Bm4. apply rnd_bound; [exact One | ]. rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 2); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  set (t0 := fsub (fmul z (st_hc 0)) c_half) in *.
  destruct (fadd_s (fmul (fmul z z) a1) t0 Fm4 Ft0) as [Fp Bp].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (p := fadd (fmul (fmul z z) a1) t0) in *.
  assert (Ap : Rabs (B p) <= 4).
  { rewrite Bp. apply rnd_bound; [apply (fmt_pow 2); lia | ]. change (bpow radix2 2) with 4.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul_s (fmul z z) p Fz2 Fp) as [Fq Bq].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 4); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  set (q := fmul (fmul z z) p) in *.
  assert (Aq : Rabs (B q) <= 1).
  { rewrite Bq. apply rnd_bound; [exact One | ]. rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 4); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  (* q is the certificate's h_q *)
  assert (Eq : B q = h_q (B z)).
  { rewrite Bq, Bp, Bm4, Ba1, Bt1, Bt0, Bm3, Bm2, Bm0, Bz2, Bh3, Bh4, Bh5, Bh6, Bhf.
    unfold h_q, h_p. cbv zeta.
    change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
    rewrite Rmult_1_l. reflexivity. }
  (* s = RN(ln1 + z) and e1, by Fast2Sum *)
  assert (Th1 : Rabs (B (st_th i)) <= 711 / 2048) by lra.
  assert (CaseE : (E = 0)%Z \/ 1 <= Rabs (IZR E)).
  { destruct (Z.eq_dec E 0) as [E0 | E0]; [left; exact E0 | right; rewrite <- abs_IZR; apply IZR_le; lia]. }
  assert (Smin : / 512 <= 1) by lra.
  assert (BigE : 1 <= Rabs (IZR E) -> 3439 / 10000 * Rabs (IZR E) <= Rabs (B ln1 + B z)).
  { intros HE1. rewrite Bln1. pose proof (Rabs_triang_inv (IZR E * B st_l1) (- (B (st_th i) + B z))) as T.
    replace (IZR E * B st_l1 - - (B (st_th i) + B z)) with (IZR E * B st_l1 + B (st_th i) + B z) in T by ring.
    rewrite Rabs_Ropp in T. rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) in T by lra.
    assert (Rabs (B (st_th i) + B z) <= 711 / 2048 + / 512) by (apply Rle_trans with (1 := Rabs_triang _ _); lra).
    assert (Rabs (IZR E) * B st_l1 >= Rabs (IZR E) * 0.6931) by (apply Rle_ge, Rmult_le_compat_l; [apply Rabs_pos | lra]).
    nra. }
  assert (Pre : B ln1 = 0 \/ Rabs (B z) <= Rabs (B ln1)).
  { destruct CaseE as [E0 | HE1].
    - rewrite E0, Rmult_0_l, Rplus_0_l in Bln1.
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + left. rewrite Bln1. exact (proj1 (Zn eq_refl)).
      + right. rewrite Bln1. specialize (Zf eq_refl). lra.
    - right. pose proof (BigE HE1) as BE. pose proof (Rabs_triang_inv (B ln1 + B z) (B z)) as T.
      replace (B ln1 + B z - B z) with (B ln1) in T by ring. clear - T BE HE1 Zb. nra. }
  pose proof (fast_two_sum_ieee ln1 z Fln1 Fz
               ltac:(apply Rle_trans with 1024; [rewrite Bln1, <- Veh; lra | change 1024 with (bpow radix2 10); apply bpow_le; lia])
               ltac:(apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(destruct Pre as [P | P]; [left; exact P | right; left; exact P])) as FT.
  unfold fast_two_sum64 in FT. cbv beta iota zeta in FT. destruct FT as [Fs [Fe1 [Bs Se1]]].
  set (s := fadd ln1 z) in *. set (e1 := fsub z (fsub s ln1)) in *.
  (* |s| from below, and the ratios tau = T1/s and kap = ln0/s *)
  set (T1 := IZR E * ln 2 - ln R - B ln1 - (B (fmul (of_int E) st_l0) + B (st_tl i))).
  assert (Rp : 0 < R) by lra.
  assert (El0 : (E = 0)%Z -> B (fmul (of_int E) st_l0) = 0).
  { intros E0. rewrite Vel0, E0, Rmult_0_l. apply round_0; exact _. }
  assert (Sfmt : forall c, fmtF c -> c <= Rabs (B ln1 + B z) -> c <= Rabs (B s)).
  { intros c Fc Hc. rewrite Bs. apply abs_round_ge_generic; [exact _ | exact _ | exact Fc | exact Hc]. }
  pose proof (rnd_sum_err (B ln1) (B z) (B_fmt _) (B_fmt _)) as Rs. rewrite <- Bs in Rs.
  assert (Ttl' : Rabs (B (st_tl i)) <= / 17592186044416) by lra.
  assert (Terr' : Rabs (B (st_th i) + B (st_tl i) + ln R) <= / 158456325028528675187087900672) by lra.
  assert (Lerr' : Rabs (B st_l1 + B st_l0 - ln 2) <= / 2535301200456458802993406410752) by lra.
  assert (L0b' : Rabs (B st_l0) <= / 17592186044416) by lra.
  assert (Su : bpow radix2 (-62) <= Rabs (B s) /\
               Rabs T1 <= IZR 183 * bpow radix2 (-94) * Rabs (B s) /\
               Rabs (B ln0) <= IZR 183 * bpow radix2 (-41) * Rabs (B s)).
  { destruct CaseE as [E0 | HE1].
    - assert (Ln1t : B ln1 = B (st_th i)) by (rewrite Bln1, E0, Rmult_0_l, Rplus_0_l; reflexivity).
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + destruct (Zn eq_refl) as [Th0 [Tl0 R1]].
        assert (Ln10 : B ln1 = 0) by (rewrite Ln1t; exact Th0).
        assert (Sz : B s = B z) by (rewrite Bs, Ln10, Rplus_0_l; apply exact_round, B_fmt).
        assert (Nz : B z <> 0).
        { intros Z0. apply (Hne E0). rewrite Bz in Z0. fold R in R1. rewrite R1 in Z0. lra. }
        destruct Zg as [Z0 | Zg]; [contradiction | ].
        assert (T10 : T1 = 0).
        { unfold T1. rewrite El0, E0 by exact E0. rewrite Ln10, Tl0. fold R in R1. rewrite R1, ln_1, Rmult_0_l. ring. }
        assert (Ln00 : B ln0 = 0) by (rewrite Bln0, El0, Tl0 by exact E0; ring).
        rewrite Sz, T10, Ln00, Rabs_R0. split; [exact Zg | ].
        pose proof (Rabs_pos (B z)). pose proof (bpow_ge_0 radix2 (-94)). pose proof (bpow_ge_0 radix2 (-41)).
        split; apply Rmult_le_pos; try lra; apply Rmult_le_pos; try lra; apply IZR_le; lia.
      + specialize (Zf eq_refl).
        assert (Sm : IZR 181 * bpow radix2 (-18) <= Rabs (B s)).
        { apply Sfmt.
          - apply generic_format_FLT. exists (Float radix2 181 (-18)); [reflexivity | simpl; lia | simpl; unfold emin; lia].
          - rewrite Ln1t. pose proof (Rabs_triang_inv (B (st_th i)) (- B z)) as T.
            replace (B (st_th i) - - B z) with (B (st_th i) + B z) in T by ring. rewrite Rabs_Ropp in T.
            bpow_num. lra. }
        assert (T1v : T1 = - (B (st_th i) + B (st_tl i) + ln R)) by (unfold T1; rewrite El0, E0, Ln1t by exact E0; rewrite Rmult_0_l; ring).
        split; [apply Rle_trans with (2 := Sm); bpow_num; lra | ].
        split.
        * rewrite T1v, Rabs_Ropp. apply Rle_trans with (/ 158456325028528675187087900672); [exact Terr' | ].
          apply Rle_trans with (IZR 183 * bpow radix2 (-94) * (IZR 181 * bpow radix2 (-18)));
            [bpow_num; lra | apply Rmult_le_compat_l; [bpow_num; lra | exact Sm]].
        * rewrite Bln0, El0 by exact E0. rewrite Rplus_0_l, Rabs_mult.
          apply Rle_trans with (/ 17592186044416 * (1 + / 9007199254740992)).
          { apply Rmult_le_compat; try apply Rabs_pos; [exact Ttl' | ]. apply Rle_trans with (1 := Rabs_triang _ _).
            rewrite Rabs_R1, <- U53. lra. }
          apply Rle_trans with (IZR 183 * bpow radix2 (-41) * (IZR 181 * bpow radix2 (-18)));
            [bpow_num; lra | apply Rmult_le_compat_l; [bpow_num; lra | exact Sm]].
    - pose proof (BigE HE1) as BE.
      assert (Ss : (1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)) <= Rabs (B s)).
      { pose proof (Rabs_triang_inv (B ln1 + B z) (B s)) as T. rewrite Rabs_minus_sym in Rs.
        rewrite U53 in Rs. assert (/ 9007199254740992 * Rabs (B ln1 + B z) <= Rabs (B ln1 + B z)) by (pose proof (Rabs_pos (B ln1 + B z)); lra).
        lra. }
      assert (T1v : T1 = IZR E * (ln 2 - B st_l1 - B st_l0) + (IZR E * B st_l0 - B (fmul (of_int E) st_l0)) - (B (st_th i) + B (st_tl i) + ln R))
        by (unfold T1; rewrite Bln1; ring).
      assert (EA : 1 <= Rabs (IZR E) <= 1100) by lra.
      assert (Vel' : Rabs (B (fmul (of_int E) st_l0) - IZR E * B st_l0) <= / 9007199254740992 * Rabs (IZR E * B st_l0))
        by (replace (/ 9007199254740992) with (/ 2 ^ 53) by (rewrite <- U53; symmetry; exact (bpow_m 53)); exact Vel).
      split.
      { apply Rle_trans with (2 := Ss). bpow_num. lra. }
      split.
      + rewrite T1v. apply Rle_trans with (Rabs (IZR E) * / 2535301200456458802993406410752 + / 9007199254740992 * (Rabs (IZR E) * / 17592186044416) + / 158456325028528675187087900672).
        { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
          apply Rplus_le_compat; [ | exact Terr'].
          apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat.
          - rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | ].
            replace (Rabs (ln 2 - B st_l1 - B st_l0)) with (Rabs (B st_l1 + B st_l0 - ln 2))
              by (rewrite <- Rabs_Ropp; f_equal; ring). exact Lerr'.
          - rewrite Rabs_minus_sym. apply Rle_trans with (1 := Vel'). rewrite Rabs_mult.
            apply Rmult_le_compat_l; [simpl; lra | apply Rmult_le_compat_l; [apply Rabs_pos | exact L0b']]. }
        apply Rle_trans with (IZR 183 * bpow radix2 (-94) * ((1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)))).
        { bpow_num. lra. }
        apply Rmult_le_compat_l; [bpow_num; lra | exact Ss].
      + rewrite Bln0, Rabs_mult.
        assert (Ael : Rabs (B (fmul (of_int E) st_l0)) <= Rabs (IZR E) * / 17592186044416 * (1 + / 9007199254740992)).
        { pose proof (Rabs_triang_inv (B (fmul (of_int E) st_l0)) (IZR E * B st_l0)) as T.
          assert (Rabs (IZR E * B st_l0) <= Rabs (IZR E) * / 17592186044416) by (rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | exact L0b']).
          pose proof (Rabs_pos (IZR E * B st_l0)). pose proof (Rabs_triang_inv (B (fmul (of_int E) st_l0)) (IZR E * B st_l0)). lra. }
        apply Rle_trans with ((Rabs (IZR E) * / 17592186044416 * (1 + / 9007199254740992) + / 17592186044416) * (1 + / 9007199254740992)).
        { apply Rmult_le_compat; try apply Rabs_pos.
          - apply Rle_trans with (1 := Rabs_triang _ _). lra.
          - apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_R1, <- U53. lra. }
        apply Rle_trans with (IZR 183 * bpow radix2 (-41) * ((1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)))).
        { bpow_num. lra. }
        apply Rmult_le_compat_l; [bpow_num; lra | exact Ss]. }
  destruct Su as [Slo [HT1 Hln0]].
  set (zr := B z) in *.
  assert (Pslo : 0 < Rabs (B s)) by (pose proof (bpow_gt_0 radix2 (-62)); lra).
  assert (Snz : B s <> 0) by (intros S0; rewrite S0, Rabs_R0 in Pslo; lra).
  assert (Shi : Rabs (B s) <= 900).
  { pose proof (Rabs_triang_inv (B s) (B ln1 + zr)) as T.
    assert (Rabs (B ln1 + zr) <= 772) by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Bln1, <- Veh; lra).
    rewrite U53 in Rs. lra. }
  (* eta: Fast2Sum's error is at most 2^-53 |s| *)
  assert (He1 : Rabs (B e1) <= bpow radix2 (-53) * Rabs (B s)).
  { pose proof (rnd_err_out (B ln1 + zr)) as R1. rewrite <- Bs in R1.
    specialize (R1 (Rle_trans _ _ _ (bpow_le radix2 (-1022) (-62) ltac:(lia)) Slo)).
    replace (B e1) with (- (B s - (B ln1 + zr))) by lra. rewrite Rabs_Ropp. exact R1. }
  (* No ln_1p split residual: the low sum is e1 + ln0. *)
  assert (Hln0' : Rabs (B ln0) <= 1) by (apply Rle_trans with (1 := Hln0); bpow_num; lra).
  set (w := ln0).
  assert (Fw : finite w) by exact Fln0.
  assert (Hw : Rabs (B w) <= 4) by (unfold w; lra).
  assert (He1' : Rabs (B e1) <= 1) by (bpow_num_in He1; lra).
  destruct (rnd_sum_rel (B e1) (B w) (B_fmt _) (B_fmt _)) as [d2 [Hd2 Ed2]].
  destruct (fadd_s e1 w Fe1 Fw) as [Fpre Bpre]; [apply Small, Rle_trans with (1 := Rabs_triang _ _); lra | ].
  rewrite Ed2 in Bpre. set (pre := fadd e1 w) in *.
  assert (Hpre : Rabs (B pre) <= 10) by (rewrite Bpre, Rabs_mult; apply Rle_trans with (5 * 2);
    [apply Rmult_le_compat; try apply Rabs_pos; [apply Rle_trans with (1 := Rabs_triang _ _); lra
     | apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_R1; bpow_num_in Hd2; lra] | lra]).
  destruct (rnd_sum_rel (B pre) (B q) (B_fmt _) (B_fmt _)) as [d3 [Hd3 Ed3]].
  destruct (fadd_s pre q Fpre Fq) as [Flo Blo]; [apply Small, Rle_trans with (1 := Rabs_triang _ _); lra | ].
  rewrite Ed3 in Blo. set (lo := fadd pre q) in *.
  (* eps *)
  destruct c_kh_ok as [Fkh Bkh]. destruct c_k2h_ok as [Fk2 Bk2]. destruct c_ah_ok as [Fah Bah].
  assert (Z2 : B (fmul z z) = 0 \/ bpow radix2 (-124) <= Rabs (B (fmul z z))).
  { rewrite Bz2. destruct Zg as [Z0 | Zg']; [left; fold zr in Z0; rewrite Z0, Rmult_0_l; apply round_0; exact _ | right].
    apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-124)); lia | ].
    rewrite Rabs_mult. replace (-124)%Z with (-62 + -62)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat; try apply bpow_ge_0; exact Zg'. }
  destruct (fmul_s (fmul z z) c_kh Fz2 Fkh) as [Fe2 Be2]; [apply Small; rewrite Bkh, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-49))) by apply bpow_ge_0; bpow_num; pose proof (Rabs_pos (B (fmul z z))); lra | ].
  rewrite Bkh, (rnd_scale (B (fmul z z)) (-49) (-124) (B_fmt _) Z2 ltac:(lia)) in Be2.
  pose proof (is_finite_Babs 53 1024 unop_nan_pl64 s) as Fas. fold (b64_abs s) in Fas. rewrite Fs in Fas.
  assert (Bas : B (b64_abs s) = Rabs (B s)) by apply B_abs.
  destruct (fmul_s (b64_abs s) c_k2h Fas Fk2) as [Fe3 Be3]; [apply Small; rewrite Bk2, Bas, Rabs_mult, Rabs_Rabsolu, (Rabs_pos_eq (bpow radix2 (-83))) by apply bpow_ge_0; bpow_num; pose proof (Rabs_pos (B s)); lra | ].
  rewrite Bk2, Bas, (rnd_scale (Rabs (B s)) (-83) (-62) ltac:(rewrite <- Bas; apply B_fmt) ltac:(right; rewrite Rabs_Rabsolu; exact Slo) ltac:(lia)) in Be3.
  destruct (rnd_sum_rel (Rabs (B s) * bpow radix2 (-83)) (bpow radix2 (-102)) ltac:(rewrite <- Be3; apply B_fmt) (fmt_pow (-102) ltac:(lia))) as [da [Hda Eda]].
  destruct (fadd_s (fmul (b64_abs s) c_k2h) c_ah Fe3 Fah) as [Fe4 Be4]; [apply Small; rewrite Be3, Bah; bpow_num; apply Rabs_le; pose proof (Rabs_pos (B s)); lra | ].
  rewrite Be3, Bah, Eda in Be4.
  set (E1 := (Rabs (B s) * bpow radix2 (-83) + bpow radix2 (-102)) * (1 + da)) in *.
  destruct (rnd_sum_rel (B (fmul z z) * bpow radix2 (-49)) E1 ltac:(rewrite <- Be2; apply B_fmt) ltac:(rewrite <- Be4; apply B_fmt)) as [db [Hdb Edb]].
  assert (HE1 : 0 <= E1 <= 1).
  { unfold E1. apply Rabs_le_inv in Hda.
    assert (P83 : 0 < bpow radix2 (-83) <= / 1048576) by (split; [apply bpow_gt_0 | change (/ 1048576) with (bpow radix2 (-20)); apply bpow_le; lia]).
    assert (P102 : 0 < bpow radix2 (-102) <= / 1048576) by (split; [apply bpow_gt_0 | change (/ 1048576) with (bpow radix2 (-20)); apply bpow_le; lia]).
    assert (Ub : bpow radix2 (-53) <= / 2) by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
    pose proof (Rabs_pos (B s)) as Ps.
    assert (B0 : 0 <= Rabs (B s) * bpow radix2 (-83) <= 900 / 1048576)
      by (split; [apply Rmult_le_pos; lra | apply Rmult_le_compat; lra]).
    split; [apply Rmult_le_pos; lra | ].
    apply Rle_trans with ((900 / 1048576 + / 1048576) * 2); [apply Rmult_le_compat; lra | lra]. }
  assert (Hz2K : 0 <= B (fmul z z) * bpow radix2 (-49) <= 1).
  { assert (Z0 : 0 <= B (fmul z z)).
    { rewrite Bz2. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ]. apply Rle_0_sqr. }
    assert (P49 : 0 < bpow radix2 (-49) <= 1) by (split; [apply bpow_gt_0 | change 1 with (bpow radix2 0); apply bpow_le; lia]).
    apply Rabs_le_inv in Az2.
    split; [apply Rmult_le_pos; lra | apply Rle_trans with (1 * 1); [apply Rmult_le_compat; lra | lra]]. }
  destruct (fadd_s (fmul (fmul z z) c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah) Fe2 Fe4) as [Feps Beps].
  { apply Small. rewrite Be2, Be4. rewrite Rabs_pos_eq; lra. }
  rewrite Be2, Be4, Edb in Beps.
  set (eps := fadd (fmul (fmul z z) c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah)) in *.
  assert (Hzr1 : 0 < 1 + zr) by lra.
  assert (Dec : IZR E * ln 2 + ln y = IZR E * ln 2 - ln R + ln (1 + zr)).
  { assert (Y : y = (1 + zr) / R) by (rewrite Bz; field; lra).
    rewrite Y. unfold Rdiv. rewrite ln_mult, ln_Rinv by (try apply Rinv_0_lt_compat; lra). ring. }
  (* the polynomial's two errors *)
  set (Pz := h_Pz zr).
  assert (QT : exists t4 t3, B q = zr * zr * (Pz + t4) /\ ln (1 + zr) = zr + zr * zr * Pz + zr * zr * t3 /\
             IZR (-577) * bpow radix2 (-61) <= t4 <= IZR 577 * bpow radix2 (-61) /\
             IZR (-37) * bpow radix2 (-56) <= t3 <= IZR 37 * bpow radix2 (-56) /\
             IZR (-513) * bpow radix2 (-10) <= Pz <= IZR (-511) * bpow radix2 (-10)).
  { destruct (Req_dec zr 0) as [Z0 | Nz].
    - exists 0, 0. rewrite Eq. unfold Pz. rewrite Z0. unfold h_q, h_Pz.
      rewrite !Rmult_0_l, Rplus_0_r, ln_1, round_0 by exact _. rewrite Rmult_0_l, round_0 by exact _.
      split; [ring | ]. split; [ring | ]. bpow_num. split; [lra | ]. split; [lra | ].
      replace (IZR 1 * / IZR 2) with (/ 2) by (simpl; field). split; lra.
    - destruct Zg as [Z0 | Zg']; [contradiction | ].
      destruct (stage_h_q zr ltac:(split; [rewrite Rmult_1_l; exact Zg' | rewrite Rmult_1_l; change (bpow radix2 (-9)) with (/ 512); lra])) as [Q1 Q2].
      assert (Z2p : 0 < zr * zr) by (exact (Rsqr_pos_lt zr Nz)).
      exists ((h_q zr - zr * zr * Pz) / (zr * zr)), ((ln (1 + zr) - zr - zr * zr * Pz) / (zr * zr)).
      split; [rewrite Eq; field; exact Nz | ]. split; [field; exact Nz | ].
      split; [exact Q1 | ]. split; [ | exact Q2].
      apply rng_abs. apply ratio_bound; [rewrite Rabs_pos_eq; lra | ].
      rewrite (Rabs_pos_eq (zr * zr)) by lra.
      pose proof (h_approx zr ltac:(simpl; lra)) as HA. fold Pz in HA.
      apply Rle_trans with (1 := HA). apply Rmult_le_compat_r; [lra | ]. bpow_num. simpl. lra. }
  destruct QT as [t4 [t3 [Eq4 [Eq3 [Ht4 [Ht3 HPz]]]]]].
  assert (Z2r : 0 <= B (fmul z z) /\ Rabs (B (fmul z z) - zr * zr) <= bpow radix2 (-53) * (zr * zr)).
  { rewrite Bz2. split; [apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | apply Rle_0_sqr] | ].
    destruct Zg as [Z0 | Zg'].
    - fold zr in Z0. rewrite Z0, Rmult_0_l, round_0, Rminus_0_r, Rabs_R0, Rmult_0_r by exact _. lra.
    - fold zr in Zg'.
      assert (Hb : bpow radix2 (-1022) <= Rabs (zr * zr)).
      { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-62) * bpow radix2 (-62)).
        - rewrite <- bpow_plus. apply bpow_le. lia.
        - apply Rmult_le_compat; try apply bpow_ge_0; exact Zg'. }
      pose proof (rnd_rel (zr * zr) Hb) as RZ. rewrite (Rabs_pos_eq (zr * zr) (Rle_0_sqr zr)) in RZ. exact RZ. }
  destruct Z2r as [Z2a Z2b].
  destruct (ln_compose (IZR E * ln 2 + ln y) (IZR E * ln 2 - ln R) (B ln1) (B (fmul (of_int E) st_l0)) (B (st_tl i)) d0 0 d2 d3 0 t4 t3 Pz zr 0
              (B s) (B e1) (B ln0) (B w) (B pre) (B q) (B lo) (B (fmul z z)) da db E1 (B eps) 0 0)
    as [Ep [Lo1 Main]].
  - rewrite Dec, Eq3. ring.
  - unfold Rdiv. ring.
  - exact Hzr.
  - lra.
  - exact Bln0.
  - unfold w. ring.
  - exact Bpre.
  - exact Eq4.
  - exact Blo.
  - exact Slo.
  - exact Shi.
  - exact HT1.
  - exact Hln0.
  - exact He1.
  - exact Ht4.
  - exact Ht3.
  - bpow_num; lra.
  - exact HPz.
  - bpow_num; lra.
  - bpow_num; lra.
  - bpow_num; lra.
  - exact Hd0.
  - rewrite Rabs_R0; apply bpow_ge_0.
  - exact Hd2.
  - exact Hd3.
  - exact Hda.
  - exact Hdb.
  - exact Z2a.
  - exact Z2b.
  - reflexivity.
  - exact Beps.
  - split; [exact Fs | ]. split; [exact Flo | ]. split; [exact Feps | ]. split; [exact Ep | ].
    split; [apply Rle_trans with 900; [exact Shi | apply Rle_trans with (bpow radix2 10); [bpow_num; lra | apply bpow_le; lia]] | ].
    split; [exact Lo1 | exact Main].
Qed.


Local Strategy opaque [ln_parts].
