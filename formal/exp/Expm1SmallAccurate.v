(** Executable Q128 small-argument expm1 series and its error bound. *)
From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import ExpAccurate Expm1Tables Expm1AccurateLevels Expm1Series.
Open Scope R_scope.

Definition q_recip (i : nat) : Q128.q128 :=
  Q128.new false (fst (em_recip i)) (- Z.of_nat (snd (em_recip i))).

Lemma q_recip_ok i : (2 <= i <= 16)%nat ->
  NZ (q_recip i) /\ Rabs (Q128.qval (q_recip i) * INR i - 1) <= / 2 ^ 127.
Proof.
  intros Hi. destruct (em_recip_table_ok i Hi) as [Hm Hb].
  assert (W : (0 <= fst (em_recip i) < Q128.W)%Z) by (unfold Q128.W; lia).
  split; [apply new_nz, W | ].
  unfold q_recip. rewrite Q128.new_val by exact W. unfold QSpec.val, F2R. cbn [Fnum Fexp].
  rewrite bpow_m. exact Hb.
Qed.

Fixpoint hq (r : Q128.q128) (c : nat) : Q128.q128 :=
  match c with
  | O => q_one
  | S c' => Q128.add q_one (Q128.mul (Q128.mul r (q_recip (17 - c))) (hq r c'))
  end.

Fixpoint xq (r : R) (c : nat) : R :=
  match c with
  | O => 1
  | S c' => 1 + r / INR (17 - c) * xq r c'
  end.

Lemma step r c d lo hi Eprev Ecur :
  0.9 <= lo -> hi <= 1.1 -> lo <= xq (Q128.qval r) c <= hi ->
  NZ r -> Rabs (Q128.qval r) <= 0.0312501 -> (c < 15)%nat -> INR (17 - S c) = d ->
  (forall rr k ma Xn En mb s, Rabs rr <= 0.0312501 -> lo <= Xn <= hi -> Rabs En <= Eprev ->
     Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
     Rabs (1 + (rr * (1 / d * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + rr / d * Xn)) <= Ecur) ->
  NZ (hq r c) -> Rabs (Q128.qval (hq r c) - xq (Q128.qval r) c) <= Eprev -> Eprev <= / 1000 ->
  NZ (hq r (S c)) /\ Rabs (Q128.qval (hq r (S c)) - xq (Q128.qval r) (S c)) <= Ecur.
Proof.
  intros Lo Hhi XR Nr Hr Hc Hd Bridge NH HE Ep.
  set (i := (17 - S c)%nat) in *.
  assert (Hi : (2 <= i <= 16)%nat) by (unfold i; lia).
  assert (D1 : 1 <= d) by (rewrite <- Hd; replace 1 with (INR 1) by reflexivity; apply le_INR; lia).
  destruct (q_recip_ok i Hi) as [Nk Vk]. rewrite Hd in Vk.
  destruct (mul_any r (q_recip i) Nr Nk) as [N1 [ma [Hma E1]]].
  destruct (mul_any _ (hq r c) N1 NH) as [N2 [mb [Hmb E2]]].
  destruct (add_any q_one _ q_one_nz N2) as [N3 E3].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hma, Hmb. rewrite bpow_m in Hma, Hmb.
  assert (U127 : 0 < / 2 ^ 127 < / 1000) by (split; interval with (i_prec 64)).
  cbn [hq xq]. fold i. split; [exact N3 | ].
  set (rv := Q128.qval r) in *. set (X := xq rv c) in *. set (H := Q128.qval (hq r c)) in *.
  set (k := Q128.qval (q_recip i) * d - 1).
  assert (Ek : Q128.qval (q_recip i) = 1 / d * (1 + k)) by (unfold k; field; lra).
  set (b := Q128.qval (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) in *.
  assert (Eb : b = rv * (1 / d * (1 + k)) * (1 + ma) * (X + (H - X)) * (1 + mb)).
  { rewrite E2, E1, Ek. ring. }
  fold X in XR.
  assert (Hb : Rabs b <= 1).
  { rewrite Eb. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hr. apply Rabs_le_inv in Vk.
    assert (0 < 1 / d <= 1) by (split; [unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; lra
                                       | unfold Rdiv; rewrite Rmult_1_l; rewrite <- Rinv_1; apply Rinv_le_contravar; lra]).
    assert (Kb : - / 2 ^ 127 <= k <= / 2 ^ 127) by (unfold k; lra).
    assert (A : Rabs (rv * (1 / d * (1 + k))) <= 0.032).
    { rewrite Rabs_mult. apply Rle_trans with (0.0312501 * 1.002); [ | lra].
      apply Rmult_le_compat; try apply Rabs_pos; [apply Rabs_le; lra | ].
      rewrite Rabs_mult, (Rabs_pos_eq (1 / d)) by lra. apply Rle_trans with (1 * Rabs (1 + k));
        [apply Rmult_le_compat_r; [apply Rabs_pos | lra] | rewrite Rabs_pos_eq by lra; lra]. }
    assert (B1 : Rabs (1 + ma) <= 1) by (apply Rabs_le; split; lra).
    assert (B2 : Rabs (1 + mb) <= 1) by (apply Rabs_le; split; lra).
    assert (B3 : Rabs (X + (H - X)) <= 1.102) by (apply Rabs_le; split; lra).
    apply Rle_trans with (0.032 * 1 * 1.102 * 1); [ | lra].
    apply Rabs_mult_le; [apply Rabs_mult_le; [apply Rabs_mult_le; [exact A | exact B1] | exact B3] | exact B2]. }
  set (s := Q128.qval (Q128.add q_one (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) - (1 + b)).
  assert (Hs : Rabs s <= / 2 ^ 126).
  { unfold s. rewrite q_one_val in E3. fold b in E3.
    apply Rle_trans with (1 := E3). rewrite Rabs_R1, Rmax_left by lra.
    change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)). rewrite bpow_m. lra. }
  assert (HK : Rabs k <= / 2 ^ 127) by exact Vk.
  pose proof (Bridge rv k ma X (H - X) mb s Hr ltac:(lra) HE HK Hma Hmb Hs) as Br.
  replace (Q128.qval (Q128.add q_one (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) - (1 + rv / INR i * X))
    with (1 + rv * (1 / d * (1 + k)) * (1 + ma) * (X + (H - X)) * (1 + mb) + s - (1 + rv / d * X))
    by (unfold s; rewrite <- Eb, <- Hd; ring).
  exact Br.
Qed.

Theorem series_ok r : NZ r -> Rabs (Q128.qval r) <= 0.0312501 ->
 NZ (hq r 15) /\ Rabs (Q128.qval (hq r 15) - xq (Q128.qval r) 15) <= 538 / 2^135.
Proof.
 intros Nr Hr.
 pose proof Hr as Range. apply Rabs_le_inv in Range.
 assert (S0 : NZ (hq r 0) /\ Rabs (Q128.qval (hq r 0) - xq (Q128.qval r) 0) <= 0).
 { cbn [hq xq]. rewrite q_one_val, Rminus_diag_eq, Rabs_R0 by reflexivity. split; [exact q_one_nz | lra]. }
 Ltac lvl Nr Hr Range r c lo hi L Sin Sout := 
   let N := fresh "N" in let E := fresh "E" in destruct Sin as [N E];
   pose proof (step r c _ lo hi _ _ ltac:(lra) ltac:(lra)
     ltac:(generalize Range; generalize (Q128.qval r); intros rv Rv; cbn [xq]; repeat rewrite INR_IZR_INZ; small_numerals; interval with (i_prec 80))
     Nr Hr ltac:(lia) ltac:(rewrite INR_IZR_INZ; reflexivity) L N E
     ltac:(interval with (i_prec 64))) as Sout.
 lvl Nr Hr Range r 0%nat 0.988121436 1.011916515 em_level_16 S0 S1.
 lvl Nr Hr Range r 1%nat 0.988004026 1.012036297 em_level_15 S1 S2.
 lvl Nr Hr Range r 2%nat 0.987870961 1.012172050 em_level_14 S2 S3.
 lvl Nr Hr Range r 3%nat 0.987718886 1.012327197 em_level_13 S3 S4.
 lvl Nr Hr Range r 4%nat 0.987543416 1.012506212 em_level_12 S4 S5.
 lvl Nr Hr Range r 5%nat 0.987338701 1.012715063 em_level_11 S5 S6.
 lvl Nr Hr Range r 6%nat 0.987096765 1.012961887 em_level_10 S6 S7.
 lvl Nr Hr Range r 7%nat 0.986806441 1.013258075 em_level_09 S7 S8.
 lvl Nr Hr Range r 8%nat 0.986451601 1.013620084 em_level_08 S8 S9.
 lvl Nr Hr Range r 9%nat 0.986008051 1.014072594 em_level_07 S9 S10.
 lvl Nr Hr Range r 10%nat 0.985437773 1.014654393 em_level_06 S10 S11.
 lvl Nr Hr Range r 11%nat 0.984677402 1.015430125 em_level_05 S11 S12.
 lvl Nr Hr Range r 12%nat 0.983612882 1.016516151 em_level_04 S12 S13.
 lvl Nr Hr Range r 13%nat 0.982016103 1.018145188 em_level_03 S13 S14.
 lvl Nr Hr Range r 14%nat 0.979354804 1.020860251 em_level_02 S14 S15.
 exact S15.
Qed.

Definition em_small_accurate x := Q128.mul (qf x) (hq (qf x) 15).

Theorem em_small_accurate_bound x : finite x ->
 /2^54 <= Rabs (B x) <= /32 ->
 QSpec.normalized 128 (Q128.m (em_small_accurate x)) /\
 Rabs (Q128.qval (em_small_accurate x)-(exp (B x)-1)) <= /2^123 * Rabs (exp (B x)-1).
Proof.
 intros Fx X. assert (X0 : B x <> 0).
 { intros Z. rewrite Z, Rabs_R0 in X. assert (0 < /2^54) by interval with (i_prec 64). lra. }
 assert (XA : Rabs (B x) <= 0.0312501) by lra.
 pose proof (from_f64_nz (bits_of_b64 x)) as Nx.
 pose proof (from_f64_b64 x Fx) as Vx. fold (qf x) in Nx, Vx.
 destruct (series_ok (qf x) Nx ltac:(rewrite Vx; exact XA)) as [Nh Eh].
 rewrite Vx in Eh. change (xq (B x) 15) with (small_series (B x) 15) in Eh.
 pose proof (small_series_tail (B x) XA X0) as Et.
 assert (Etb : Rabs (small_series (B x) 15-(exp (B x)-1)/B x) <= 112/2^135).
 { apply Rle_trans with (1:=Et). pose proof (Rabs_pos (B x)) as Ap.
   generalize Ap, XA. generalize (Rabs (B x)). intros a Ha Hb.
   interval with (i_prec 180). }
 set (G := (exp (B x)-1)/B x).
 pose proof (expm1_ratio_small (B x) XA X0) as GRange. fold G in GRange.
 assert (HE : Rabs (Q128.qval (hq (qf x) 15)-G) <= 650/2^135).
 { replace (Q128.qval (hq (qf x) 15)-G) with
   ((Q128.qval (hq (qf x) 15)-small_series (B x) 15)+(small_series (B x) 15-G)) by ring.
   apply Rle_trans with (1:=Rabs_triang _ _). fold G in Etb. lra. }
 destruct (mul_any (qf x) (hq (qf x) 15) Nx Nh) as [Nq [m [Hm Vm]]].
 change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hm. rewrite bpow_m in Hm.
 fold (em_small_accurate x) in Nq, Vm. rewrite Vx in Vm.
 pose proof (em_accurate_small_certificate G (Q128.qval (hq (qf x) 15)-G) m ltac:(lra) HE Hm) as C.
 assert (W : exp (B x)-1 = B x*G) by (unfold G; field; exact X0).
 assert (W0 : exp (B x)-1 <> 0) by (rewrite W; apply Rmult_integral_contrapositive_currified; [exact X0 | lra]).
 assert (Id : (G+(Q128.qval (hq (qf x) 15)-G))*(1+m)/G-1 =
   (Q128.qval (em_small_accurate x)-(exp (B x)-1))/(exp (B x)-1)).
 { rewrite Vm, W. field. split; lra. }
 rewrite Id in C.
 assert (E : Rabs (Q128.qval (em_small_accurate x)-(exp (B x)-1)) <= /2^123 * Rabs (exp (B x)-1)).
 { replace (Q128.qval (em_small_accurate x)-(exp (B x)-1)) with
   (((Q128.qval (em_small_accurate x)-(exp (B x)-1))/(exp (B x)-1))*(exp (B x)-1)) by (field; exact W0).
   rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact C]. }
 split; [ | exact E]. destruct Nq as [Z | N]; [ | exact N].
 rewrite (qval_zero _ Z), Rminus_0_l, Rabs_Ropp in E.
 pose proof (Rabs_pos_lt _ W0). assert (/2^123 < 1) by interval with (i_prec 64). nra.
Qed.

Require Import Exp2Fallback Ln1pLemmas.
Theorem em_small_accurate_round x : finite x -> /2^54 <= Rabs (B x) <= /32 ->
 finite (Q128.to_f64 (em_small_accurate x)) /\
 B (Q128.to_f64 (em_small_accurate x)) = rndF (Q128.qval (em_small_accurate x)).
Proof.
 intros Fx X. destruct (em_small_accurate_bound x Fx X) as [N E].
 assert (XA : -/32 <= B x <= /32) by (apply Rabs_le_inv; lra).
 assert (W : Rabs (exp (B x)-1) <= /16).
 { generalize XA. generalize (B x). intros v V. interval with (i_prec 80). }
 assert (Qb : Rabs (Q128.qval (em_small_accurate x)) <= 1).
 { pose proof (Rabs_triang_inv (Q128.qval (em_small_accurate x)) (exp (B x)-1)).
   assert (/2^123 <= 1) by interval with (i_prec 64). pose proof (Rabs_pos (exp (B x)-1)). nra. }
 assert (Bd : bnd 1 0 (Q128.qval (em_small_accurate x))) by (unfold bnd; change (IZR 1 * bpow radix2 0) with (1*1); lra).
 assert (Ov : Rabs (rndF (Q128.qval (em_small_accurate x))) < bpow radix2 1024).
 { apply Rle_lt_trans with (1:=bnd_round 1 0 _ ltac:(lia) ltac:(lia) Bd).
   apply bnd_lt; lia. }
 split; [apply q128_round_finite | apply to_f64_val]; assumption.
Qed.
