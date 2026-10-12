(** Multiplying the exact exp2 residual by ln 2, without assuming the
    error-free product's domain or the split subtraction is exact. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Interval Require Import Tactic.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingConstant.
Require Import ExpStageReduction Exp2Constants Ln1pLemmas Ln1pReduction Ln1pTest.
Open Scope R_scope.
Definition split_hi p := fsub (fadd p c_split) c_split.

Lemma split_residual_ok p : finite p -> Rabs (B p) <= bpow radix2 (-10) ->
 let h := split_hi p in
 finite h /\ on_grid (-40) (B h) /\
 Rabs (B p - B h) <= bpow radix2 (-41) /\
 finite (fsub p h) /\ B (fsub p h) = B p - B h.
Proof.
 intros Fp Ap. unfold split_hi.
 destruct (split_round p Fp Ap) as [Fh Bh].
 set (h := fsub (fadd p c_split) c_split) in *.
 set (K := Znearest ne (B p * bpow radix2 40)) in *.
 assert (Near : Rabs (B p * bpow radix2 40 - IZR K) <= / 2) by (unfold K; apply Znearest_half).
 assert (Gh : on_grid (-40) (B h)) by (exists K; exact Bh).
 assert (Dh : Rabs (B p - B h) <= bpow radix2 (-41)).
 { rewrite Bh. replace (B p - IZR K * bpow radix2 (-40)) with ((B p * bpow radix2 40 - IZR K) * bpow radix2 (-40)).
   - rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (-40))) by apply bpow_ge_0.
     bpow_num. bpow_num_in Near. lra.
   - bpow_num. field. }
 assert (Fd : fmtF (B p - B h)).
 { destruct (Z.eq_dec K 0) as [K0 | Kn].
   - rewrite Bh, K0. replace (B p - IZR 0 * bpow radix2 (-40)) with (B p) by (simpl; ring). apply B_fmt.
   - assert (K1 : 1 <= Rabs (IZR K)) by (rewrite <- abs_IZR; apply IZR_le; lia).
     assert (Pl : bpow radix2 (-41) <= Rabs (B p)).
     { pose proof (Rabs_triang_inv (IZR K) (IZR K - B p * bpow radix2 40)) as T.
       replace (IZR K - (IZR K - B p * bpow radix2 40)) with (B p * bpow radix2 40) in T by ring.
       rewrite Rabs_minus_sym, Rabs_mult, (Rabs_pos_eq (bpow radix2 40)) in T by apply bpow_ge_0.
       bpow_num_in T. bpow_num_in Near. bpow_num. lra. }
     apply (grid_repr (-93)); [lia | | apply Rle_lt_trans with (1 := Dh); apply bpow_lt; lia].
     apply grid_minus.
     + apply (grid_fmt_bound (FLT_exp emin prec) (-41)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | right; exact Pl].
     + apply (grid_le (-40)); [lia | exact Gh]. }
 destruct (fsub_s p h Fp Fh) as [Fsub Bsub].
 { apply Rle_trans with (1 := Dh). apply bpow_le; lia. }
 rewrite (exact_round _ Fd) in Bsub.
 repeat split; assumption.
Qed.

Definition exp2_product d : f64 * f64 :=
 let '(p,e) := two_prod64 d e2_lh in
 let rl := fadd e (fmul d e2_ll) in
 let rh := split_hi p in
 (rh, fadd (fsub p rh) rl).

Theorem exp2_product_ok d : finite d -> Rabs (B d) <= bpow radix2 (-10) ->
 (B d = 0 \/ bpow radix2 (-62) <= Rabs (B d)) ->
 let '(rh,rt) := exp2_product d in
 finite rh /\ finite rt /\ on_grid (-40) (B rh) /\
 Rabs (B rh) <= 0.000678 /\ Rabs (B rt) <= bpow radix2 (-40) /\
 Rabs (B rh + B rt - B d * ln 2) <= bpow radix2 (-93).
Proof.
 intros Fd Ad Dlo.
 pose proof e2_lh_range as Lh. pose proof e2_ll_bound as Ll.
 assert (Lh' : Rabs (B e2_lh) <= 0.693148).
 { rewrite e2_lh_val. unfold Rdiv. rewrite Rabs_pos_eq by lra. lra. }
 assert (Dom : in_two_prod_domain (B d) (B e2_lh)).
 { unfold in_two_prod_domain. destruct Dlo as [D0 | Dl].
   - left. rewrite D0. ring.
   - right. rewrite Rabs_mult, (Rabs_pos_eq (B e2_lh)) by lra.
     apply Rle_trans with (bpow radix2 (-62) * 0.69).
     + bpow_num. lra.
     + apply Rmult_le_compat; try apply bpow_ge_0; lra. }
 pose proof (two_prod_ieee (-10) 0 d e2_lh Fd e2_lh_finite Ad ltac:(change (bpow radix2 0) with 1; lra) ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
 unfold exp2_product. revert TP. generalize (two_prod64 d e2_lh). intros [p e] [Fp [Fe [Bp Sum]]].
 assert (Ap : Rabs (B p) <= bpow radix2 (-10)).
 { rewrite Bp. apply rnd_bound; [apply (fmt_pow (-10)); lia | ].
   rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-10) * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | ring_simplify; lra]. }
 assert (Pe : Rabs (B e) <= bpow radix2 (-64)).
 { replace (B e) with (- (B p - B d * B e2_lh)) by lra. rewrite Rabs_Ropp, Bp.
   apply (rnd_err_below _ (-10)); [lia | ]. rewrite Rabs_mult.
   apply Rle_trans with (bpow radix2 (-10) * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | ring_simplify; lra]. }
 assert (Psmall : Rabs (B p) <= 0.000677).
 { pose proof (Rabs_triang_inv (B p) (B e)) as T.
   assert (Prod : Rabs (B d * B e2_lh) <= bpow radix2 (-10) * 0.693148)
     by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
   assert (B p = B d * B e2_lh - B e) by lra.
   rewrite H. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. bpow_num_in Prod. bpow_num_in Pe. lra. }
 destruct (split_residual_ok p Fp Ap) as [Fh [Gh [Dh [Fsub Bsub]]]].
 set (rh := split_hi p) in *.
 assert (Rh : Rabs (B rh) <= 0.000678).
 { pose proof (Rabs_triang_inv (B rh) (B p)) as T. rewrite Rabs_minus_sym in T. bpow_num_in Dh. lra. }
 assert (Dprod : Rabs (B d * B e2_ll) <= bpow radix2 (-65)).
 { rewrite Rabs_mult. replace (-65)%Z with (-10 + -55)%Z by reflexivity. rewrite bpow_plus.
   apply Rmult_le_compat; try apply Rabs_pos; [exact Ad | change (Rabs (B e2_ll) <= / 36028797018963968); rewrite e2_ll_val; interval]. }
 destruct (fmul_s d e2_ll Fd e2_ll_finite) as [Ft Bt].
 { apply Rle_trans with (1 := Dprod). apply bpow_le; lia. }
 assert (Terr : Rabs (B (fmul d e2_ll) - B d * B e2_ll) <= bpow radix2 (-119)).
 { rewrite Bt. apply (rnd_err_below _ (-65)); [lia | exact Dprod]. }
 assert (At : Rabs (B (fmul d e2_ll)) <= bpow radix2 (-65)).
 { rewrite Bt. apply rnd_bound; [apply (fmt_pow (-65)); lia | exact Dprod]. }
 assert (El : Rabs (B e + B (fmul d e2_ll)) <= bpow radix2 (-63)).
 { apply Rle_trans with (1 := Rabs_triang _ _). bpow_num_in Pe. bpow_num_in At. bpow_num. lra. }
 destruct (fadd_s e (fmul d e2_ll) Fe Ft) as [Frl Brl].
 { apply Rle_trans with (1 := El). apply bpow_le; lia. }
 set (rl := fadd e (fmul d e2_ll)) in *.
 assert (RLerr : Rabs (B rl - (B e + B (fmul d e2_ll))) <= bpow radix2 (-117)).
 { rewrite Brl. apply (rnd_err_below _ (-63)); [lia | exact El]. }
 assert (Arl : Rabs (B rl) <= bpow radix2 (-63)).
 { rewrite Brl. apply rnd_bound; [apply (fmt_pow (-63)); lia | exact El]. }
 assert (Ert : Rabs (B (fsub p rh) + B rl) <= bpow radix2 (-40)).
 { rewrite Bsub. apply Rle_trans with (1 := Rabs_triang _ _). bpow_num_in Dh. bpow_num_in Arl. bpow_num. lra. }
 destruct (fadd_s (fsub p rh) rl Fsub Frl) as [Frt Brt].
 { apply Rle_trans with (1 := Ert). apply bpow_le; lia. }
 set (rt := fadd (fsub p rh) rl) in *.
 assert (Rterr : Rabs (B rt - (B p - B rh + B rl)) <= bpow radix2 (-94)).
 { rewrite Brt, <- Bsub. apply (rnd_err_below _ (-40)); [lia | exact Ert]. }
 assert (Art : Rabs (B rt) <= bpow radix2 (-40)).
 { rewrite Brt. apply rnd_bound; [apply (fmt_pow (-40)); lia | exact Ert]. }
 assert (Lc : Rabs (B d * (B e2_lh + B e2_ll - ln 2)) <= bpow radix2 (-119)).
 { rewrite Rabs_mult. replace (-119)%Z with (-10 + -109)%Z by reflexivity. rewrite bpow_plus.
   apply Rmult_le_compat; try apply Rabs_pos; [exact Ad | change (Rabs (B e2_lh + B e2_ll - ln 2) <= / 649037107316853453566312041152512); apply Rle_trans with (1 := e2_l_split); interval with (i_prec 180)]. }
 split; [exact Fh | ]. split; [exact Frt | ]. split; [exact Gh | ]. split; [exact Rh | ]. split; [exact Art | ].
 replace (B rh + B rt - B d * ln 2) with
   ((B rt - (B p - B rh + B rl)) + (B rl - (B e + B (fmul d e2_ll))) +
    (B (fmul d e2_ll) - B d * B e2_ll) + B d * (B e2_lh + B e2_ll - ln 2)) by (clear - Sum; nra).
 apply Rle_trans with (1 := Rabs_triang _ _). apply Rle_trans with (Rabs ((B rt - (B p - B rh + B rl)) + (B rl - (B e + B (fmul d e2_ll)))) + Rabs (B (fmul d e2_ll) - B d * B e2_ll) + Rabs (B d * (B e2_lh + B e2_ll - ln 2))).
 - apply Rplus_le_compat_r, Rabs_triang.
 - pose proof (Rabs_triang (B rt - (B p - B rh + B rl)) (B rl - (B e + B (fmul d e2_ll)))).
   bpow_num_in Rterr. bpow_num_in RLerr. bpow_num_in Terr. bpow_num_in Lc. bpow_num. lra.
Qed.
