(** The fallback's compensated ln 2 product, with its error-free-transform
    domain, normalization and the grids needed by the shared fast kernel. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingConstant.
Require Import Exp2Constants Ln1pLemmas Ln1pReduction Ln1pTest ExpFast.
Open Scope R_scope.
Definition exp2_dwproduct d :=
 let '(p,e) := two_prod64 d e2_lh in
 two_sum64 p (fadd e (fmul d e2_ll)).

Theorem exp2_dwproduct_ok d : finite d -> Rabs (B d) <= bpow radix2 (-8) ->
 (B d = 0 \/ bpow radix2 (-60) <= Rabs (B d)) ->
 let '(rh,rl) := exp2_dwproduct d in
 finite rh /\ finite rl /\ B rh = rndF (B rh + B rl) /\
 on_grid (-151) (B rh) /\ on_grid (-967) (B rl) /\
 Rabs (B rh + B rl - B d * ln 2) <= bpow radix2 (-113).
Proof.
 intros Fd D Dlo.
 pose proof e2_lh_range as Lh. pose proof e2_ll_bound as Ll.
 assert (Dom : in_two_prod_domain (B d) (B e2_lh)).
 { unfold in_two_prod_domain. destruct Dlo as [D0 | Dl].
   - left. rewrite D0. ring.
   - right. rewrite Rabs_mult, (Rabs_pos_eq (B e2_lh)) by lra.
     apply Rle_trans with (bpow radix2 (-60) * 0.69).
     + bpow_num. lra.
     + apply Rmult_le_compat; try apply bpow_ge_0; lra. }
 pose proof (two_prod_ieee (-8) 0 d e2_lh Fd e2_lh_finite D
   ltac:(change (bpow radix2 0) with 1; rewrite Rabs_pos_eq by lra; lra)
   ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
 unfold exp2_dwproduct. revert TP.
 generalize (two_prod64 d e2_lh). intros [p e] [Fp [Fe [Bp Sum]]].
 assert (Prod : Rabs (B d * B e2_lh) <= bpow radix2 (-8)).
 { rewrite Rabs_mult, (Rabs_pos_eq (B e2_lh)) by lra.
   apply Rle_trans with (bpow radix2 (-8) * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
 assert (Ap : Rabs (B p) <= bpow radix2 (-8)).
 { rewrite Bp. apply rnd_bound; [apply fmt_pow; lia | exact Prod]. }
 assert (Pe : Rabs (B e) <= bpow radix2 (-62)).
 { replace (B e) with (- (B p - B d * B e2_lh)) by lra.
   rewrite Rabs_Ropp, Bp. apply (rnd_err_below _ (-8)); [lia | exact Prod]. }
 assert (Dt : Rabs (B d * B e2_ll) <= bpow radix2 (-63)).
 { rewrite Rabs_mult. replace (-63)%Z with (-8 + -55)%Z by reflexivity. rewrite bpow_plus.
   apply Rmult_le_compat; try apply Rabs_pos; [exact D | change (Rabs (B e2_ll) <= / 36028797018963968); apply Rle_trans with (1 := Ll); interval with (i_prec 100)]. }
 destruct (fmul_s d e2_ll Fd e2_ll_finite) as [Ft Bt].
 { apply Rle_trans with (1 := Dt). apply bpow_le; lia. }
 set (t := fmul d e2_ll) in *.
 assert (Et : Rabs (B t - B d * B e2_ll) <= bpow radix2 (-117)).
 { rewrite Bt. apply (rnd_err_below _ (-63)); [lia | exact Dt]. }
 assert (At : Rabs (B t) <= bpow radix2 (-63)).
 { rewrite Bt. apply rnd_bound; [apply fmt_pow; lia | exact Dt]. }
 assert (Ev : Rabs (B e + B t) <= bpow radix2 (-61)).
 { apply Rle_trans with (1 := Rabs_triang _ _). bpow_num_in Pe. bpow_num_in At. bpow_num. lra. }
 destruct (fadd_s e t Fe Ft) as [Fv Bv].
 { apply Rle_trans with (1 := Ev). apply bpow_le; lia. }
 set (v := fadd e t) in *.
 assert (Verr : Rabs (B v - (B e + B t)) <= bpow radix2 (-115)).
 { rewrite Bv. apply (rnd_err_below _ (-61)); [lia | exact Ev]. }
 assert (Av : Rabs (B v) <= bpow radix2 (-61)).
 { rewrite Bv. apply rnd_bound; [apply fmt_pow; lia | exact Ev]. }
 assert (Ec : Rabs (B d * (B e2_lh + B e2_ll - ln 2)) <= bpow radix2 (-117)).
 { rewrite Rabs_mult. replace (-117)%Z with (-8 + -109)%Z by reflexivity. rewrite bpow_plus.
   apply Rmult_le_compat; try apply Rabs_pos; [exact D | change (Rabs (B e2_lh + B e2_ll - ln 2) <= / 649037107316853453566312041152512); apply Rle_trans with (1 := e2_l_split); interval with (i_prec 180)]. }
 assert (Err : Rabs (B p + B v - B d * ln 2) <= bpow radix2 (-113)).
 { replace (B p + B v - B d * ln 2) with
   ((B v - (B e + B t)) + (B t - B d * B e2_ll) + B d * (B e2_lh + B e2_ll - ln 2)) by (clear - Sum; nra).
   apply Rle_trans with (Rabs (B v - (B e + B t)) + Rabs (B t - B d * B e2_ll) + Rabs (B d * (B e2_lh + B e2_ll - ln 2))).
   - apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat_r, Rabs_triang.
   - bpow_num_in Verr. bpow_num_in Et. bpow_num_in Ec. bpow_num. lra. }
 assert (Pbig : Rabs (B p) <= bpow radix2 1020) by (apply Rle_trans with (1 := Ap); apply bpow_le; lia).
 assert (Vbig : Rabs (B v) <= bpow radix2 1020) by (apply Rle_trans with (1 := Av); apply bpow_le; lia).
 pose proof (two_sum_ieee p v Fp Fv Pbig Vbig) as TS.
 destruct (two_sum64 p v) as [rh rl]. destruct TS as [Fh [Fl [Bh Shl]]].
 assert (Gh : on_grid (-151) (B rh)).
 { apply (grid_le (-115)); [lia | ].
   apply (grid_fmt_bound (FLT_exp emin prec) (-63));
     [intros ex; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
   destruct Dlo as [D0 | Dl].
   - left. rewrite D0, Rmult_0_l, (round_0 radix2 (FLT_exp emin prec) (Znearest ne)) in Bp.
     assert (E0 : B e = 0) by (rewrite D0, Bp in Sum; lra).
     assert (T0 : B t = 0) by (rewrite Bt, D0, Rmult_0_l; apply round_0; exact _).
     rewrite Bh, Bp, Bv, E0, T0, Rplus_0_l.
     rewrite Rplus_0_l, !(round_0 radix2 (FLT_exp emin prec) (Znearest ne)). reflexivity.
   - right.
     assert (L : 0.69 <= ln 2) by interval with (i_prec 64).
     assert (Dz : 0.69 * bpow radix2 (-60) <= Rabs (B d * ln 2)).
     { rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra. rewrite (Rmult_comm 0.69). apply Rmult_le_compat; [apply bpow_ge_0 | lra | exact Dl | exact L]. }
     assert (Slo : bpow radix2 (-62) <= Rabs (B p + B v)).
     { pose proof (Rabs_triang_inv (B d * ln 2) (B p + B v)) as T.
       rewrite Rabs_minus_sym in T. bpow_num_in Dz. bpow_num_in Err. bpow_num. lra. }
     assert (Sn : bpow radix2 (-1022) <= Rabs (B p + B v)) by (apply Rle_trans with (2 := Slo); apply bpow_le; lia).
     pose proof (rel_FLT _ Sn) as E. rewrite <- Bh in E.
     pose proof (Rabs_triang_inv (B p + B v) (B rh)) as T. rewrite Rabs_minus_sym in T.
     bpow_num_in Slo. bpow_num. lra. }
 assert (Gd : on_grid (-112) (B d)).
 { apply (grid_fmt_bound (FLT_exp emin prec) (-60)); [intros ex; unfold FLT_exp, emin, prec; lia | apply B_fmt | exact Dlo]. }
 assert (GLh : on_grid (-53) (B e2_lh)).
 { exists 6243314768165359%Z. rewrite e2_lh_val. bpow_num. field. }
 assert (GLl : on_grid (-108) (B e2_ll)).
 { exists 7525737178955839%Z. rewrite e2_ll_val. bpow_num. field. }
 assert (GP : on_grid (-220) (B d * B e2_lh)).
 { apply (grid_le (-165)); [lia | ]. exact (grid_mult (-112) (-53) _ _ Gd GLh). }
 assert (GT : on_grid (-220) (B d * B e2_ll)) by exact (grid_mult (-112) (-108) _ _ Gd GLl).
 assert (Gp : on_grid (-220) (B p)) by (rewrite Bp; apply grid_round; auto with typeclass_instances).
 assert (Ge : on_grid (-220) (B e)) by (replace (B e) with (B d * B e2_lh - B p) by lra; apply grid_minus; assumption).
 assert (Gv : on_grid (-220) (B v)) by (rewrite Bv, Bt; repeat first [assumption | apply grid_round | apply grid_plus | exact _]).
 assert (Grh : on_grid (-220) (B rh)) by (rewrite Bh; repeat first [assumption | apply grid_round | apply grid_plus | exact _]).
 assert (Gl : on_grid (-967) (B rl)).
 { apply (grid_le (-220)); [lia | ]. replace (B rl) with (B p + B v - B rh) by lra.
   apply grid_minus; [apply grid_plus; assumption | exact Grh]. }
 repeat split; try assumption.
 - rewrite Shl. exact Bh.
 - rewrite Shl. exact Err.
Qed.
