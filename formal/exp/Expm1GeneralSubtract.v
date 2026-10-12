(** Cancellation-aware error and grid for the fallback's subtraction before
    scaling. Both words use the executable IEEE double-word operation. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid RoundingTest.
Require Import ExpFast Expm1GeneralBounds Expm1GeneralScale Expm1Scale Ln1pLemmas StageGappa.
Open Scope R_scope.
Definition em_subtract_fast yh yl k := add_f64_64 yh yl (fneg (em_general_pow2 (-k))).
Theorem em_subtract_fast_ok yh yl k x z :
 finite yh -> finite yl -> B yh = rndF (B yh+B yl) -> 3/4 <= B yh <= 4 ->
 on_grid (-1020) (B yh) -> on_grid (-1020) (B yl) ->
 Rabs (z-(B yh+B yl)) <= /2^69*Rabs z ->
 (-54 <= k <= 1024)%Z -> /32 <= Rabs x -> exp x = z*bpow radix2 k ->
 let '(h,l) := em_subtract_fast yh yl k in
 finite h /\ finite l /\ B h = rndF (B h+B l) /\
 on_grid (Z.min (-1020) (-k)) (B h) /\ on_grid (Z.min (-1020) (-k)) (B l) /\
 Rabs ((B h+B l)*bpow radix2 k-(exp x-1)) <= /2^62*Rabs (exp x-1).
Proof.
 intros Fh Fl DW Hy Gh Gl EY K X Ex.
 pose proof (bpow_gt_0 radix2 k) as Pk.
 pose proof (exp_pos x) as Px.
 assert (Zp : 0 < z) by nra.
 assert (Yl : Rabs (B yl) <= bpow radix2 (-50)).
 { pose proof (lo_bound (B yh) (B yl) ltac:(apply Rle_trans with (3/4); [interval with (i_prec 64) | rewrite Rabs_pos_eq; lra]) DW) as L.
   rewrite (Rabs_pos_eq (B yh)) in L by lra. change (bpow radix2 (-52)) with (/4503599627370496) in L.
   change (bpow radix2 (-50)) with (/1125899906842624). lra. }
 destruct (em_general_pow2_ok (-k) ltac:(lia)) as [Fc Bc].
 set (c := fneg (em_general_pow2 (-k))).
 assert (Fnc : finite c) by (unfold c, fneg, b64_opp; rewrite is_finite_Bopp; exact Fc).
 assert (Vc : B c = - bpow radix2 (-k)) by (unfold c, fneg, b64_opp; rewrite B2R_Bopp, Bc; reflexivity).
 assert (C : Rabs (B c) <= bpow radix2 54).
 { rewrite Vc, Rabs_Ropp, Rabs_pos_eq by apply bpow_ge_0. apply bpow_le; lia. }
 assert (Ah : Rabs (B yh) <= bpow radix2 54) by (rewrite Rabs_pos_eq by lra; apply Rle_trans with 4; [lra | change 4 with (bpow radix2 2); apply bpow_le; lia]).
 assert (Al : Rabs (B yl) <= bpow radix2 54) by (apply Rle_trans with (1:=Yl); apply bpow_le; lia).
 assert (Up : forall a, Rabs a <= bpow radix2 54 -> Rabs a <= bpow radix2 1018) by (intros; apply Rle_trans with (1:=H); apply bpow_le; lia).
 pose proof (add_f64_ieee yh yl c Fh Fl Fnc DW (Up _ Ah) (Up _ Al) (Up _ C)) as AI.
 destruct (add_f64_64_ok 1 54 yh yl c Fh Fl Fnc (bnd_of_pow _ _ Ah) (bnd_of_pow _ _ Al) (bnd_of_pow _ _ C)
   ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [_ [_ EQ]].
 pose proof (add_f64_dw (B yh) (B yl) (B c) (B_fmt yh) (B_fmt yl) (B_fmt c) DW) as DM.
 set (q := Z.min (-1020) (-k)).
 assert (Gnc : on_grid q (B c)).
 { rewrite Vc. apply grid_opp. apply (grid_le (-k) q); [unfold q; lia | exists 1%Z; ring]. }
 pose proof (grid_add_f64 q (B yh) (B yl) (B c)
   (grid_le (-1020) q _ ltac:(unfold q; lia) Gh)
   (grid_le (-1020) q _ ltac:(unfold q; lia) Gl) Gnc) as GM.
 unfold em_subtract_fast. fold c. destruct (add_f64_64 yh yl c) as [h l]. cbn [fst snd] in EQ.
 rewrite <- EQ in DM, GM. cbn [fst snd] in DM, GM. destruct GM as [Gmh Gml]. destruct AI as [Fm [Fn EA]].
 repeat split; try assumption.
 set (w := exp x-1).
 pose proof (em_nonzero x X) as W. fold w in W.
 assert (W0 : w <> 0) by (intros E; rewrite E,Rabs_R0 in W; lra).
 assert (Sc : bpow radix2 (-k)*bpow radix2 k = 1) by (rewrite <-bpow_plus,Z.add_opp_diag_l; reflexivity).
 set (eY := ((B yh+B yl)-z)/z).
 assert (Y : - /2^69 <= eY <= /2^69).
 { assert (A : Rabs eY <= /2^69).
   { apply ratio_bound; [rewrite Rabs_pos_eq; lra | rewrite Rabs_minus_sym; exact EY]. }
   apply Rabs_le_inv in A. lra. }
 assert (Yid : B yh+B yl = z*(1+eY)) by (unfold eY; field; lra).
 assert (Wsum : (B yh+B yl+B c)*bpow radix2 k = w*(1+(exp x/w)*eY)).
 { replace (w*(1+exp x/w*eY)) with (w+exp x*eY) by (field; exact W0).
   rewrite Vc,Yid,Ex. unfold w. nra. }
 assert (Sn : B yh+B yl+B c <> 0).
 { intros E. rewrite E,Rmult_0_l in Wsum.
   pose proof (em_ratio_certificate x X) as R. fold w in R.
   assert (E0 : 0 < 1+(exp x/w)*eY).
   { set (r := exp x/w) in *. clearbody r eY. interval with (i_prec 100). }
   apply W0. nra. }
 set (ea := ((B h+B l)-(B yh+B yl+B c))/(B yh+B yl+B c)).
 assert (A : - /2^105 <= ea <= /2^105).
 { change (Rabs ea <= 2*bpow radix2 (-prec)^2) in EA.
   replace (2*bpow radix2 (-prec)^2) with (/2^105) in EA by (unfold prec; apply Rle_antisym; interval with (i_prec 64)).
   apply Rabs_le_inv in EA. lra. }
 assert (Mid : B h+B l = (B yh+B yl+B c)*(1+ea)) by (unfold ea; field; exact Sn).
 pose proof (em_fast_certificate (exp x/w) eY ea (em_ratio_certificate x X) Y A) as Cert.
 apply Rabs_le in Cert.
 assert (Id : (B h+B l)*bpow radix2 k-w = w*((1+exp x/w*eY)*(1+ea)-1)).
 { rewrite Mid. rewrite Rmult_assoc, (Rmult_comm (1+ea)), <-Rmult_assoc, Wsum. ring. }
 fold w. rewrite Id,Rabs_mult. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply Rabs_pos | exact Cert].
Qed.
