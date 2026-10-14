(** Binary64 middle-tail correction polynomial and compensated reconstruction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal ErfcxSquare ErfcxEntryTables.
Require erfcx_middle_polynomial.
Open Scope R_scope.
Lemma rndF_rn v : rndF v = rn v. Proof. reflexivity. Qed.

Definition poly_r t :=
 rn (pa0_r + rn (t * rn (pa1_r + rn (t * rn (pa2_r + rn (t *
 rn (pa3_r + rn (t * rn (pa4_r + rn (t * rn (pa5_r + rn (t *
 rn (pa6_r + rn (t * pa7_r)))))))))))))).
Definition poly_exact t :=
 pa0_r + t*(pa1_r + t*(pa2_r + t*(pa3_r + t*(pa4_r + t*(pa5_r + t*(pa6_r + t*pa7_r)))))).
Definition correction_exact t := 1 - t/2 + t*t*poly_exact t.

Lemma polynomial_model a b : /2^18 <= rn a <= /2^8 ->
 - /2^51 <= rn b / rn a <= /2^51 ->
 let th := rn a in let tl := rn b in
 let p := poly_r th in
 let w := rn (1 - (1/2)*th) in let ew := 1-(1/2)*th-w in
 let v := rn (rn (th * rn (th+2*tl))*p) in
 let w2 := rn (w+v) in let e3 := w+v-w2 in
 let wl := rn (e3 + rn (ew - rn ((1/2)*tl))) in
 - (21/16)/2^68 <= w2+wl-correction_exact (th+tl) <= (21/16)/2^68 /\
 998/1000 <= w2 <= 1001/1000 /\
 - /2^51 <= wl/w2 <= /2^51 /\
 0 <= p <= 1 /\ 99/100 <= w <= 1 /\ 0 <= v <= /2^15.
Proof.
 intros A Q. cbv zeta.
 unfold poly_r, correction_exact, poly_exact,
  pa0_r,pa1_r,pa2_r,pa3_r,pa4_r,pa5_r,pa6_r,pa7_r.
 repeat split; erfcx_goal (erfcx_middle_polynomial.l1 a b).
Qed.

Definition poly64 th :=
 fadd pa0 (fmul th (fadd pa1 (fmul th (fadd pa2 (fmul th
 (fadd pa3 (fmul th (fadd pa4 (fmul th (fadd pa5 (fmul th
 (fadd pa6 (fmul th pa7))))))))))))).

Definition correction64 th tl : f64*f64 :=
 let pp := poly64 th in
 let '(w,ew) := fast_two_sum64 one (fmul neg_half th) in
 let v := fmul (fmul th (fadd th (fmul two tl))) pp in
 let '(w2,e3) := fast_two_sum64 w v in
 (w2, fadd e3 (fsub ew (fmul half tl))).

Lemma horner_step th a b : finite th -> finite a -> finite b ->
 Rabs (B th) <= /256 -> Rabs (B a) <= 65536 -> Rabs (B b) <= 131072 ->
 finite (fadd a (fmul th b)) /\
 B (fadd a (fmul th b)) = rn (B a + rn (B th * B b)) /\
 Rabs (B (fadd a (fmul th b))) <= 131072.
Proof.
 intros Ft Fa Fb T A Bv.
 destruct (fmul_bnd 1 9 th b Ft Fb ltac:(lia) ltac:(lia)
   ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 9) with 512;
         rewrite Rabs_mult; pose proof (Rabs_pos (B th)); pose proof (Rabs_pos (B b)); nra))
 as [Fm [Bm M]].
 destruct (fadd_bnd 1 17 a (fmul th b) Fa Fm ltac:(lia) ltac:(lia)
   ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd in *; rewrite Rmult_1_l in *;
         change (bpow radix2 9) with 512 in M;
         change (bpow radix2 17) with 131072;
         eapply Rle_trans; [apply Rabs_triang | lra])) as [Fs [Bs S]].
 rewrite Bm in Bs. unfold bnd in S. rewrite Rmult_1_l in S.
 change (bpow radix2 17) with 131072 in S. repeat split; assumption.
Qed.

Lemma poly_ieee th : finite th -> /2^18 <= B th <= /2^8 ->
 finite (poly64 th) /\ B (poly64 th) = poly_r (B th).
Proof.
 intros Ft T.
 assert (T' : Rabs (B th) <= /256) by (apply Rabs_le; nra).
 destruct pa0_ok as [F0 [V0 A0]]. rewrite <- V0 in A0.
 destruct pa1_ok as [F1 [V1 A1]]. rewrite <- V1 in A1.
 destruct pa2_ok as [F2 [V2 A2]]. rewrite <- V2 in A2.
 destruct pa3_ok as [F3 [V3 A3]]. rewrite <- V3 in A3.
 destruct pa4_ok as [F4 [V4 A4]]. rewrite <- V4 in A4.
 destruct pa5_ok as [F5 [V5 A5]]. rewrite <- V5 in A5.
 destruct pa6_ok as [F6 [V6 A6]]. rewrite <- V6 in A6.
 destruct pa7_ok as [F7 [V7 A7]]. rewrite <- V7 in A7.
 destruct (horner_step th pa6 (pa7) Ft F6 F7 T' A6 ltac:(lra)) as [H6 [E6 P6]].
 set (p6 := fadd pa6 (fmul th (pa7))) in *.
 destruct (horner_step th pa5 (p6) Ft F5 H6 T' A5 P6) as [H5 [E5 P5]].
 set (p5 := fadd pa5 (fmul th (p6))) in *.
 destruct (horner_step th pa4 (p5) Ft F4 H5 T' A4 P5) as [H4 [E4 P4]].
 set (p4 := fadd pa4 (fmul th (p5))) in *.
 destruct (horner_step th pa3 (p4) Ft F3 H4 T' A3 P4) as [H3 [E3 P3]].
 set (p3 := fadd pa3 (fmul th (p4))) in *.
 destruct (horner_step th pa2 (p3) Ft F2 H3 T' A2 P3) as [H2 [E2 P2]].
 set (p2 := fadd pa2 (fmul th (p3))) in *.
 destruct (horner_step th pa1 (p2) Ft F1 H2 T' A1 P2) as [H1 [E1 P1]].
 set (p1 := fadd pa1 (fmul th (p2))) in *.
 destruct (horner_step th pa0 (p1) Ft F0 H1 T' A0 P1) as [H0 [E0 P0]].
 set (p0 := fadd pa0 (fmul th (p1))) in *.
 unfold poly64. change (finite p0 /\ B p0 = poly_r (B th)). split; [exact H0 | ].
 rewrite E0, E1, E2, E3, E4, E5, E6. rewrite V0, V1, V2, V3, V4, V5, V6, V7. reflexivity.
Qed.

Theorem correction_ieee th tl : finite th -> finite tl ->
 /2^18 <= B th <= /2^8 -> - /2^51 <= B tl / B th <= /2^51 ->
 let '(h,l) := correction64 th tl in
 finite h /\ finite l /\
 - (21/16)/2^68 <= B h+B l-correction_exact (B th+B tl) <= (21/16)/2^68 /\
 998/1000 <= B h <= 1001/1000 /\ - /2^51 <= B l/B h <= /2^51.
Proof.
 intros Ft Fl T Q.
 assert (Rth : rn (B th) = B th) by (apply round_generic; [exact _ | apply B_fmt]).
 assert (Rtl : rn (B tl) = B tl) by (apply round_generic; [exact _ | apply B_fmt]).
 pose proof (polynomial_model (B th) (B tl)
  ltac:(rewrite Rth; exact T) ltac:(rewrite Rth,Rtl; exact Q)) as Model.
 cbv zeta in Model. rewrite Rth,Rtl in Model.
 destruct Model as [Merr [Mw2 [Ml [Mp [Mw Mv]]]]].
 destruct (poly_ieee th Ft T) as [Fp Bp].
 destruct one_ok as [F1 B1]. destruct two_ok as [F2 B2].
 destruct half_ok as [Fhalf [Bhalf _]].
 destruct neg_half_ok as [Fn [Bn _]].
 assert (Half : half_r = 1/2) by (unfold half_r,float2R,F2R; simpl; bpow_num; field).
 assert (NegHalf : neg_half_r = -(1/2)) by (unfold neg_half_r,float2R,F2R; simpl; bpow_num; field).
 rewrite Half in Bhalf. rewrite NegHalf in Bn.
 assert (Lid : B tl = (B tl/B th)*B th) by (field; nra).
 assert (L : - /2^59 <= B tl <= /2^59) by nra.
 assert (FmtHalf : fmtF (B th * bpow radix2 (-1))).
 { apply mult_bpow_exact_FLT; [apply B_fmt | ].
   assert (M : (-17 <= mag radix2 (B th))%Z).
   { apply mag_ge_bpow. change (bpow radix2 (-17-1)) with (/262144).
     rewrite Rabs_pos_eq by nra; nra. }
   unfold emin,prec. lia. }
 destruct (fmul_ok 1 0 neg_half th Fn Ft ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bn,Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; nra)) as [Fnh Bnh].
 assert (Nexact : B (fmul neg_half th) = -(1/2)*B th).
 { rewrite Bnh,Bn. apply round_generic; [exact _ | ].
   replace (-(1/2)*B th) with (-(B th*bpow radix2 (-1))) by (change (bpow radix2 (-1)) with (/2); field).
   apply generic_format_opp; exact FmtHalf. }
 pose proof (fast_two_sum_ieee one (fmul neg_half th) F1 Fnh
  ltac:(rewrite B1; rewrite Rabs_pos_eq by lra; change 1 with (bpow radix2 0); apply bpow_le; lia)
  ltac:(apply Rle_trans with 1; [rewrite Nexact; apply Rabs_le; nra |
        change 1 with (bpow radix2 0); apply bpow_le; lia])
  ltac:(right; left; rewrite B1,Nexact; rewrite (Rabs_pos_eq 1) by lra; apply Rabs_le; nra)) as FS.
 unfold correction64. destruct (fast_two_sum64 one (fmul neg_half th)) as [w ew].
 destruct FS as [Fw [Few [Bw Eew]]]. rewrite B1,Nexact in Bw,Eew.
 replace (1 + -(1/2)*B th) with (1-(1/2)*B th) in Bw,Eew by ring.
 rewrite rndF_rn in Bw. rewrite <- Bw in Mw,Mw2,Ml,Merr.
 destruct (fmul_ok 1 0 two tl F2 Fl ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite B2,Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; nra)) as [Ftw Btw].
 assert (Twexact : B (fmul two tl) = 2*B tl).
 { rewrite Btw,B2,Rmult_comm. change 2 with (bpow radix2 1).
   apply round_generic; [exact _ | ]. apply mult_bpow_pos_exact_FLT; [apply B_fmt | lia]. }
 destruct (fadd_bnd 1 0 th (fmul two tl) Ft Ftw ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Twexact,Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; nra)) as [Fv0 [Bv0 V0]].
 unfold bnd in V0. rewrite Rmult_1_l in V0. change (bpow radix2 0) with 1 in V0.
 destruct (fmul_bnd 1 0 th (fadd th (fmul two tl)) Ft Fv0 ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1;
        pose proof (Rabs_le_inv _ _ V0); apply Rabs_le; nra)) as [Fv1 [Bv1 V1]].
 unfold bnd in V1. rewrite Rmult_1_l in V1. change (bpow radix2 0) with 1 in V1.
 destruct (fmul_ok 1 0 (fmul th (fadd th (fmul two tl))) (poly64 th) Fv1 Fp ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bp,Rmult_1_l; change (bpow radix2 0) with 1;
        pose proof (Rabs_le_inv _ _ V1); apply Rabs_le; nra)) as [Fv Bv].
 rewrite Bv1,Bv0,Twexact,Bp in Bv.
 set (v := fmul (fmul th (fadd th (fmul two tl))) (poly64 th)) in *.
 change (B v = rn (rn (B th * rn (B th+2*B tl))*poly_r (B th))) in Bv.
 rewrite <- Bv in Mv,Mw2,Ml,Merr.
 pose proof (fast_two_sum_ieee w v Fw Fv
  ltac:(apply Rle_trans with 1; [apply Rabs_le; lra |
        change 1 with (bpow radix2 0); apply bpow_le; lia])
  ltac:(apply Rle_trans with 1; [apply Rabs_le; nra |
        change 1 with (bpow radix2 0); apply bpow_le; lia])
  ltac:(right; left; rewrite !Rabs_pos_eq by nra; nra)) as FS2.
 destruct (fast_two_sum64 w v) as [w2 e3].
 destruct FS2 as [Fw2 [Fe3 [Bw2 Ee3]]].
 rewrite rndF_rn in Bw2. rewrite <- Bw2 in Mw2,Ml,Merr.
 destruct (fmul_bnd 1 0 half tl Fhalf Fl ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bhalf,Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; nra)) as [Fhl [Bhl HL]].
 unfold bnd in HL. rewrite Rmult_1_l in HL. change (bpow radix2 0) with 1 in HL.
 assert (EW : Rabs (B ew) <= 2) by (apply Rabs_le; nra).
 destruct (fsub_bnd 4 0 ew (fmul half tl) Few Fhl ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        pose proof (Rabs_le_inv _ _ EW); pose proof (Rabs_le_inv _ _ HL); apply Rabs_le; lra))
  as [Fwl0 [Bwl0 WL0]].
 unfold bnd in WL0. change (bpow radix2 0) with 1 in WL0. rewrite Rmult_1_r in WL0.
 assert (E3 : Rabs (B e3) <= 3) by (apply Rabs_le; nra).
 destruct (fadd_ok 8 0 e3 (fsub ew (fmul half tl)) Fe3 Fwl0 ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        eapply Rle_trans; [apply Rabs_triang | lra])) as [Fwl Bwl].
 assert (EWval : B ew = 1-(1/2)*B th-B w) by lra.
 assert (E3val : B e3 = B w+B v-B w2) by lra.
 rewrite Bwl0,Bhl,Bhalf,EWval,E3val in Bwl.
 change (B (fadd e3 (fsub ew (fmul half tl))) =
   rn ((B w+B v-B w2) + rn ((1-(1/2)*B th-B w)-rn ((1/2)*B tl)))) in Bwl.
 rewrite <- Bwl in Ml,Merr.
 repeat split; tauto.
Qed.

Require erfcx_middle_mvt.
Lemma correction_sensitivity t d : /2^18 <= t <= /2^8 ->
 - /2^102 <= d <= /2^102 ->
 - /2^101 <= correction_exact (t+d)-correction_exact t <= /2^101.
Proof.
 intros T D. unfold correction_exact,poly_exact,
  pa0_r,pa1_r,pa2_r,pa3_r,pa4_r,pa5_r,pa6_r,pa7_r.
 split; erfcx_goal (erfcx_middle_mvt.l1 t d).
Qed.

Definition reciprocal_correction64 x :=
 let '(th,tl) := reciprocal_square64 x in correction64 th tl.

Theorem reciprocal_correction_ieee x : finite x -> 16 <= B x <= 512 ->
 let '(h,l) := reciprocal_correction64 x in
 finite h /\ finite l /\
 - (21/16)/2^68 - /2^101 <= B h+B l-correction_exact ((1/B x)*(1/B x)) <= (21/16)/2^68 + /2^101 /\
 998/1000 <= B h <= 1001/1000 /\ - /2^51 <= B l/B h <= /2^51.
Proof.
 intros Fx X. pose proof (reciprocal_square_ieee x Fx X) as S.
 unfold reciprocal_correction64. destruct (reciprocal_square64 x) as [th tl].
 destruct S as [Ft [Fl [T [E Q]]]].
 pose proof (correction_ieee th tl Ft Fl T Q) as C.
 destruct (correction64 th tl) as [h l].
 destruct C as [Fh [Fl' [Ce [H L]]]].
 assert (Y : /512 <= 1/B x <= /16).
 { unfold Rdiv. rewrite Rmult_1_l. split; apply Rinv_le_contravar; lra. }
 pose proof (correction_sensitivity ((1/B x)*(1/B x))
   ((B th+B tl)-(1/B x)*(1/B x)) ltac:(nra) E) as M.
 replace ((1/B x)*(1/B x)+((B th+B tl)-(1/B x)*(1/B x))) with (B th+B tl) in M by ring.
 repeat split; try tauto; lra.
Qed.
