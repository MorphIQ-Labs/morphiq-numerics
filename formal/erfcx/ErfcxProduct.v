(** Double-word multiplication on erfcx's middle-tail range. The binary64
    rounding model includes subnormal low-word operations. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ErfcxReciprocal.
Require erfcx_dw_product.
Open Scope R_scope.

Definition product64 ah al bh bl : f64*f64 :=
 let '(p,e) := two_prod64 ah bh in
 fast_two_sum64 p (fadd e (fadd (fmul ah bl) (fmul al bh))).

Lemma product_model a b c d : /1024 <= rn a <= 2 -> /1024 <= rn c <= 2 ->
 - /2^51 <= rn b/rn a <= /2^51 -> - /2^51 <= rn d/rn c <= /2^51 ->
 let ah := rn a in let al := rn b in let bh := rn c in let bl := rn d in
 let p := rn (ah*bh) in let pe := ah*bh-p in
 let u := rn (ah*bl) in let v := rn (al*bh) in
 let cc := rn (u+v) in let t := rn (pe+cc) in
 let h := rn (p+t) in let l := p+t-h in
 - /2^77 <= ((h+l)-(ah+al)*(bh+bl))/((ah+al)*(bh+bl)) <= /2^77 /\
 /2^21 <= h <= 8 /\ - /2^51 <= l/h <= /2^51 /\
 - /2^27 <= t/p <= /2^27 /\ 999/1000 <= h/(ah*bh) <= 1001/1000.
Proof.
 intros A C B D. cbv zeta. repeat split;
 erfcx_goal (erfcx_dw_product.l1 a b c d).
Qed.

Theorem product_ieee ah al bh bl : finite ah -> finite al -> finite bh -> finite bl ->
 /1024 <= B ah <= 2 -> /1024 <= B bh <= 2 ->
 - /2^51 <= B al/B ah <= /2^51 -> - /2^51 <= B bl/B bh <= /2^51 ->
 let '(h,l) := product64 ah al bh bl in
 finite h /\ finite l /\
 - /2^77 <= ((B h+B l)-(B ah+B al)*(B bh+B bl))/((B ah+B al)*(B bh+B bl)) <= /2^77 /\
 /2^21 <= B h <= 8 /\ - /2^51 <= B l/B h <= /2^51 /\
 999/1000 <= B h/(B ah*B bh) <= 1001/1000.
Proof.
 intros Fah Fal Fbh Fbl Ah Bh Al Bl.
 assert (Ra : rn (B ah) = B ah) by (apply round_generic; [exact _ | apply B_fmt]).
 assert (Rb : rn (B al) = B al) by (apply round_generic; [exact _ | apply B_fmt]).
 assert (Rc : rn (B bh) = B bh) by (apply round_generic; [exact _ | apply B_fmt]).
 assert (Rd : rn (B bl) = B bl) by (apply round_generic; [exact _ | apply B_fmt]).
 pose proof (product_model (B ah) (B al) (B bh) (B bl)
  ltac:(rewrite Ra; exact Ah) ltac:(rewrite Rc; exact Bh)
  ltac:(rewrite Ra,Rb; exact Al) ltac:(rewrite Rc,Rd; exact Bl)) as M.
 cbv zeta in M. rewrite Ra,Rb,Rc,Rd in M.
 destruct M as [Merr [Mh [Ml [Mt Mr]]]].
 assert (Ai : B al = (B al/B ah)*B ah) by (field; lra).
 assert (Bi : B bl = (B bl/B bh)*B bh) by (field; lra).
 assert (LA : -1 <= B al <= 1) by nra.
 assert (LB : -1 <= B bl <= 1) by nra.
 pose proof (two_prod_ieee 1 1 ah bh Fah Fbh
  ltac:(change (bpow radix2 1) with 2; apply Rabs_le; lra)
  ltac:(change (bpow radix2 1) with 2; apply Rabs_le; lra)
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(right; rewrite Rabs_pos_eq by nra;
        apply Rle_trans with (bpow radix2 (-20));
        [apply bpow_le; lia | change (bpow radix2 (-20)) with (/1048576); nra])) as TP.
 unfold product64. destruct (two_prod64 ah bh) as [p e].
 destruct TP as [Fp [Fe [Bp Ee]]].
 assert (P : /1048576 <= B p <= 4).
 { rewrite Bp. split.
   - change (/1048576) with (bpow radix2 (-20)).
     apply round_ge_generic; [exact _ | exact _ | | change (bpow radix2 (-20)) with (/1048576); nra].
     apply generic_format_bpow; unfold FLT_exp,emin,prec; lia.
   - change 4 with (bpow radix2 2).
     apply round_le_generic; [exact _ | exact _ | | change (bpow radix2 2) with 4; nra].
     apply generic_format_bpow; unfold FLT_exp,emin,prec; lia. }
 assert (E : -8 <= B e <= 8) by nra.
 destruct (fmul_bnd 2 0 ah bl Fah Fbl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r; apply Rabs_le; nra)) as [Fu [Bu U]].
 destruct (fmul_bnd 2 0 al bh Fal Fbh ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r; apply Rabs_le; nra)) as [Fv [Bv V]].
 unfold bnd in U,V. change (bpow radix2 0) with 1 in U,V. rewrite Rmult_1_r in U,V.
 destruct (fadd_bnd 4 0 (fmul ah bl) (fmul al bh) Fu Fv ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        eapply Rle_trans; [apply Rabs_triang | lra])) as [Fc [Bc C]].
 unfold bnd in C. change (bpow radix2 0) with 1 in C. rewrite Rmult_1_r in C.
 destruct (fadd_bnd 16 0 e (fadd (fmul ah bl) (fmul al bh)) Fe Fc
  ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        pose proof (Rabs_le_inv _ _ C); apply Rabs_le; lra)) as [Ft [Bt T]].
 unfold bnd in T. change (bpow radix2 0) with 1 in T. rewrite Rmult_1_r in T.
 set (t := fadd e (fadd (fmul ah bl) (fmul al bh))) in *.
 assert (Pe : B e = B ah*B bh-B p) by lra.
 rewrite Bc,Bu,Bv,Pe,Bp in Bt.
 change (B t = rn ((B ah*B bh-rn (B ah*B bh)) + rn (rn (B ah*B bl)+rn (B al*B bh)))) in Bt.
 change (B p = rn (B ah*B bh)) in Bp.
 rewrite <- Bt, <- Bp in Merr,Mh,Ml,Mt,Mr.
 assert (Ti : B t = (B t/B p)*B p) by (field; lra).
 assert (TPbound : Rabs (B t) <= Rabs (B p)).
 { rewrite (Rabs_pos_eq (B p)) by lra. apply Rabs_le; nra. }
 pose proof (fast_two_sum_ieee p t Fp Ft
  ltac:(apply Rle_trans with 4; [apply Rabs_le; lra |
        change 4 with (bpow radix2 2); apply bpow_le; lia])
  ltac:(apply Rle_trans with 16; [exact T |
        change 16 with (bpow radix2 4); apply bpow_le; lia])
  ltac:(right; left; exact TPbound)) as FS.
 destruct (fast_two_sum64 p t) as [h l].
 destruct FS as [Fh [Fl [Bhh Ell]]].
 change (B h = rn (B p+B t)) in Bhh.
 rewrite <- Bhh in Merr,Mh,Ml,Mr.
 assert (El : B l = B p+B t-B h) by lra.
 rewrite <- El in Merr,Ml. repeat split; tauto.
Qed.
