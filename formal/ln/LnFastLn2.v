(** The integer exponent times the split ln(2), in scalar order. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingTest.
From Interval Require Import Tactic.
Require Import LnFastTables LnFastTableCheck LnFastAdd LnAccurate ExpFast Ln1pLemmas.
Open Scope R_scope.
Definition lf_e_ln2 e := two_sum64 (fmul (fe e) lf_lh) (fmul (fe e) lf_ll).
Theorem lf_e_ln2_ok e : (Z.abs e<=1074)%Z ->
 let '(h,l):=lf_e_ln2 e in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=2048 /\ Rabs(B l)<=4096 /\
 Rabs(B h+B l-IZR e*ln 2)<=745/2^106*Rabs(IZR e*ln 2).
Proof.
 intros E. destruct (fe_ok e ltac:(lia)) as [Fe Ve].
 assert (Ae : Rabs(IZR e)<=1074) by (rewrite <-abs_IZR; apply IZR_le; exact E).
 assert (Ah : Rabs(B lf_lh)<=1) by (rewrite lf_lh_val; interval with (i_prec 80)).
 assert (Al : Rabs(B lf_ll)<=1) by (rewrite lf_ll_val; interval with (i_prec 80)).
 assert (Fmt : fmtF(IZR e*B lf_lh)).
 { rewrite lf_lh_val. apply generic_format_FLT. exists (Float radix2 (e*3048493539143) (-42)).
   - unfold F2R; cbn [Fnum Fexp]. rewrite mult_IZR. change (bpow radix2 (-42)) with (/4398046511104). field.
   - cbn [Fnum]. rewrite Z.abs_mul. cbn. unfold prec; nia.
   - cbn [Fexp]; unfold emin; lia. }
 destruct (fmul_exact (fe e) lf_lh Fe lf_lh_finite) as [Fp Vp].
 - rewrite Ve; exact Fmt.
 - rewrite Ve,Rabs_mult. apply Rle_lt_trans with 1074; [pose proof (Rabs_pos (IZR e)); nra | interval with (i_prec 80)].
 - rewrite Ve in Vp.
   destruct (fmul_p 11 (fe e) lf_ll Fe lf_ll_finite ltac:(lia)) as [Fq [Vq Aq]].
   + rewrite Ve,Rabs_mult. change (bpow radix2 11) with 2048. pose proof (Rabs_pos (IZR e)); nra.
   + rewrite Ve in Vq.
     assert (N : normal_or_zero (IZR e*B lf_ll)).
     { destruct (Req_dec (IZR e*B lf_ll) 0) as [Z | NZ]; [left; exact Z | right].
       apply Rle_trans with (bpow radix2 (-97)); [apply bpow_le; lia | apply grid_nonzero; [ | exact NZ]].
       exists (e*8711806768342832)%Z. rewrite lf_ll_val,mult_IZR.
       change (bpow radix2 (-97)) with (/158456325028528675187087900672). field. }
     assert (Eq : Rabs(B (fmul (fe e) lf_ll)-IZR e*B lf_ll)<=lf_u*Rabs(IZR e*B lf_ll)).
     { rewrite Vq,normal_round by exact N.
       pose proof (relative_error_N_FLX radix2 prec ltac:(unfold prec; lia) ne (IZR e*B lf_ll)) as R.
       replace (/2*bpow radix2 (-prec+1)) with lf_u in R by (unfold prec,lf_u; simpl; lra). exact R. }
     assert (Ap : Rabs(B (fmul (fe e) lf_lh))<=2048).
     { rewrite Vp,Rabs_mult. pose proof (Rabs_pos (IZR e)); nra. }
     change (bpow radix2 11) with 2048 in Aq.
     pose proof (two_sum_ieee (fmul (fe e) lf_lh) (fmul (fe e) lf_ll) Fp Fq
      ltac:(apply Rle_trans with 2048; [exact Ap | interval with (i_prec 80)])
      ltac:(apply Rle_trans with 2048; [exact Aq | interval with (i_prec 80)])) as S.
     unfold lf_e_ln2. destruct (two_sum64 (fmul (fe e) lf_lh) (fmul (fe e) lf_ll)) as [h l].
     destruct S as [Fh [Fl [Vh Vs]]].
     assert (Dw : B h=rndF(B h+B l)) by (rewrite Vs; exact Vh).
     assert (Bnd : Rabs(B h+B l-IZR e*ln 2)<=745/2^106*Rabs(IZR e*ln 2)).
     { rewrite Vs,Vp. replace (IZR e*B lf_lh+B (fmul (fe e) lf_ll)-IZR e*ln 2)
        with (IZR e*(B lf_lh+B lf_ll-ln 2)+(B (fmul (fe e) lf_ll)-IZR e*B lf_ll)) by ring.
       apply Rle_trans with (1:=Rabs_triang _ _). rewrite !Rabs_mult.
       pose proof lf_ln2_error as L. replace (/2^53) with lf_u in L by (unfold lf_u; field).
       rewrite Rabs_mult in Eq. assert (P : 0<ln 2) by interval with (i_prec 80).
       rewrite (Rabs_pos_eq (ln 2)) by lra. pose proof (Rabs_pos (IZR e)). nra. }
     assert (As : Rabs(B h+B l)<=2048).
     { pose proof (Rabs_triang_inv (B h+B l) (IZR e*ln 2)).
       assert (A : Rabs(IZR e*ln 2)<=1074).
       { rewrite Rabs_mult. assert (Rabs(ln 2)<=1) by interval with (i_prec 80). pose proof (Rabs_pos (IZR e)); nra. }
       assert (745/2^106<=/2) by interval with (i_prec 140). pose proof (Rabs_pos (IZR e*ln 2)); nra. }
     assert (H : Rabs(B h)<=2048) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 11); lia | exact As]).
     assert (L : Rabs(B l)<=4096).
     { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
     repeat split; assumption.
Qed.
