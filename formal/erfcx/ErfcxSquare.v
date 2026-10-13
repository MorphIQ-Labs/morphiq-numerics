(** IEEE implementation of the square of erfcx's corrected reciprocal. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal.
Require erfcx_middle_square.
Open Scope R_scope.
Definition two : f64 := b64_of_bits 4611686018427387904.
Lemma two_ok : finite two /\ B two = 2.
Proof.
 split.
 - exact (bits_finite 4611686018427387904 false 4503599627370496 (-51) eq_refl).
 - pose proof (bits_val 4611686018427387904 false 4503599627370496 51 eq_refl) as V.
   unfold two. rewrite V. simpl. field.
Qed.
Definition square64 yh yl : f64 * f64 :=
 let '(p,e) := two_prod64 yh yh in
 (p, fadd e (fmul (fmul two yh) yl)).

Lemma square_model a b : /512 <= rn a <= /16 ->
 - /2^56 <= rn b <= /2^56 ->
 - (257/2^61) <= rn b / rn a <= 257/2^61 ->
 let p := rn (rn a * rn a) in
 let e := rn a * rn a - p in
 let l := rn (e + rn (2 * rn a * rn b)) in
 - /2^95 <= ((p+l) - (rn a+rn b)*(rn a+rn b)) /
                ((rn a+rn b)*(rn a+rn b)) <= /2^95 /\
 - /2^51 <= l/p <= /2^51.
Proof.
 intros A B Q. cbv zeta. repeat split;
 erfcx_goal (erfcx_middle_square.l1 a b).
Qed.

Theorem square_ieee yh yl : finite yh -> finite yl ->
 /512 <= B yh <= /16 -> - /2^56 <= B yl <= /2^56 ->
 - (257/2^61) <= B yl / B yh <= 257/2^61 ->
 let '(p,l) := square64 yh yl in
 finite p /\ finite l /\
 /2^18 <= B p <= /2^8 /\
 - /2^95 <= ((B p+B l) - (B yh+B yl)*(B yh+B yl)) /
                ((B yh+B yl)*(B yh+B yl)) <= /2^95 /\
 - /2^51 <= B l/B p <= /2^51.
Proof.
 intros Fy Fl Y L Q. destruct two_ok as [F2 B2].
 pose proof (two_prod_ieee 0 0 yh yh Fy Fy
  ltac:(change (bpow radix2 0) with 1; apply Rabs_le; lra)
  ltac:(change (bpow radix2 0) with 1; apply Rabs_le; lra)
  ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(right; rewrite Rabs_pos_eq by nra;
        apply Rle_trans with (bpow radix2 (-18));
        [apply bpow_le; lia | change (bpow radix2 (-18)) with (/262144); nra])) as TP.
 unfold square64. destruct (two_prod64 yh yh) as [p e].
 destruct TP as [Fp [Fe [Bp Ee]]].
 assert (Prange : /2^18 <= B p <= /2^8).
 { rewrite Bp. replace (/2^18) with (bpow radix2 (-18)) by (bpow_num; field).
   replace (/2^8) with (bpow radix2 (-8)) by (bpow_num; field). split.
   - apply round_ge_generic; [exact _ | exact _ | | change (bpow radix2 (-18)) with (/262144); nra].
     apply generic_format_bpow; unfold FLT_exp, emin, prec; lia.
   - apply round_le_generic; [exact _ | exact _ | | change (bpow radix2 (-8)) with (/256); nra].
     apply generic_format_bpow; unfold FLT_exp, emin, prec; lia. }
 assert (PP : Rabs (B p) <= 1).
 { rewrite Bp. apply abs_round_le_generic; [exact _ | exact _ | | apply Rabs_le; nra].
   change 1 with (bpow radix2 0). apply generic_format_bpow; unfold FLT_exp, emin, prec; lia. }
 assert (EE : Rabs (B e) <= 2) by (apply Rabs_le; pose proof (Rabs_le_inv _ _ PP); nra).
 destruct (fmul_ok 1 0 two yh F2 Fy ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite B2, Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; lra)) as [Ft Bt].
 assert (Bt_exact : B (fmul two yh) = 2 * B yh).
 { rewrite Bt, B2, Rmult_comm. change 2 with (bpow radix2 1).
   apply round_generic; [exact _ | ]. apply mult_bpow_exact_FLT; [apply B_fmt | ].
   assert (M : (-8 <= mag radix2 (B yh))%Z).
   { apply mag_ge_bpow. change (bpow radix2 (-8 - 1)) with (/512).
     rewrite Rabs_pos_eq by lra; lra. }
   unfold emin, prec. lia. }
 destruct (fmul_ok 1 0 (fmul two yh) yl Ft Fl ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bt_exact, Rmult_1_l; change (bpow radix2 0) with 1;
        apply Rabs_le; nra)) as [Fc Bc].
 assert (CC : Rabs (B (fmul (fmul two yh) yl)) <= 1).
 { rewrite Bc, Bt_exact. apply abs_round_le_generic; [exact _ | exact _ | | apply Rabs_le; nra].
   change 1 with (bpow radix2 0). apply generic_format_bpow; unfold FLT_exp, emin, prec; lia. }
 destruct (fadd_ok 3 0 e (fmul (fmul two yh) yl) Fe Fc ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        eapply Rle_trans; [apply Rabs_triang | lra])) as [Fsum Bsum].
 assert (Ryh : rn (B yh) = B yh) by (apply round_generic; [exact _ | apply B_fmt]).
 assert (Ryl : rn (B yl) = B yl) by (apply round_generic; [exact _ | apply B_fmt]).
 pose proof (square_model (B yh) (B yl)
   ltac:(rewrite Ryh; exact Y) ltac:(rewrite Ryl; exact L)
   ltac:(rewrite Ryh, Ryl; exact Q)) as S.
 cbv zeta in S. rewrite Ryh, Ryl in S.
 assert (Eeq : B e = B yh * B yh - B p) by lra.
 rewrite Bsum, Bc, Bt_exact, Eeq, Bp. rewrite Bp in Prange. repeat split; tauto.
Qed.

Require erfcx_middle_square_composition.
Lemma square_composition t ey es : /2^18 <= t <= /2^8 ->
 - /2^98 <= ey <= /2^98 -> - /2^95 <= es <= /2^95 ->
 - /2^102 <= t*(1+ey)*(1+ey)*(1+es)-t <= /2^102.
Proof.
 intros T E S. split; erfcx_goal (erfcx_middle_square_composition.l1 t ey es).
Qed.

Definition reciprocal_square64 x :=
 let '(yh,yl) := reciprocal64 x in square64 yh yl.

Theorem reciprocal_square_ieee x : finite x -> 16 <= B x <= 512 ->
 let '(th,tl) := reciprocal_square64 x in
 finite th /\ finite tl /\
 /2^18 <= B th <= /2^8 /\
 - /2^102 <= (B th+B tl) - (1/B x)*(1/B x) <= /2^102 /\
 - /2^51 <= B tl/B th <= /2^51.
Proof.
 intros Fx X.
 pose proof (reciprocal_ieee x Fx X) as R.
 unfold reciprocal_square64. destruct (reciprocal64 x) as [yh yl].
 destruct R as [Fh [Fl [H [L [Q E]]]]].
 pose proof (square_ieee yh yl Fh Fl H L Q) as S.
 destruct (square64 yh yl) as [th tl].
 destruct S as [Ft [Fl' [Prange [Se Sl]]]].
 assert (Y : /512 <= 1/B x <= /16).
 { unfold Rdiv. rewrite Rmult_1_l. split; apply Rinv_le_contravar; lra. }
 set (y := 1/B x) in *.
 assert (T : /2^18 <= y*y <= /2^8) by nra.
 assert (NZ : y <> 0 /\ B yh+B yl <> 0) by (simpl in L; split; lra).
 pose proof (square_composition (y*y) (((B yh+B yl)-y)/y)
  (((B th+B tl)-(B yh+B yl)*(B yh+B yl))/((B yh+B yl)*(B yh+B yl))) T E Se) as C.
 replace (y*y*(1+((B yh+B yl)-y)/y)*(1+((B yh+B yl)-y)/y)*
   (1+((B th+B tl)-(B yh+B yl)*(B yh+B yl))/((B yh+B yl)*(B yh+B yl)))-y*y)
  with ((B th+B tl)-y*y) in C by (field; tauto).
 repeat split; tauto.
Qed.
