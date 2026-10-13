(** The table kernel's four power-of-two shifters and exact residual. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa ExpReduction.
Open Scope R_scope.

Lemma table_split_round v sh g : finite v -> finite sh -> (-23 <= g <= -20)%Z ->
 B sh = IZR (3*2^51)*bpow radix2 g ->
 Rabs (B v) <= 131072*bpow radix2 g ->
 let h := fsub (fadd v sh) sh in
 finite h /\ B h = IZR (Znearest ne (B v*bpow radix2 (-g)))*bpow radix2 g /\
 (Z.abs (Znearest ne (B v*bpow radix2 (-g))) <= 131072)%Z.
Proof.
 intros Fv Fs G Bs V h.
 assert (Scale : bpow radix2 g*bpow radix2 (-g)=1).
 { rewrite <- bpow_plus. replace (g+-g)%Z with 0%Z by ring. reflexivity. }
 assert (P : 0<bpow radix2 g) by apply bpow_gt_0.
 assert (I : 0<bpow radix2 (-g)) by apply bpow_gt_0.
 assert (Lo : bpow radix2 (g+52)=4503599627370496*bpow radix2 g).
 { rewrite bpow_plus. change (bpow radix2 52) with 4503599627370496. ring. }
 assert (Hi : bpow radix2 (g+53)=9007199254740992*bpow radix2 g).
 { rewrite bpow_plus. change (bpow radix2 53) with 9007199254740992. ring. }
 assert (Vs : -131072*bpow radix2 g <= B v <= 131072*bpow radix2 g).
 { apply Rabs_le_inv in V. lra. }
 change (IZR (3*2^51)) with 6755399441055744 in Bs.
 destruct (fadd_ok 1 (g+53) v sh Fv Fs ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l,Hi,Bs; apply Rabs_le; lra)) as [Fa Ba].
 set (K := Znearest ne (B v*bpow radix2 (-g))).
 assert (Ra : B (fadd v sh)=IZR (K+3*2^51)*bpow radix2 g).
 { rewrite Ba,Bs.
   assert (Mag : mag radix2 (B v+6755399441055744*bpow radix2 g)=(g+53)%Z :> Z).
   { apply mag_unique. replace (g+53-1)%Z with (g+52)%Z by ring.
     rewrite Lo,Hi,Rabs_pos_eq by lra. lra. }
   unfold round,scaled_mantissa,cexp. rewrite Mag. unfold FLT_exp,emin,prec.
   replace (Z.max (g+53-53) (-1074)) with g by lia.
   replace ((B v+6755399441055744*bpow radix2 g)*bpow radix2 (-g))
     with (B v*bpow radix2 (-g)+IZR (3*2^51))
     by (change (IZR (3*2^51)) with 6755399441055744; nra).
   rewrite znearest_shift by reflexivity. reflexivity. }
 assert (Kb : (Z.abs K<=131072)%Z).
 { assert (Scaled : Rabs (B v*bpow radix2 (-g)) <= 131072).
   { rewrite Rabs_mult,(Rabs_pos_eq (bpow radix2 (-g))) by lra.
     apply Rle_trans with (131072*bpow radix2 g*bpow radix2 (-g)).
     - apply Rmult_le_compat_r; lra.
     - rewrite Rmult_assoc,Scale. lra. }
   assert (Near : Rabs (B v*bpow radix2 (-g)-IZR K) <= /2) by (unfold K; apply Znearest_half).
   assert (KI : Rabs (IZR K) < IZR 131073).
   { apply Rabs_le_inv in Near,Scaled. change (IZR 131073) with 131073.
     apply Rabs_lt. lra. }
   rewrite <-abs_IZR in KI. apply lt_IZR in KI. lia. }
 assert (KR : Rabs (IZR K)<=131072) by (rewrite <-abs_IZR; apply IZR_le; exact Kb).
 assert (Diff : B (fadd v sh)-B sh=IZR K*bpow radix2 g).
 { rewrite Ra,Bs,plus_IZR. change (IZR (3*2^51)) with 6755399441055744. ring. }
 destruct (fsub_ok 1 (g+53) (fadd v sh) sh Fa Fs ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l,Hi,Diff,Rabs_mult,(Rabs_pos_eq (bpow radix2 g)) by lra;
        apply Rmult_le_compat_r; lra)) as [Fh Bh].
 split; [exact Fh | split; [ | exact Kb]]. unfold h. rewrite Bh,Diff.
 apply round_generic; [exact _ | ].
 apply generic_format_FLT. exists (Float radix2 K g).
 - reflexivity.
 - change (Z.abs K < 9007199254740992)%Z. lia.
 - change (-1074 <= g)%Z. lia.
Qed.

Require Import Ln1pReduction.
(** A nearest-grid split has an exactly representable low word, including
    the zero-high-word case for subnormal inputs. *)
Lemma nearest_residual_ieee v h g K : finite v -> finite h -> (-1021<=g<=1)%Z ->
 B h=IZR K*bpow radix2 g -> Rabs (B v*bpow radix2 (-g)-IZR K)<=/2 ->
 finite (fsub v h) /\ B (fsub v h)=B v-B h /\ Rabs (B v-B h)<=bpow radix2 (g-1).
Proof.
 intros Fv Fh G Bh Near.
 assert (Scale : bpow radix2 g*bpow radix2 (-g)=1).
 { rewrite <-bpow_plus. replace (g+-g)%Z with 0%Z by ring. reflexivity. }
 assert (P : 0<bpow radix2 g) by apply bpow_gt_0.
 assert (Dh : Rabs (B v-B h)<=bpow radix2 (g-1)).
 { rewrite Bh.
   replace (B v-IZR K*bpow radix2 g) with ((B v*bpow radix2 (-g)-IZR K)*bpow radix2 g)
     by (rewrite Rmult_minus_distr_r,Rmult_assoc;rewrite (Rmult_comm (bpow radix2 (-g)) (bpow radix2 g)),Scale;ring).
   replace (g-1)%Z with (-1+g)%Z by ring. rewrite bpow_plus.
   change (bpow radix2 (-1)) with (/2).
   rewrite Rabs_mult,(Rabs_pos_eq (bpow radix2 g)) by lra.
   apply Rmult_le_compat_r;lra. }
 assert (Hg : on_grid g (B h)) by (exists K;exact Bh).
 assert (Fmt : fmtF (B v-B h)).
 { destruct (Z.eq_dec K 0) as [K0|Kn].
   - rewrite Bh,K0. replace (B v-IZR 0*bpow radix2 g) with (B v) by (simpl;ring). apply B_fmt.
   - assert (Hlow : bpow radix2 g<=Rabs (B h)) by (apply grid_nonzero;[exact Hg|rewrite Bh;intro Zero;apply Kn;apply eq_IZR;simpl;nra]).
     assert (Vlow : bpow radix2 (g-1)<=Rabs (B v)).
     { pose proof (Rabs_triang_inv (B h) (B h-B v)) as D.
       replace (B h-(B h-B v)) with (B v) in D by ring. rewrite Rabs_minus_sym in D.
       assert (Two : bpow radix2 g=2*bpow radix2 (g-1)).
       { change 2 with (bpow radix2 1). rewrite <-bpow_plus. f_equal;lia. } lra. }
     apply (grid_repr (g-53));[lia| |].
     + apply grid_minus.
       * replace (g-53)%Z with ((g-1)-52)%Z by ring.
         apply (grid_fmt_bound (FLT_exp emin prec));[intros;unfold FLT_exp,emin,prec;lia|apply B_fmt|right;exact Vlow].
       * apply grid_le with g;[lia|exact Hg].
     + apply Rle_lt_trans with (1:=Dh). apply bpow_lt;lia. }
 assert (Dsmall : Rabs (B v-B h)<=1).
 { apply Rle_trans with (1:=Dh). change 1 with (bpow radix2 0). apply bpow_le;lia. }
 destruct (fsub_ok 1 0 v h Fv Fh ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l;change (bpow radix2 0) with 1;exact Dsmall)) as [Fl Bl].
 rewrite round_generic in Bl by (exact _ || exact Fmt). repeat split;assumption.
Qed.

Theorem table_split_residual v sh g : finite v -> finite sh -> (-23 <= g <= -20)%Z ->
 B sh=IZR (3*2^51)*bpow radix2 g -> Rabs (B v)<=131072*bpow radix2 g ->
 let h := fsub (fadd v sh) sh in
 finite h /\ on_grid g (B h) /\ Rabs (B h)<=131072*bpow radix2 g /\
 Rabs (B v-B h)<=bpow radix2 (g-1) /\
 finite (fsub v h) /\ B (fsub v h)=B v-B h.
Proof.
 intros Fv Fs G Bs V h.
 destruct (table_split_round v sh g Fv Fs G Bs V) as [Fh [Bh Kb]]. fold h in Fh,Bh.
 set (K := Znearest ne (B v*bpow radix2 (-g))) in *.
 assert (Near : Rabs (B v*bpow radix2 (-g)-IZR K)<=/2) by (unfold K;apply Znearest_half).
 destruct (nearest_residual_ieee v h g K Fv Fh ltac:(lia) Bh Near) as [Fl [Bl Dh]].
 assert (Hg : on_grid g (B h)) by (exists K;exact Bh).
 assert (Hb : Rabs (B h)<=131072*bpow radix2 g).
 { rewrite Bh,Rabs_mult,(Rabs_pos_eq (bpow radix2 g)) by apply bpow_ge_0.
   apply Rmult_le_compat_r;[apply bpow_ge_0|rewrite <-abs_IZR;apply IZR_le;exact Kb]. }
 repeat split;assumption.
Qed.

Definition table_shifter e : f64 := b64_of_bits ((1052+e)*2^52+2^51).
Lemma table_shifter_ok e : (0 <= e <= 3)%Z ->
 finite (table_shifter e) /\ B (table_shifter e)=IZR (3*2^51)*bpow radix2 (e-23).
Proof.
 intros E. assert (Cases : e=0%Z \/ e=1%Z \/ e=2%Z \/ e=3%Z) by lia.
 destruct Cases as [E0|[E0|[E0|E0]]]; subst e.
 - split.
   + exact (bits_finite 4740038607807447040 false 6755399441055744 (-23) eq_refl).
   + pose proof (bits_val 4740038607807447040 false 6755399441055744 23 eq_refl) as V.
     change (B (b64_of_bits 4740038607807447040)=IZR (3*2^51)*bpow radix2 (-23)).
     rewrite V. change (IZR (3*2^51)) with 6755399441055744. bpow_num. simpl. field.
 - split.
   + exact (bits_finite 4744542207434817536 false 6755399441055744 (-22) eq_refl).
   + pose proof (bits_val 4744542207434817536 false 6755399441055744 22 eq_refl) as V.
     change (B (b64_of_bits 4744542207434817536)=IZR (3*2^51)*bpow radix2 (-22)).
     rewrite V. change (IZR (3*2^51)) with 6755399441055744. bpow_num. simpl. field.
 - split.
   + exact (bits_finite 4749045807062188032 false 6755399441055744 (-21) eq_refl).
   + pose proof (bits_val 4749045807062188032 false 6755399441055744 21 eq_refl) as V.
     change (B (b64_of_bits 4749045807062188032)=IZR (3*2^51)*bpow radix2 (-21)).
     rewrite V. change (IZR (3*2^51)) with 6755399441055744. bpow_num. simpl. field.
 - split.
   + exact (bits_finite 4753549406689558528 false 6755399441055744 (-20) eq_refl).
   + pose proof (bits_val 4753549406689558528 false 6755399441055744 20 eq_refl) as V.
     change (B (b64_of_bits 4753549406689558528)=IZR (3*2^51)*bpow radix2 (-20)).
     rewrite V. change (IZR (3*2^51)) with 6755399441055744. bpow_num. simpl. field.
Qed.

Definition table_split64 v e : f64*f64 :=
 let h := fsub (fadd v (table_shifter e)) (table_shifter e) in (h,fsub v h).

Theorem table_split_ieee v e : finite v -> (0 <= e <= 3)%Z ->
 Rabs (B v)<=bpow radix2 (e-6) ->
 let '(h,l) := table_split64 v e in
 finite h /\ finite l /\
 B h=round radix2 (FIX_exp (e-23)) (Znearest ne) (B v) /\
 on_grid (e-23) (B h) /\ Rabs (B h)<=bpow radix2 (e-6) /\
 B h+B l=B v /\ Rabs (B l)<=bpow radix2 (e-24).
Proof.
 intros Fv E V. destruct (table_shifter_ok e E) as [Fs Bs].
 assert (HM : bpow radix2 (e-6)=131072*bpow radix2 (e-23)).
 { replace (e-6)%Z with (17+(e-23))%Z by ring. rewrite bpow_plus. reflexivity. }
 rewrite HM in V.
 destruct (table_split_round v (table_shifter e) (e-23) Fv Fs ltac:(lia) Bs V) as [_ [H _]].
 destruct (table_split_residual v (table_shifter e) (e-23) Fv Fs ltac:(lia) Bs V)
  as [Fh [Hg [Hb [D [Fl L]]]]].
 unfold table_split64. cbv zeta. rewrite L.
 replace (e-24)%Z with ((e-23)-1)%Z by ring. rewrite HM.
 repeat split; try assumption; try lra.
Qed.

Lemma grid_product_format a b qa qb ba bb :
 (-1074 <= qa+qb)%Z -> (ba+bb<53)%Z ->
 on_grid qa a -> on_grid qb b ->
 Rabs a<=bpow radix2 (qa+ba) -> Rabs b<=bpow radix2 (qb+bb) -> fmtF (a*b).
Proof.
 intros Emin Bits Ga Gb A Bv. apply (grid_repr (qa+qb)); [exact Emin | apply grid_mult; assumption | ].
 apply Rle_lt_trans with (bpow radix2 (qa+ba)*bpow radix2 (qb+bb)).
 - rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption.
 - rewrite <-bpow_plus. apply bpow_lt;lia.
Qed.

Theorem table_square_ieee h e : finite h -> (0 <= e <= 3)%Z ->
 on_grid (e-23) (B h) -> Rabs (B h)<=bpow radix2 (e-6) ->
 finite (fmul h h) /\ B (fmul h h)=B h*B h /\
 on_grid (2*(e-23)) (B (fmul h h)).
Proof.
 intros Fh E Gh H.
 assert (Fmt : fmtF (B h*B h)).
 { apply (grid_product_format (B h) (B h) (e-23) (e-23) 17 17); try lia; try assumption;
   replace (e-23+17)%Z with (e-6)%Z by ring;exact H. }
 assert (Hb : Rabs (B h)<=/8).
 { apply Rle_trans with (1:=H). change (/8) with (bpow radix2 (-3)). apply bpow_le;lia. }
 destruct (fmul_ok 1 0 h h Fh Fh ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l; change (bpow radix2 0) with 1;
        rewrite Rabs_mult; pose proof (Rabs_pos (B h));nra)) as [F Bv].
 rewrite round_generic in Bv by (exact _ || exact Fmt).
 split; [exact F | split; [exact Bv | ]]. rewrite Bv.
 replace (2*(e-23))%Z with ((e-23)+(e-23))%Z by ring. apply grid_mult;exact Gh.
Qed.
