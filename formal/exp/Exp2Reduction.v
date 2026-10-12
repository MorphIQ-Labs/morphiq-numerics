(** Exact dyadic reduction for the 512-entry exp2 stage. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings RoundingConstant.
Require Import ExpStageReduction Ln1pLemmas Ln1pReduction.
Open Scope R_scope.
Definition c_512 : f64 := b64_of_bits 4647714815446351872.
Definition c_inv512 : f64 := b64_of_bits 4566650022153682944.
Lemma c_512_ok : finite c_512 /\ B c_512 = bpow radix2 9.
Proof. exact (enc_pow2 9 ltac:(lia)). Qed.
Lemma c_inv512_ok : finite c_inv512 /\ B c_inv512 = bpow radix2 (-9).
Proof. exact (enc_pow2 (-9) ltac:(lia)). Qed.
Definition exp2_reduce x : f64 * Z * Z * f64 :=
 let t := fadd (fmul x c_512) ExpReduction.shifter in
 let n := fsub t ExpReduction.shifter in
 let ni := (bits_of_b64 t - bits_of_b64 ExpReduction.shifter)%Z in
 (n, Z.land ni 511, Z.shiftr ni 9, fsub x (fmul n c_inv512)).
Theorem exp2_reduce_ok x : finite x -> bpow radix2 (-55) <= Rabs (B x) -> Rabs (B x) < 1016 ->
 let '(n,j,k,d) := exp2_reduce x in
 exists ni, finite n /\ B n = IZR ni /\ (Z.abs ni <= 520192)%Z /\
 ni = (512*k+j)%Z /\ (0 <= j < 512)%Z /\ (-1016 <= k <= 1016)%Z /\
 finite d /\ B d = B x - IZR ni / 512 /\ Rabs (B d) <= bpow radix2 (-10) /\
 (B d = 0 \/ bpow radix2 (-62) <= Rabs (B d)).
Proof.
 intros Fx Xlo Xhi. unfold exp2_reduce.
 destruct c_512_ok as [Fc Vc]. destruct c_inv512_ok as [Fi Vi].
 assert (Small : forall v, Rabs v <= 1048576 -> Rabs v <= bpow radix2 1000).
 { intros v Hv. apply Rle_trans with 1048576; [exact Hv | change 1048576 with (bpow radix2 20); apply bpow_le; lia]. }
 destruct (fmul_s x c_512 Fx Fc) as [Fy By].
 { apply Small. rewrite Vc, Rabs_mult, (Rabs_pos_eq (bpow radix2 9)) by apply bpow_ge_0. change (bpow radix2 9) with 512. lra. }
 rewrite Vc, (rnd_scale (B x) 9 (-55) (B_fmt _) (or_intror Xlo) ltac:(lia)) in By.
 set (y := fmul x c_512) in *.
 assert (Yb : Rabs (B y) <= bpow radix2 50).
 { rewrite By, Rabs_mult, (Rabs_pos_eq (bpow radix2 9)) by apply bpow_ge_0. bpow_num. lra. }
 destruct (shifter_add y Fy Yb) as [Ft Bt].
 set (t := fadd y ExpReduction.shifter) in *.
 set (ni := Znearest ne (B y)) in *.
 assert (Hk : Rabs (B y - IZR ni) <= / 2) by (unfold ni; apply Znearest_half).
 assert (Ni : (Z.abs ni <= 520192)%Z).
 { assert (T : Rabs (IZR ni) <= Rabs (B y - IZR ni) + Rabs (B y)).
   { replace (IZR ni) with (- (B y - IZR ni) + B y) at 1 by ring. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
   rewrite By, Rabs_mult, (Rabs_pos_eq (bpow radix2 9)) in T by apply bpow_ge_0.
   change (bpow radix2 9) with 512 in T.
   assert (Hk' : Rabs (B x * 512 - IZR ni) <= / 2) by (rewrite By in Hk; exact Hk).
   assert (Rabs (IZR ni) < 520193) by lra. rewrite <- abs_IZR in H. apply lt_IZR in H. lia. }
 destruct ExpReduction.shifter_value as [Bs Fs].
 assert (Hd : bnd 1 53 (B t - B ExpReduction.shifter)).
 { unfold bnd. rewrite Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
   rewrite <- abs_IZR. replace (IZR 1 * bpow radix2 53) with (IZR (2 ^ 53)) by (simpl; ring). apply IZR_le. lia. }
 destruct (fsub_ok 1 53 t ExpReduction.shifter Ft Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fn Bn].
 assert (Bn' : B (fsub t ExpReduction.shifter) = IZR ni).
 { rewrite Bn, Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
   apply round_generic; auto with typeclass_instances.
   replace (IZR ni) with (IZR ni * bpow radix2 0) by (change (bpow radix2 0) with 1; ring).
   apply ExpReduction.fmt_int; lia. }
 set (n := fsub t ExpReduction.shifter) in *.
 assert (Bits : (bits_of_b64 t - bits_of_b64 ExpReduction.shifter)%Z = ni).
 { rewrite (shifted_bits t ni Ft Bt ltac:(lia)), shifter_bits. ring. }
 rewrite Bits.
 assert (Jk : Z.land ni 511 = (ni mod 512)%Z /\ Z.shiftr ni 9 = (ni / 512)%Z).
 { split; [change 511%Z with (Z.ones 9); rewrite Z.land_ones by lia; reflexivity | rewrite Z.shiftr_div_pow2 by lia; reflexivity]. }
 destruct Jk as [J K]. rewrite J, K.
 pose proof (Z.div_mod ni 512 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ni 512 ltac:(lia)) as MB.
 assert (P1f : fmtF (B n * B c_inv512)).
 { rewrite Bn', Vi. apply ExpReduction.fmt_int; lia. }
 destruct (fmul_s n c_inv512 Fn Fi) as [Fp Bp].
 { apply Small. rewrite Bn', Vi, Rabs_mult, <- abs_IZR, (Rabs_pos_eq (bpow radix2 (-9))) by apply bpow_ge_0.
   assert (IZR (Z.abs ni) <= 520192) by (apply IZR_le; lia). bpow_num. lra. }
 rewrite (exact_round _ P1f), Bn', Vi in Bp.
 change (bpow radix2 (-9)) with (/ 512) in Bp.
 assert (Db : Rabs (B x - IZR ni / 512) <= bpow radix2 (-10)).
 { rewrite By in Hk. change (bpow radix2 9) with 512 in Hk.
   replace (B x - IZR ni / 512) with ((B x * 512 - IZR ni) * / 512) by field.
   rewrite Rabs_mult, (Rabs_pos_eq (/ 512)) by lra. bpow_num. lra. }
 assert (Big : ni <> 0%Z -> bpow radix2 (-10) <= Rabs (B x)).
 { intros Nz. assert (N1 : 1 <= Rabs (IZR ni)) by (rewrite <- abs_IZR; apply IZR_le; lia).
   pose proof (Rabs_triang_inv (IZR ni) (IZR ni - B y)) as T.
   replace (IZR ni - (IZR ni - B y)) with (B y) in T by ring. rewrite Rabs_minus_sym in T.
   rewrite By, Rabs_mult, (Rabs_pos_eq (bpow radix2 9)) in T by apply bpow_ge_0. rewrite By in Hk. change (bpow radix2 9) with 512 in T, Hk. bpow_num. lra. }
 assert (Gd : ni <> 0%Z -> on_grid (-62) (B x - IZR ni / 512)).
 { intros Nz. apply grid_minus.
   - apply (grid_fmt_bound (FLT_exp emin prec) (-10)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | right; exact (Big Nz)].
   - apply grid_le with (-9)%Z; [lia | ]. exists ni. reflexivity. }
 assert (Fd : fmtF (B x - IZR ni / 512)).
 { destruct (Z.eq_dec ni 0) as [Z0 | Nz].
   - rewrite Z0. replace (B x - IZR 0 / 512) with (B x) by (simpl; field). apply B_fmt.
   - apply (grid_repr (-62)); [lia | exact (Gd Nz) | ]. apply Rle_lt_trans with (1 := Db). apply bpow_lt; lia. }
 destruct (fsub_s x (fmul n c_inv512) Fx Fp) as [Fd' Bd].
 { apply Small. rewrite Bp. apply Rle_trans with (1 := Db). bpow_num. lra. }
 rewrite Bp in Bd.
 change (B (fsub x (fmul n c_inv512)) = rndF (B x - IZR ni / 512)) in Bd.
 rewrite (exact_round _ Fd) in Bd.
 exists ni. split; [exact Fn | ]. split; [exact Bn' | ]. split; [exact Ni | ].
 split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [exact Fd' | ].
 split; [exact Bd | ]. rewrite Bd. split; [exact Db | ].
 destruct (Req_dec (B x - IZR ni / 512) 0) as [Z0 | Nz]; [left; exact Z0 | right].
 destruct (Z.eq_dec ni 0) as [N0 | N0].
 - rewrite N0. replace (B x - IZR 0 / 512) with (B x) by (simpl; field).
   apply Rle_trans with (2 := Xlo). apply bpow_le; lia.
 - destruct (Gd N0) as [m Hm]. rewrite Hm in *. rewrite Rabs_mult, <- abs_IZR, (Rabs_pos_eq (bpow radix2 (-62))) by apply bpow_ge_0.
   assert (m <> 0)%Z by (intros M0; apply Nz; rewrite M0; simpl; ring).
   assert (1 <= IZR (Z.abs m)) by (apply IZR_le; lia).
   pose proof (bpow_ge_0 radix2 (-62)). nra.
Qed.
