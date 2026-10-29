(** Hardware FMA for the normalized reciprocal stage. Its exact residual
    equals the portable split reduction, including the sign of zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings Grid.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pLemmas LnNormalized.
Require LnReduction.
Open Scope R_scope.

Definition reciprocal_dyadic_check (bits:Z) : bool :=
 match dec bits with
 | Some (m,e) =>
   let p:=(2^(-10-e))%Z in let k:=(m/p)%Z in
   ((e<=? -10) && (0<?k) && (m=?k*p) &&
      ((k=?1024) || negb (2^63 mod k =? 0)))%Z
 | None => false
 end.

Lemma reciprocal_dyadic_certificate : forallb reciprocal_dyadic_check st_r_bits=true.
Proof. vm_compute; reflexivity. Qed.

Lemma reciprocal_dyadic i : (i<512)%nat ->
 exists k:Z, (0<k)%Z /\ B(st_r i)=IZR k*bpow radix2 (-10) /\
 (k=1024 \/ 2^63 mod k<>0)%Z.
Proof.
 intros I.
 assert (Len:length st_r_bits=512%nat) by (vm_compute; reflexivity).
 pose proof reciprocal_dyadic_certificate as Check.
 rewrite forallb_forall in Check.
 assert (Member:In (nth i st_r_bits 0%Z) st_r_bits) by (apply nth_In; rewrite Len; exact I).
 specialize (Check (nth i st_r_bits 0%Z) Member).
 unfold reciprocal_dyadic_check in Check.
 destruct (dec (nth i st_r_bits 0%Z)) as [[m e]|] eqn:D; [|discriminate].
 cbv zeta in Check.
 repeat rewrite andb_true_iff in Check.
 destruct Check as [[[E K] M] Alt].
 apply Z.leb_le in E. apply Z.ltb_lt in K. apply Z.eqb_eq in M.
 set (k:=(m/2^(-10-e))%Z) in *. exists k. split; [exact K | split].
 - destruct (dec_ok _ _ D) as [_ V]. unfold st_r. rewrite V.
   unfold dval. cbn [fst snd]. rewrite M.
   apply shift_val. lia.
 - apply orb_true_iff in Alt. destruct Alt as [A|A].
   + left. apply Z.eqb_eq,A.
   + right. apply negb_true_iff in A. apply Z.eqb_neq,A.
Qed.

Lemma reciprocal_zero_only_one h :
 on_grid (-53) (B h) -> (rd_i (bits_of_b64 h)<512)%nat ->
 B h*B(st_r (rd_i(bits_of_b64 h)))=1 -> B h=1.
Proof.
 intros [m M] I Z.
 destruct (reciprocal_dyadic _ I) as [k [K [R Alt]]].
 assert (MK:(m*k=2^63)%Z).
 { apply eq_IZR. rewrite mult_IZR. rewrite M,R in Z.
   bpow_num_in Z. change (IZR (2^63)) with 9223372036854775808. nra. }
 assert (Mod:(2^63 mod k=0)%Z).
 { rewrite <- MK, Z.mod_mul by lia. reflexivity. }
 destruct Alt as [->|Bad]; [|contradiction].
 rewrite R in Z. assert (One:IZR 1024*bpow radix2 (-10)=1) by (bpow_num; field).
 rewrite One in Z. lra.
Qed.

Definition reciprocal_fma h := b64_fma mode_NE h (rd_rs (bits_of_b64 h))
 (b64_of_bits 13830554455654793216).

Theorem normalized_fma_identical h :
 finite h -> bpow radix2 (-53)<=B h<=bpow radix2 1020 ->
 rd_e(bits_of_b64 h)=0%Z -> on_grid (-53)(B h) ->
 reciprocal_fma h=rd_z h.
Proof.
 intros Fh H E G.
 pose proof (Ln1pReduction.reduce_ok h Fh H) as Red. cbv zeta in Red.
 destruct Red as [_ [I [R [_ [_ [Frs [Vrs [Fz [Vz [_ [[zi [Zi [Zbound _]]] _]]]]]]]]]]].
 rewrite E in Vrs,Vz. change (B(rd_rs(bits_of_b64 h))=B(st_r(rd_i(bits_of_b64 h)))*1) in Vrs.
 change (B(rd_z h)=B h*1*B(st_r(rd_i(bits_of_b64 h)))-1) in Vz.
 destruct (Req_dec (B(rd_z h)) 0) as [Zero|Nonzero].
 - assert (Hone:B h=1) by (apply reciprocal_zero_only_one; [exact G|exact I|nra]).
   assert (Strict:forall x:f64, B x<>0 -> is_finite_strict 53 1024 x=true).
   { intros x N. destruct x; try reflexivity; exfalso; apply N; reflexivity. }
   assert (Same:h=Ln1pReduction.c_one).
   { apply B2R_inj; [apply Strict; lra|apply Strict; rewrite (proj2 c_one_ok); lra|rewrite (proj2 c_one_ok); exact Hone]. }
   subst h. vm_compute; reflexivity.
 - set (minus_one:=b64_of_bits 13830554455654793216).
   assert (Fm:finite minus_one) by reflexivity.
   assert (Vm:B minus_one= -1).
   { unfold minus_one. rewrite (bits_val 13830554455654793216 true 4503599627370496 52 eq_refl).
     change ((-4503599627370496)/2^52= -1). field. }
   pose proof (Bfma_correct 53 1024 eq_refl eq_refl ternop_nan_pl64 mode_NE h
     (rd_rs(bits_of_b64 h)) minus_one Fh Frs Fm) as C. cbv zeta in C.
   assert (Exact:B h*B(rd_rs(bits_of_b64 h))+B minus_one=B(rd_z h)) by (rewrite Vm; nra).
   rewrite Exact in C.
   change (round radix2 (FLT_exp (3-1024-53) 53) (round_mode mode_NE) (B(rd_z h)))
      with (rndF (B(rd_z h))) in C.
   rewrite exact_round in C by apply B_fmt.
   rewrite Rlt_bool_true in C.
   2: { apply Rle_lt_trans with (/2^9); [lra|replace (/2^9) with (bpow radix2 (-9)) by (bpow_num; field); apply bpow_lt; lia]. }
   destruct C as [V [F _]].
   assert (Value:B(reciprocal_fma h)=B(rd_z h)) by exact V.
   assert (Strict:forall x:f64, B x<>0 -> is_finite_strict 53 1024 x=true).
   { intros x N. destruct x; try reflexivity; exfalso; apply N; reflexivity. }
   apply B2R_inj; [apply Strict; rewrite Value; exact Nonzero|apply Strict; exact Nonzero|exact Value].
Qed.

Theorem reduced_fma_identical x : finite x -> 0<B x ->
 let '(_,_,h,_):=LnReduction.reduce x in reciprocal_fma h=rd_z h.
Proof.
 intros Fx Px.
 pose proof (LnReduction.reduce_ok x Fx Px) as Red.
 pose proof (reduced_stage_exponent_zero x) as Exponent.
 destruct (LnReduction.reduce x) as [[[e i]h]r] eqn:D.
 destruct Red as [I [_ [Fh [Y [G _]]]]].
 destruct Exponent as [E _].
 destruct (LnReduction.ln_range i I) as [Yl [Yu _]].
 apply normalized_fma_identical; try assumption.
 split.
 - apply Rle_trans with (/2); [change (/2) with (bpow radix2 (-1)); apply bpow_le; lia|lra].
 - apply Rle_trans with 2; [lra|change 2 with (bpow radix2 1); apply bpow_le; lia].
Qed.
