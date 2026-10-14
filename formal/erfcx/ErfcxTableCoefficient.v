(** Exact masked coefficients and differences, checked from their encodings. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid.
Require Import Ln1pCheck Ln1pReduction ErfcxTableSplit.
Open Scope R_scope.
Definition truncated_bits b shift := Z.land b (Z.lnot (2^shift-1)).
Definition coefficient_check b shift precision : bool :=
 match dec b, dec (truncated_bits b shift) with
 | Some full, Some cut =>
   let q := (snd cut+shift)%Z in let delta := dsub full cut in
   (0 <=? shift)%Z && (-80 <=? q)%Z && (q <=? 0)%Z &&
   (fst cut mod 2^shift =? 0)%Z &&
   dle (dabs full) (4%Z,0%Z) && dle (dabs cut) (4%Z,0%Z) &&
   dle (dabs cut) (1%Z,(q+precision)%Z) &&
   (-1074 <=? snd delta)%Z && (Z.abs (fst delta) <? 2^53)%Z
 | _,_ => false
 end.

Lemma dyadic_grid d shift : (0<=shift)%Z -> (fst d mod 2^shift=0)%Z ->
 on_grid (snd d+shift) (dval d).
Proof.
 destruct d as [m e]. cbn [fst snd]. intros Shift Mod.
 assert (Pow : (0<2^shift)%Z) by (apply Z.pow_pos_nonneg;lia).
 pose proof (Z.div_mod m (2^shift) ltac:(lia)) as Eq. rewrite Mod,Z.add_0_r in Eq.
 exists (m/2^shift)%Z. unfold dval;cbn [fst snd].
 assert (M : IZR m=IZR (m/2^shift)*bpow radix2 shift).
 { rewrite <-Ln1pCheck.IZR_pow2 by lia. rewrite <-mult_IZR. f_equal. lia. }
 rewrite M,bpow_plus. ring.
Qed.

Lemma dyadic_format d : (-1074<=snd d)%Z -> (Z.abs (fst d)<2^53)%Z -> fmtF (dval d).
Proof.
 destruct d as [m e]. cbn [fst snd]. intros E M. apply generic_format_FLT.
 exists (Float radix2 m e).
 - reflexivity.
 - change (Z.abs m<2^53)%Z. exact M.
 - change (-1074<=e)%Z. exact E.
Qed.

Definition coefficient64 b shift : f64*f64 :=
 let full := b64_of_bits b in let cut := b64_of_bits (truncated_bits b shift) in
 (cut,fsub full cut).

Theorem coefficient_check_ok b shift precision : coefficient_check b shift precision=true ->
 let '(a,d) := coefficient64 b shift in
 finite (b64_of_bits b) /\ finite a /\ finite d /\
 B d=B (b64_of_bits b)-B a /\
 Rabs (B (b64_of_bits b))<=4 /\ Rabs (B a)<=4 /\
 exists q, (-80<=q<=0)%Z /\ on_grid q (B a) /\ Rabs (B a)<=bpow radix2 (q+precision).
Proof.
 unfold coefficient_check.
 destruct (dec b) as [full|] eqn:F; [|discriminate].
 destruct (dec (truncated_bits b shift)) as [cut|] eqn:C; [|discriminate].
 intros Check. repeat rewrite andb_true_iff in Check.
 destruct Check as [[[[[[[[Shift Qlo] Qhi] Mod] Full] Cut] Prec] Emin] Mant].
 apply Z.leb_le in Shift,Qlo,Qhi,Emin. apply Z.eqb_eq in Mod. apply Z.ltb_lt in Mant.
 apply dle_ok in Full,Cut,Prec. rewrite dval_abs in Full,Cut,Prec.
 change (dval (4%Z,0%Z)) with (4*1) in Full,Cut.
 change (dval (1%Z,(snd cut+shift+precision)%Z)) with (1*bpow radix2 (snd cut+shift+precision)) in Prec.
 rewrite Rmult_1_l in Prec.
 destruct (dec_ok _ _ F) as [Ff Bf]. destruct (dec_ok _ _ C) as [Fc Bc].
 assert (Fmt : fmtF (B (b64_of_bits b)-B (b64_of_bits (truncated_bits b shift)))).
 { rewrite Bf,Bc,<-dval_sub. apply dyadic_format;assumption. }
 destruct (fsub_ok 1 4 (b64_of_bits b) (b64_of_bits (truncated_bits b shift)) Ff Fc
  ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l;change (bpow radix2 4) with 16;rewrite Bf,Bc;
        apply Rle_trans with (Rabs (dval full)+Rabs (dval cut));
        [unfold Rminus;rewrite <-(Rabs_Ropp (dval cut));apply Rabs_triang|lra])) as [Fd Bd].
 rewrite round_generic in Bd by (exact _ || exact Fmt).
 unfold coefficient64;cbv zeta. repeat split;try assumption;try (rewrite Bf; lra);try (rewrite Bc;lra).
 exists (snd cut+shift)%Z. split;[lia|split].
 - rewrite Bc. apply dyadic_grid;assumption.
 - rewrite Bc. exact Prec.
Qed.

Definition low_word_check b :=
 match dec b with Some d => dle (dabs d) (1%Z,0%Z) | None => false end.
Lemma low_word_check_ok b : low_word_check b=true ->
 finite (b64_of_bits b) /\ Rabs (B (b64_of_bits b))<=1.
Proof.
 unfold low_word_check. destruct (dec b) as [d|] eqn:D; [|discriminate].
 intros C. destruct (dec_ok _ _ D) as [F V]. split;[exact F|].
 apply dle_ok in C. rewrite dval_abs in C. change (dval (1%Z,0%Z)) with (1*1) in C.
 rewrite V; lra.
Qed.


(** Exact range checks used to discharge table evaluation and Fast2Sum
    preconditions. All comparisons are on decoded dyadic values. *)
Definition word_range_check b lo hi : bool :=
 match dec b with
 | Some v => dle lo v && dle v hi
 | None => false
 end.
Lemma word_range_check_ok b lo hi : word_range_check b lo hi=true ->
 finite (b64_of_bits b) /\ dval lo<=B (b64_of_bits b)<=dval hi.
Proof.
 unfold word_range_check. destruct (dec b) as [v|] eqn:D;[|discriminate].
 intros C. apply andb_true_iff in C as [L U].
 destruct (dec_ok b v D) as [F V]. rewrite V. split;[exact F|].
 split;apply dle_ok;assumption.
Qed.

Definition coefficient_size_check head full low shift ratio err : bool :=
 match dec head,dec full,dec low,dec (truncated_bits full shift) with
 | Some a0,Some a,Some l,Some cut =>
   dle (dabs cut) (dmul (1%Z,ratio) a0) &&
   dle (dabs (dadd (dsub a cut) l)) (1%Z,err)
 | _,_,_,_ => false
 end.
Lemma coefficient_size_check_ok head full low shift ratio err :
 coefficient_size_check head full low shift ratio err=true ->
 Rabs (B (b64_of_bits (truncated_bits full shift)))<=bpow radix2 ratio*B (b64_of_bits head) /\
 Rabs (B (b64_of_bits full)-B (b64_of_bits (truncated_bits full shift))+B (b64_of_bits low))<=bpow radix2 err.
Proof.
 unfold coefficient_size_check.
 destruct (dec head) as [a0|] eqn:D0;[|discriminate].
 destruct (dec full) as [a|] eqn:Da;[|discriminate].
 destruct (dec low) as [l|] eqn:Dl;[|discriminate].
 destruct (dec (truncated_bits full shift)) as [cut|] eqn:Dc;[|discriminate].
 intros C. apply andb_true_iff in C as [Size Err].
 apply dle_ok in Size,Err.
 rewrite dval_abs,dval_mul in Size.
 rewrite dval_abs,dval_add,dval_sub in Err.
 destruct (dec_ok _ _ D0) as [_ V0]. destruct (dec_ok _ _ Da) as [_ Va].
 destruct (dec_ok _ _ Dl) as [_ Vl]. destruct (dec_ok _ _ Dc) as [_ Vc].
 rewrite V0,Va,Vl,Vc. unfold dval at 2 in Size. cbn [fst snd] in Size.
 change (dval (1%Z,err)) with (1*bpow radix2 err) in Err.
 rewrite Rmult_1_l in Size,Err. split;assumption.
Qed.
