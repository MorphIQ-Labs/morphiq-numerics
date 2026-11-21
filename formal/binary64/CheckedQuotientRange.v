(** The exponent scan used by checked double-word division.  A finite
    binary64 constructor stores the exact nonzero significand and exponent;
    its significand digit count is [64 - leading_zeros].  The scan ignores
    either signed zero and accumulates the same nonnegative L and H as Rust. *)
From Coq Require Import Reals ZArith Lia Lra List.
From Flocq Require Import Core Digits IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Binary64Div.
Import ListNotations.
Open Scope R_scope.

Definition checked_word_exponent (x:f64) : Z :=
 match x with
 | B754_finite _ m e _ => (e + Zdigits radix2 (Zpos m) - 1)%Z
 | _ => 0%Z
 end.

Fixpoint quotient_extents (words:list f64) : Z * Z :=
 match words with
 | [] => (0%Z,0%Z)
 | w::tail =>
   let '(l,h):=quotient_extents tail in
   match w with
   | B754_zero _ => (l,h)
   | _ => (Z.max l (-checked_word_exponent w),
           Z.max h (checked_word_exponent w+1))
   end
 end.

Definition checked_quotient_range (words:list f64) : bool :=
 let '(l,h):=quotient_extents words in Z.leb (2*l+2*h) 917.

Lemma checked_word_exponent_mag x : finite x -> B x<>0 ->
 checked_word_exponent x = (mag radix2 (B x)-1)%Z.
Proof.
 destruct x as [s|s|s p P|s m e E]; simpl; try discriminate.
 - intros _ H; exfalso; apply H; reflexivity.
 - intros _ _. unfold checked_word_exponent.
   destruct s; simpl; rewrite mag_F2R_Zdigits by discriminate;
   simpl; lia.
Qed.

Lemma checked_word_exponent_bounds x : finite x -> B x<>0 ->
 bpow radix2 (checked_word_exponent x)<=Rabs(B x)<
 bpow radix2 (checked_word_exponent x+1).
Proof.
 intros F NZ. rewrite (checked_word_exponent_mag x F NZ).
 rewrite Z.sub_add.
 split; [apply bpow_mag_le|apply bpow_mag_gt]; exact NZ.
Qed.

Lemma quotient_extents_nonnegative words :
 (0<=fst(quotient_extents words))%Z /\ (0<=snd(quotient_extents words))%Z.
Proof.
 induction words as [|w tail IH]; simpl; [lia|].
 destruct (quotient_extents tail) as [l h]; simpl in *.
 destruct w; simpl; lia.
Qed.

Lemma quotient_extents_contains words w :
 In w words -> finite w ->
 in_range (fst(quotient_extents words)) (snd(quotient_extents words)) (B w).
Proof.
 induction words as [|a tail IH]; simpl; [tauto|].
 destruct (quotient_extents tail) as [l h] eqn:Ext; simpl in *.
 intros [Eq|InTail] F.
 - subst a. destruct w as [s|s|s p P|s m e E]; simpl in *; try discriminate.
   + left; reflexivity.
   + right. assert (NZ:B (B754_finite 53 1024 s m e E)<>0).
     { destruct s; simpl.
       - pose proof (F2R_lt_0 radix2 (Float radix2 (Zneg m) e) ltac:(simpl; lia)); lra.
       - pose proof (F2R_gt_0 radix2 (Float radix2 (Zpos m) e) ltac:(simpl; lia)); lra. }
     pose proof (checked_word_exponent_bounds (B754_finite 53 1024 s m e E) eq_refl NZ) as [Lo Hi]. simpl in Lo, Hi.
     split.
     * apply Rle_trans with (2:=Lo). apply bpow_le. lia.
     * apply Rlt_le_trans with (1:=Hi). apply bpow_le. lia.
 - specialize (IH InTail F). destruct a; simpl; try exact IH.
   all: destruct IH as [Zero|[Lo Hi]]; [now left|right; split].
   all: try (apply Rle_trans with (2:=Lo); apply bpow_le; lia).
   all: apply Rlt_le_trans with (1:=Hi); apply bpow_le; lia.
Qed.

Theorem checked_quotient_range_sound words :
 Forall (fun w=>finite w) words -> checked_quotient_range words=true ->
 let '(l,h):=quotient_extents words in
 (0<=l)%Z /\ (0<=h)%Z /\ (2*l+2*h<=917)%Z /\
 Forall (fun w=>in_range l h (B w)) words.
Proof.
 intros Fin Guard. unfold checked_quotient_range in Guard.
 pose proof (quotient_extents_nonnegative words) as Nonnegative.
 pose proof (quotient_extents_contains words) as Contains.
 destruct (quotient_extents words) as [l h]; simpl in *.
 apply Z.leb_le in Guard. destruct Nonnegative as [L H].
 repeat split; try assumption.
 apply Forall_forall. intros w W. apply Contains; [exact W|].
 rewrite Forall_forall in Fin. exact (Fin w W).
Qed.
