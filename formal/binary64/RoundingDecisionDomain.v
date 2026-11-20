(** Acceptance rules out a tiny leading word when the reference value is
    separated from zero. This supplies the rounding theorem's domain without
    assuming that a quotient pair is normalized. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps RoundingCore RoundingTest.
Open Scope R_scope.

Lemma decision_abs_finite x : finite x -> finite(b64_abs x).
Proof. destruct x; simpl; auto. Qed.

Lemma decision_small_ulp x : finite x -> Rabs(B x)<=bpow radix2 (-900) ->
 finite(ulp_f x) /\ bnd 1 (-900) (B(ulp_f x)).
Proof.
 destruct x as [s|s|s p P|s m e E]; cbn [is_finite ulp_f]; try discriminate.
 - intros _ _. destruct (pow2_f (-1074) ltac:(lia)) as [V F].
   split;[exact F|]. unfold bnd. rewrite V,Rabs_pos_eq by apply bpow_ge_0.
   rewrite Rmult_1_l. apply bpow_le;lia.
 - intros _ Small. cbn [B2R] in Small.
   pose proof E as Canon. unfold bounded in Canon. apply andb_prop in Canon as [Canon _].
   pose proof (canonical_canonical_mantissa 53 1024 false m e Canon) as C.
   assert (Lower:(-1074<=e)%Z).
   { unfold canonical,cexp,FLT_exp in C. cbn [Fexp] in C. lia. }
   assert (Abs:Rabs(F2R(Float radix2 (SpecFloat.cond_Zopp s (Zpos m)) e))=
      IZR(Zpos m)*bpow radix2 e).
   { rewrite <-F2R_Zabs. destruct s;reflexivity. }
   rewrite Abs in Small.
   assert (M:1<=IZR(Zpos m)) by (change (IZR 1<=IZR(Zpos m));apply IZR_le;lia).
   assert (Pow:bpow radix2 e<=bpow radix2 (-900)).
   { pose proof (bpow_gt_0 radix2 e);nra. }
   assert (Upper:(e<= -900)%Z) by (now apply (le_bpow radix2)).
   destruct (pow2_f e ltac:(lia)) as [V F].
   split;[exact F|]. unfold bnd. rewrite V,Rabs_pos_eq by apply bpow_ge_0.
   rewrite Rmult_1_l. exact Pow.
Qed.

Lemma decision_half_small x : finite x -> bnd 1 (-900) (B x) ->
 finite(fmul x half) /\ bnd 1 (-900) (B(fmul x half)).
Proof.
 intros F Bound. destruct (pow2_f (-1) ltac:(lia)) as [Half Hf].
 change (B half=/2) in Half. change (finite half) in Hf.
 assert (Product:bnd 1 (-900) (B x*B half)).
 { unfold bnd in *. rewrite Rabs_mult,Half,(Rabs_pos_eq (/2)) by lra.
   pose proof (Rabs_pos (B x));lra. }
 destruct (fmul_ok 1 (-900) x half F Hf ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Product)
   as [Fp Value]. split;[exact Fp|]. rewrite Value. apply bnd_round;[lia|lia|exact Product].
Qed.

Lemma decision_tiny_leading_word hi lo eps v :
 finite hi -> finite lo -> finite eps -> 0<=B eps<=1 ->
 Rabs(B hi)<=bpow radix2 (-900) -> Rabs(B lo)<=bpow radix2 926 ->
 decide_with hi lo eps=Some v -> Rabs(B lo)<bpow radix2 (-900).
Proof.
 intros Fh Fl Fe E Small Low Accepted.
 pose proof (decision_abs_finite hi Fh) as Fm.
 pose proof (decision_abs_finite lo Fl) as Fa.
 assert (M:Rabs(B(b64_abs hi))<=bpow radix2 (-900)) by (rewrite B_abs,Rabs_Rabsolu;exact Small).
 destruct (decision_small_ulp (b64_abs hi) Fm M) as [Fu Bu].
 set (g:=if fraction_zero(b64_abs hi) then fmul(ulp_f(b64_abs hi)) half else ulp_f(b64_abs hi)).
 assert (G:finite g /\ bnd 1 (-900) (B g)).
 { unfold g. destruct (fraction_zero(b64_abs hi));[apply decision_half_small|split];assumption. }
 destruct G as [Fg Bg]. destruct (decision_half_small g Fg Bg) as [Fc Bc].
 assert (P:bnd 1 (-900) (B eps*B(b64_abs hi))).
 { unfold bnd. rewrite B_abs,Rabs_mult,Rabs_pos_eq,Rabs_Rabsolu by lra.
   rewrite Rmult_1_l. pose proof (Rabs_pos (B hi));nra. }
 destruct (fmul_ok 1 (-900) eps (b64_abs hi) Fe Fm ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) P)
   as [Fp Vp].
 assert (Bp:bnd 1 (-900) (B(fmul eps (b64_abs hi)))).
 { rewrite Vp. apply bnd_round;[lia|lia|exact P]. }
 assert (Nonnegative:0<=B(fmul eps (b64_abs hi))).
 { rewrite Vp,B_abs. apply round_ge_generic;auto with typeclass_instances.
   - apply generic_format_0.
   - pose proof (Rabs_pos (B hi));nra. }
 assert (A:bnd 1 926 (B(b64_abs lo))).
 { unfold bnd. rewrite B_abs,Rabs_Rabsolu,Rmult_1_l. exact Low. }
 assert (S:bnd 2 926 (B(b64_abs lo)+B(fmul eps(b64_abs hi)))).
 { apply (bnd_plus 1 1);[exact A|apply (bnd_up 1 (-900));[lia|lia|exact Bp]]. }
 destruct (fadd_ok 2 926 (b64_abs lo) (fmul eps(b64_abs hi)) Fa Fp
   ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) S) as [Fs Vs].
 unfold decide_with in Accepted. fold g in Accepted.
 destruct (Bcompare 53 1024 _ _) eqn:Cmp in Accepted;[|discriminate].
 destruct c;try discriminate.
 rewrite Bcompare_correct in Cmp by assumption. injection Cmp as Cmp.
 apply Rcompare_Lt_inv in Cmp.
 assert (Lo:B(b64_abs lo)<=B(fadd (b64_abs lo) (fmul eps(b64_abs hi)))).
 { rewrite Vs. apply round_ge_generic;auto with typeclass_instances.
   - apply B_fmt.
   - lra. }
 unfold bnd in Bc. rewrite Rmult_1_l in Bc.
 rewrite B_abs in Lo. pose proof (Rle_abs (B(fmul g half))). lra.
Qed.

Theorem decision_reference_domain hi lo eps Z e1 v :
 finite hi -> finite lo -> finite eps -> 0<=B eps<=1 -> 0<=e1<=/2 ->
 Rabs(B lo)<=bpow radix2 926 -> bpow radix2 (-64)<=Rabs Z ->
 Rabs(Z-(B hi+B lo))<=e1*Rabs Z -> decide_with hi lo eps=Some v ->
 bpow radix2 (-900)<Rabs(B hi).
Proof.
 intros Fh Fl Fe E Err Low Ref Accuracy Accepted.
 apply Rnot_le_lt. intro Small.
 pose proof (decision_tiny_leading_word hi lo eps v Fh Fl Fe E Small Low Accepted) as Tiny.
 assert (Sum:Rabs(B hi+B lo)<=2*bpow radix2 (-900)) by (pose proof (Rabs_triang (B hi) (B lo));lra).
 assert (T:Rabs Z<=Rabs(Z-(B hi+B lo))+Rabs(B hi+B lo)).
 { pose proof (Rabs_triang (Z-(B hi+B lo)) (B hi+B lo)) as H.
   replace (Z-(B hi+B lo)+(B hi+B lo)) with Z in H by ring. exact H. }
 assert (Gap:4*bpow radix2 (-900)<bpow radix2 (-64)).
 { change 4 with (bpow radix2 2). rewrite <-bpow_plus. apply bpow_lt;lia. }
 pose proof (Rabs_pos Z);nra.
Qed.

Theorem decision_quotient_ok hi lo eps Z e1 v :
 finite hi -> finite lo -> finite eps ->
 Rabs(B hi)<=bpow radix2 926 -> Rabs(B lo)<=bpow radix2 926 ->
 bpow radix2 (-80)<=e1<=bpow radix2 (-60) ->
 e1*(1+bpow radix2 (-50))<=B eps<=1 -> bpow radix2 (-64)<=Rabs Z ->
 Rabs(Z-(B hi+B lo))<=e1*Rabs Z -> decide_with hi lo eps=Some v ->
 v=hi /\ rndF Z=B hi.
Proof.
 intros Fh Fl Fe High Low E Ep Ref Accuracy Accepted.
 assert (E0:0<=e1<=/2).
 { pose proof (bpow_gt_0 radix2 (-80)).
   assert (Small:bpow radix2 (-60)<=/2) by (change (/2) with (bpow radix2 (-1));apply bpow_le;lia).
   lra. }
 assert (EPS:0<=B eps<=1).
 { pose proof (bpow_gt_0 radix2 (-50));nra. }
 pose proof (decision_reference_domain hi lo eps Z e1 v Fh Fl Fe EPS E0 Low Ref Accuracy Accepted) as Lower.
 apply (decide_with_word_bounded_ok hi lo eps Z e1 v);try assumption.
 - split;[lra|apply Rle_lt_trans with (1:=High);apply bpow_lt;lia].
 - apply Rle_trans with (Rabs(B hi)).
   + pose proof (Rabs_pos (B hi));nra.
   + apply Rle_trans with (1:=High);apply bpow_le;lia.
 - apply Rle_trans with (1:=Low);apply bpow_le;lia.
Qed.
