(** The cosine residual's exact -t_hi^2/2 double-word, including low-word scaling. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul
 IEEE64Eft Grid Encodings.
From Interval Require Import Tactic.
Require Import StageGappa TrigTail.
Open Scope R_scope.

Definition trig_neg_half : f64 := b64_of_bits 0xbfe0000000000000%Z.
Lemma trig_neg_half_value : B trig_neg_half = -/2.
Proof.
 unfold trig_neg_half.
 rewrite (bits_val 0xbfe0000000000000 true 4503599627370496 53 eq_refl).
 change (-4503599627370496 / 2^53 = -/2). field.
Qed.
Lemma trig_neg_half_finite : finite trig_neg_half.
Proof. exact (bits_finite 0xbfe0000000000000 _ _ _ eq_refl). Qed.

Lemma trig_half_exact a : finite a -> Rabs(B a)<=1 -> on_grid (-224) (B a) ->
 finite(fmul trig_neg_half a) /\ B(fmul trig_neg_half a)=-(B a/2).
Proof.
 intros A Bound Grid.
 destruct (trig_mul_bounded 0 trig_neg_half a trig_neg_half_finite A ltac:(lia)
   ltac:(rewrite trig_neg_half_value; change (bpow radix2 0) with 1; interval)) as [F [Value _]].
 split; [exact F|]. rewrite Value,trig_neg_half_value.
 replace (-/2*B a) with (-(B a*bpow radix2 (-1))) by (bpow_num; field).
 rewrite round_generic.
 - bpow_num; field.
 - exact _.
 - apply generic_format_opp. apply (scaled_fmt_grid (B a) (-224) (-1));
     [apply B_fmt|exact Grid|lia].
Qed.

Definition trig_cos_square th :=
 let '(uh,ul):=two_prod64 th th in
 two_sum64 (fmul trig_neg_half uh) (fmul trig_neg_half ul).

Theorem trig_cos_square_correct th : finite th -> /2^60<=Rabs(B th)<=0.0078126 ->
 let '(h,l):=trig_cos_square th in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\ B h+B l=-(B th*B th/2).
Proof.
 intros Th Range. pose proof (proj2 Range) as Upper.
 assert (One:Rabs(B th)<=bpow radix2 0) by (change (bpow radix2 0) with 1; lra).
 assert (Domain:in_two_prod_domain (B th) (B th)).
 { right. rewrite Rabs_mult. destruct Range as [Lower _]. bpow_num.
   assert (Positive:0</2^60) by interval. nra. }
 pose proof (two_prod_ieee 0 0 th th Th Th One One ltac:(lia) ltac:(lia) ltac:(lia) Domain) as Product.
 unfold trig_cos_square. destruct (two_prod64 th th) as [uh ul] eqn:Parts.
 cbn zeta iota in Product |- *. destruct Product as [Uh [Ul [UhValue Exact]]].
 pose proof (f_equal fst Parts) as Head. change (fmul th th=uh) in Head.
 destruct (trig_mul_bounded (-13) th th Th Th ltac:(lia)
   ltac:(bpow_num; interval)) as [_ [_ UhBound]]. rewrite Head in UhBound.
 assert (UhSmall:Rabs(B uh)<=/8192) by (bpow_num_all; exact UhBound).
 assert (SquareSmall:Rabs(B th*B th)<=/8192) by interval.
 assert (UlSmall:Rabs(B ul)<=/4096).
 { replace (B ul) with (B th*B th-B uh) by lra.
   pose proof (Rabs_triang (B th*B th) (-B uh)) as Triangle.
   rewrite Rabs_Ropp in Triangle. unfold Rminus; lra. }
 assert (ThGrid:on_grid (-112) (B th)).
 { apply (grid_fmt_bound (FLT_exp emin prec) (-60) (B th));
     [intro e; unfold FLT_exp,emin,prec; lia|apply B_fmt|].
   right. replace (bpow radix2 (-60)) with (/2^60) by (bpow_num; field). exact (proj1 Range). }
 assert (ProductGrid:on_grid (-224) (B th*B th)).
 { change (-224)%Z with ((-112)+(-112))%Z. apply grid_mult; exact ThGrid. }
 assert (UhGrid:on_grid (-224) (B uh)) by (rewrite UhValue; apply grid_round; auto with typeclass_instances).
 assert (UlGrid:on_grid (-224) (B ul)).
 { replace (B ul) with (B th*B th-B uh) by lra. apply grid_minus; assumption. }
 destruct (trig_half_exact uh Uh ltac:(lra) UhGrid) as [HalfUh Hu].
 destruct (trig_half_exact ul Ul ltac:(lra) UlGrid) as [HalfUl Hl].
 assert (HuBound:Rabs(B(fmul trig_neg_half uh))<=bpow radix2 1020).
 { rewrite Hu. bpow_num; interval. }
 assert (HlBound:Rabs(B(fmul trig_neg_half ul))<=bpow radix2 1020).
 { rewrite Hl. bpow_num; interval. }
 pose proof (two_sum_ieee (fmul trig_neg_half uh) (fmul trig_neg_half ul)
   HalfUh HalfUl HuBound HlBound) as Sum.
 destruct (two_sum64 (fmul trig_neg_half uh) (fmul trig_neg_half ul)) as [h l].
 cbn zeta iota in Sum |- *. destruct Sum as [H [L [Rounded Value]]].
 repeat split; try assumption.
 - rewrite Value; exact Rounded.
 - rewrite Value,Hu,Hl. lra.
Qed.
