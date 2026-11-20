(** The actual checked double-word division, including the operand, range,
    nonzero-divisor and zero-result screens. Errors erase to [None]. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Div IEEE64 IEEE64Div CheckedQuotientRange.
Import ListNotations.
Open Scope R_scope.

Definition checked_float_eq (x y:f64) : bool :=
 match Bcompare 53 1024 x y with Some Eq=>true|_=>false end.
Definition checked_zero : f64 := B754_zero 53 1024 false.
Definition checked_valid (h l:f64) : bool :=
 is_finite 53 1024 h && is_finite 53 1024 l && checked_float_eq (fadd h l) h.
Definition checked_admit (xh zh zl:f64) : option (f64*f64) :=
 if checked_float_eq xh checked_zero &&
    negb(checked_float_eq zh checked_zero && checked_float_eq zl checked_zero)
 then None else Some(zh,zl).
Definition checked_divide (xh xl yh yl:f64) : option(f64*f64) :=
 if checked_valid xh xl && checked_valid yh yl then
 if checked_float_eq yh checked_zero then None else
 if checked_quotient_range [xh;xl;yh;yl] then
 let '(zh,zl):=div64 xh xl yh yl in checked_admit xh zh zl
 else None else None.

Lemma checked_float_eq_spec x y : finite x -> finite y ->
 (checked_float_eq x y=true <-> B x=B y).
Proof.
 intros X Y. unfold checked_float_eq. rewrite Bcompare_correct by assumption.
 destruct (Rcompare_spec (B x) (B y)); split; intros; try reflexivity; try discriminate; lra.
Qed.

Lemma checked_valid_finite h l : checked_valid h l=true -> finite h /\ finite l.
Proof. unfold checked_valid. rewrite !andb_true_iff. tauto. Qed.

Lemma checked_valid_normalized L H h l : (0<=H<=458)%Z ->
 in_range L H (B h) -> in_range L H (B l) -> checked_valid h l=true ->
 B h=rndF(B h+B l).
Proof.
 intros HH Rh Rl Valid. destruct (checked_valid_finite h l Valid) as [Fh Fl].
 assert (Bh:bnd 1 458 (B h)) by (apply (bnd_up 1 H);[lia|lia|now apply range_bnd with L]).
 assert (Bl:bnd 1 458 (B l)) by (apply (bnd_up 1 H);[lia|lia|now apply range_bnd with L]).
 assert (Sum:bnd 2 458 (B h+B l)) by (apply (bnd_plus 1 1);assumption).
 destruct (fadd_ok 2 458 h l Fh Fl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Sum) as [Fs Value].
 unfold checked_valid in Valid. apply andb_true_iff in Valid as [_ Eq].
 apply (checked_float_eq_spec _ _ Fs Fh) in Eq. transitivity (B(fadd h l));[symmetry;exact Eq|exact Value].
Qed.

Lemma checked_admit_value xh zh zl z : checked_admit xh zh zl=Some z -> z=(zh,zl).
Proof.
 unfold checked_admit. destruct (_ && _); intro E; [discriminate|now injection E].
Qed.

Lemma division_word_bound k E w : (0<=k<=512)%Z -> (E<=917)%Z ->
 bnd k E w -> Rabs w<=bpow radix2 926.
Proof.
 intros K Exp Bound.
 pose proof (bnd_up k E 917 w ltac:(lia) Exp Bound) as Up.
 pose proof (bnd_weaken k 512 917 w Up ltac:(lia)) as Wide.
 unfold bnd in Wide. change (IZR 512) with (bpow radix2 9) in Wide.
 rewrite <-bpow_plus in Wide. exact Wide.
Qed.

Theorem checked_divide_sound xh xl yh yl zh zl :
 checked_divide xh xl yh yl=Some(zh,zl) ->
 finite zh /\ finite zl /\
 Rabs ((B zh+B zl-(B xh+B xl)/(B yh+B yl))/((B xh+B xl)/(B yh+B yl)))
 <=15*bpow radix2 (-prec)^2+56*bpow radix2 (-prec)^3 /\
 Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926.
Proof.
 unfold checked_divide.
 destruct (checked_valid xh xl && checked_valid yh yl) eqn:Valid; [|discriminate].
 apply andb_true_iff in Valid as [X Y].
 destruct (checked_valid_finite _ _ X) as [Fxh Fxl].
 destruct (checked_valid_finite _ _ Y) as [Fyh Fyl].
 destruct (checked_float_eq yh checked_zero) eqn:Nonzero; [discriminate|].
 destruct (checked_quotient_range [xh;xl;yh;yl]) eqn:Range; [|discriminate].
 assert (Finite:Forall (fun w=>finite w) [xh;xl;yh;yl]) by (repeat constructor;assumption).
 pose proof (checked_quotient_range_sound _ Finite Range) as Ranges.
 destruct (quotient_extents [xh;xl;yh;yl]) as [L H].
 destruct Ranges as [L0 [H0 [Span Ranges]]].
 inversion Ranges as [|? ? Rxh Rest]; subst.
 inversion Rest as [|? ? Rxl Rest2]; subst.
 inversion Rest2 as [|? ? Ryh Rest3]; subst.
 inversion Rest3 as [|? ? Ryl Rest4]; subst.
 assert (Ex:B xh=rndF(B xh+B xl)) by (eapply (checked_valid_normalized L H);[lia|exact Rxh|exact Rxl|exact X]).
 assert (Ey:B yh=rndF(B yh+B yl)) by (eapply (checked_valid_normalized L H);[lia|exact Ryh|exact Ryl|exact Y]).
 assert (NZ:B yh<>0).
 { intro Zero. assert (Eq:checked_float_eq yh checked_zero=true).
   { apply checked_float_eq_spec;[exact Fyh|reflexivity|exact Zero]. }
   congruence. }
 pose proof (div_ieee L H xh xl yh yl L0 H0 Span Fxh Fxl Ex Fyh Fyl Ey NZ Rxh Rxl Ryh Ryl) as Bound.
 assert (Ly:bpow radix2 (-L)<=Rabs(B yh)) by (destruct Ryh as [Zero|[Lo _]];[contradiction|exact Lo]).
 destruct (div64_bounded L H xh xl yh yl L0 H0 Span Fxh Fxl Fyh Fyl
   (range_bnd _ _ _ Rxh) (range_bnd _ _ _ Rxl) (range_bnd _ _ _ Ryh) (range_bnd _ _ _ Ryl) Ly)
   as [_ [_ [_ [Bh Bl]]]].
 destruct (div64 xh xl yh yl) as [h l]. cbn [fst snd] in Bh,Bl.
 intro Accepted. apply checked_admit_value in Accepted. inversion Accepted;subst. destruct Bound as [Fh [Fl Err]].
 split;[exact Fh|]. split;[exact Fl|]. split;[exact Err|]. split.
 - apply (division_word_bound 172 (2*H+2*L));[lia|lia|exact Bh].
 - apply (division_word_bound 344 (2*H+2*L));[lia|lia|exact Bl].
Qed.

Lemma checked_admit_zero xh zh zl : finite xh -> finite zh -> finite zl ->
 B xh=0 -> checked_admit xh zh zl=Some(zh,zl) -> B zh=0 /\ B zl=0.
Proof.
 intros X H L Zero. unfold checked_admit.
 assert (XZ:checked_float_eq xh checked_zero=true) by (apply checked_float_eq_spec;[exact X|reflexivity|exact Zero]).
 rewrite XZ. simpl. destruct (checked_float_eq zh checked_zero) eqn:ZH; simpl; [|discriminate].
 destruct (checked_float_eq zl checked_zero) eqn:ZL; simpl; [|discriminate].
 intros _. split.
 - apply (checked_float_eq_spec zh checked_zero H eq_refl);exact ZH.
 - apply (checked_float_eq_spec zl checked_zero L eq_refl);exact ZL.
Qed.

Theorem checked_divide_zero xh xl yh yl zh zl :
 checked_divide xh xl yh yl=Some(zh,zl) -> B xh=0 -> B zh=0 /\ B zl=0.
Proof.
 intros Accepted Zero.
 destruct (checked_divide_sound _ _ _ _ _ _ Accepted) as [Fzh [Fzl _]].
 unfold checked_divide in Accepted.
 destruct (checked_valid xh xl && checked_valid yh yl) eqn:V;[|discriminate].
 apply andb_true_iff in V as [X _]. destruct (checked_valid_finite _ _ X) as [Fxh _].
 destruct (checked_float_eq yh checked_zero);[discriminate|].
 destruct (checked_quotient_range [xh;xl;yh;yl]);[|discriminate].
 destruct (div64 xh xl yh yl) as [h l].
 pose proof (checked_admit_value _ _ _ _ Accepted) as Eq. inversion Eq;subst.
 eapply checked_admit_zero; eassumption.
Qed.
