(** Public ln and ln_1p entries, with screens, decisions, and accurate paths. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest Encodings.
From Q Require Q128.
From Interval Require Import Tactic.
Require Import Exp2 ExpAccurate ExpFast LnAccurate LnStage Ln1p Ln1pScreen Ln1pStageH Ln1pStageB
 LnFastDecision LnEntryLemmas Ln1pLemmas.
Open Scope R_scope.
Definition lf_tiny : f64 := b64_of_bits 4363988038922010624.
Definition lf_minus_one : f64 := b64_of_bits 13830554455654793216.
Definition lf_nan : f64 := b64_of_bits 9221120237041090560.
Definition lf_neg_inf : f64 := b64_of_bits 18442240474082181120.
Definition lf_infinite (x:f64) := match x with B754_infinity _ => true | _ => false end.
Definition lf_eq a b := match Bcompare 53 1024 a b with Some Eq => true | _ => false end.
Lemma lf_tiny_ok : finite lf_tiny /\ B lf_tiny=/2^54.
Proof. split; [exact (bits_finite 4363988038922010624 false 4503599627370496 (-106) eq_refl) | ].
unfold lf_tiny. rewrite (bits_val 4363988038922010624 false 4503599627370496 106 eq_refl); cbn [SpecFloat.cond_Zopp]; field. Qed.
Lemma lf_minus_one_ok : finite lf_minus_one /\ B lf_minus_one= -1.
Proof. split; [exact (bits_finite 13830554455654793216 true 4503599627370496 (-52) eq_refl) | ].
unfold lf_minus_one. rewrite (bits_val 13830554455654793216 true 4503599627370496 52 eq_refl). change ((-4503599627370496)/2^52= -1). field. Qed.
Lemma lf_eq_ok a b : finite a -> finite b -> (lf_eq a b=true <-> B a=B b).
Proof.
 intros Fa Fb. unfold lf_eq. rewrite Bcompare_correct by assumption.
 destruct (Rcompare_spec (B a) (B b)); split; intros; try reflexivity; try discriminate; lra.
Qed.
Definition ln_entry x :=
 if is_nan 53 1024 x then x else
 if flt x c_zero then lf_nan else
 if lf_eq x c_zero then lf_neg_inf else
 if lf_infinite x then x else
 if lf_eq x c_one then c_zero else
 match ln_stage x with Some y => y | None =>
 match lf_ln_fast x with Some y => y | None => Q128.to_f64 (ln_acc x) end end.
Definition ln1p_reference_entry x :=
 if is_nan 53 1024 x then x else
 if flt x lf_minus_one then lf_nan else
 if lf_eq x lf_minus_one then lf_neg_inf else
 if lf_infinite x then x else
 if flt (b64_abs x) lf_tiny then x else
 match lf_ln1p_fast x with Some y => y | None => Q128.to_f64 (ln_1p_acc x) end.
Definition ln1p_entry x := match ln_1p_stages x with Some y => y | None => ln1p_reference_entry x end.
Lemma lf_finite_screens x : finite x -> is_nan 53 1024 x=false /\ lf_infinite x=false.
Proof. intros F; destruct x; try discriminate; split; reflexivity. Qed.
Lemma lf_not_eq a b : finite a -> finite b -> B a<>B b -> lf_eq a b=false.
Proof. intros Fa Fb N; destruct (lf_eq a b) eqn:E; [apply lf_eq_ok in E; auto; contradiction | reflexivity]. Qed.
Theorem ln_entry_regular x : finite x -> 0<B x -> B x<>1 ->
 midpoint_far (Rabs(ln(B x))) (/2^118) -> finite (ln_entry x) /\ B (ln_entry x)=rndF(ln(B x)).
Proof.
 intros Fx Px Nx Far. destruct (lf_finite_screens x Fx) as [Nan Inf].
 assert (Neg : flt x c_zero=false) by (apply (proj2 (flt_false _ _ Fx c_zero_finite)); rewrite c_zero_val; lra).
 assert (Zero : lf_eq x c_zero=false) by (apply lf_not_eq; try assumption; [exact c_zero_finite | rewrite c_zero_val; lra]).
 assert (One : lf_eq x c_one=false) by (apply lf_not_eq; try assumption; [exact c_one_finite | rewrite c_one_val; intro Z; apply Nx; rewrite Z; field]).
 unfold ln_entry; rewrite Nan,Neg,Zero,Inf,One.
 destruct (ln_stage x) as [y | ] eqn:S.
 - destruct (ln_stage_ok x y Fx Px Nx S) as [Fy [V _]]; auto.
 - destruct (lf_ln_fast x) as [y | ] eqn:F; [exact (lf_ln_fast_ok x y Fx Px Nx F) | ].
   pose proof (ln_accurate_ok x Fx Px Nx Far) as V.
   destruct (ln_acc_ok x Fx Px Nx) as [_ [E R]].
   split; [eapply lf_rounded_approx_finite; [exact R | exact (lf_ln_away x Fx Px Nx) | exact E] | exact V].
Qed.
Definition lf_bounded_ln1p x y := finite y /\ exists v, B y=rndF v /\
 Rabs(v-ln(1+B x))<=/2^123*Rabs(ln(1+B x)).
Lemma lf_exact_ln1p x y : finite y -> B y=rndF(ln(1+B x)) -> lf_bounded_ln1p x y.
Proof.
 intros F V. split; [exact F | exists (ln(1+B x)); split; [exact V | ]].
 rewrite Rminus_diag_eq,Rabs_R0 by reflexivity. apply Rmult_le_pos; [interval with (i_prec 160) | apply Rabs_pos].
Qed.
Lemma lf_stages_finite x y : ln_1p_stages x=Some y -> finite y.
Proof.
 unfold ln_1p_stages. destruct (h_screen x) eqn:H.
 - destruct (stage_h x) as [v | ] eqn:S.
   + intros E; injection E as <-. destruct (h_screen_ok x H) as [F [A X]].
     exact (proj1 (stage_h_ok x v F A X S)).
   + destruct (b_screen x) eqn:B; [ | discriminate]. intros E.
     destruct (b_screen_ok x B) as [F [A X]]. exact (proj1 (stage_b_ok x y F A X E)).
 - destruct (b_screen x) eqn:B; [ | discriminate]. intros E.
   destruct (b_screen_ok x B) as [F [A X]]. exact (proj1 (stage_b_ok x y F A X E)).
Qed.
Theorem ln1p_entry_regular x : finite x -> -1<B x -> lf_bounded_ln1p x (ln1p_entry x).
Proof.
 intros Fx X. unfold ln1p_entry. destruct (ln_1p_stages x) as [y | ] eqn:S.
 - destruct (ln_1p_stages_ok x y S) as [_ [V _]]. apply lf_exact_ln1p; [apply lf_stages_finite with x; exact S | exact V].
 - unfold ln1p_reference_entry. destruct (lf_finite_screens x Fx) as [Nan Inf].
   destruct lf_minus_one_ok as [Fm Vm]. destruct lf_tiny_ok as [Ft Vt].
   assert (Neg : flt x lf_minus_one=false) by (apply (proj2 (flt_false _ _ Fx Fm)); rewrite Vm; lra).
   assert (Minus : lf_eq x lf_minus_one=false) by (apply lf_not_eq; try assumption; rewrite Vm; lra).
   rewrite Nan,Neg,Minus,Inf. destruct (flt (b64_abs x) lf_tiny) eqn:T.
   + apply (flt_true _ _ ltac:(unfold b64_abs; rewrite is_finite_Babs; exact Fx) Ft) in T.
     rewrite B_abs,Vt in T. apply lf_exact_ln1p; [exact Fx | symmetry; apply lf_tiny_round; [exact T | apply B_fmt]].
   + apply (flt_false _ _ ltac:(unfold b64_abs; rewrite is_finite_Babs; exact Fx) Ft) in T.
     rewrite B_abs,Vt in T. assert (A : bpow radix2 (-54)<=Rabs(B x)) by (apply Rle_trans with (2:=T); interval with (i_prec 100)).
     destruct (lf_ln1p_fast x) as [y | ] eqn:F.
     * destruct (lf_ln1p_fast_ok x y Fx X A F) as [Fy V]; apply lf_exact_ln1p; assumption.
     * destruct (ln_1p_acc_ok x Fx X A) as [_ [E R]].
       split; [eapply lf_rounded_approx_finite; [exact R | exact (ln1p_away (B x) X A) | exact E] | ].
       exists (Q128.qval (ln_1p_acc x)); split; assumption.
Qed.

Theorem ln_entry_specials :
 ln_entry (b64_of_bits 0)=lf_neg_inf /\
 ln_entry (b64_of_bits 9223372036854775808)=lf_neg_inf /\
 ln_entry (b64_of_bits 4607182418800017408)=c_zero /\
 ln_entry (b64_of_bits 9218868437227405312)=b64_of_bits 9218868437227405312 /\
 ln_entry (b64_of_bits 18442240474082181120)=lf_nan.
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem ln1p_entry_specials :
 ln1p_entry (b64_of_bits 0)=b64_of_bits 0 /\
 ln1p_entry (b64_of_bits 9223372036854775808)=b64_of_bits 9223372036854775808 /\
 ln1p_entry lf_minus_one=lf_neg_inf /\
 ln1p_entry (b64_of_bits 9218868437227405312)=b64_of_bits 9218868437227405312 /\
 ln1p_entry (b64_of_bits 18442240474082181120)=lf_nan.
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem ln_entry_nan x : is_nan 53 1024 x=true -> ln_entry x=x.
Proof. intros H; unfold ln_entry; rewrite H; reflexivity. Qed.
Theorem ln1p_entry_nan x : is_nan 53 1024 x=true -> ln1p_entry x=x.
Proof.
 intros H. unfold ln1p_entry. destruct (ln_1p_stages x) as [y | ] eqn:S.
 - destruct (ln_1p_stages_ok x y S) as [F _]. destruct (lf_finite_screens x F) as [N _]; congruence.
 - unfold ln1p_reference_entry; rewrite H; reflexivity.
Qed.
Theorem ln_entry_negative x : finite x -> B x<0 -> ln_entry x=lf_nan.
Proof.
 intros Fx X. destruct (lf_finite_screens x Fx) as [Nan _]. unfold ln_entry; rewrite Nan.
 assert (N : flt x c_zero=true) by (apply (proj2 (flt_true _ _ Fx c_zero_finite)); rewrite c_zero_val; exact X).
 rewrite N; reflexivity.
Qed.
Lemma lf_stages_domain x y : ln_1p_stages x=Some y -> -1<B x.
Proof.
 unfold ln_1p_stages. destruct (h_screen x) eqn:H.
 - destruct (stage_h x) as [v | ] eqn:S.
   + intros _. destruct (h_screen_ok x H) as [_ [_ X]]; tauto.
   + destruct (b_screen x) eqn:B; [ | discriminate]. intros _.
     destruct (b_screen_ok x B) as [_ [_ X]]; tauto.
 - destruct (b_screen x) eqn:B; [ | discriminate]. intros _.
   destruct (b_screen_ok x B) as [_ [_ X]]; tauto.
Qed.
Theorem ln1p_entry_below_domain x : finite x -> B x< -1 -> ln1p_entry x=lf_nan.
Proof.
 intros Fx X. unfold ln1p_entry. destruct (ln_1p_stages x) as [y | ] eqn:S.
 - pose proof (lf_stages_domain x y S); lra.
 - destruct (lf_finite_screens x Fx) as [Nan _]. unfold ln1p_reference_entry; rewrite Nan.
   destruct lf_minus_one_ok as [Fm Vm].
   assert (N : flt x lf_minus_one=true) by (apply (proj2 (flt_true _ _ Fx Fm)); rewrite Vm; exact X).
   rewrite N; reflexivity.
Qed.
