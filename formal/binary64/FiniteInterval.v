(** Conservative finite intervals. This proof concerns real values and
    binary64 nearest rounding followed by predecessor/successor. The Rust
    implementation rejects nonfinite neighbours; see docs/interval.md for
    the primitive correspondence and the limits of this source binding. *)
From Coq Require Import Reals Lra Psatz.
From Flocq Require Import Core.
Open Scope R_scope.

Notation fexp := (FLT_exp (-1074) 53).
#[local] Instance prec53 : Prec_gt_0 53 := eq_refl.
Definition rn (x : R) := round radix2 fexp (Znearest (fun n => negb (Z.even n))) x.
Definition down (x : R) := pred radix2 fexp (rn x).
Definition up (x : R) := succ radix2 fexp (rn x).
Definition encloses (l u x : R) := l <= x /\ x <= u.

Theorem neighbour_enclosure x : encloses (down x) (up x) x.
Proof.
 split; [apply pred_round_le_id | apply succ_round_ge_id];
 auto with typeclass_instances.
Qed.

Theorem monotone_enclosure (f : R -> R) l u x :
 encloses l u x ->
 (forall a b, l <= a -> a <= b -> b <= u -> f a <= f b) ->
 encloses (down (f l)) (up (f u)) (f x).
Proof.
 intros [L U] M. destruct (neighbour_enclosure (f l)).
 destruct (neighbour_enclosure (f u)). split;
 [specialize (M l x ltac:(lra) L U) | specialize (M x u L U ltac:(lra))]; lra.
Qed.

Theorem add_enclosure l u a b x y :
 encloses l u x -> encloses a b y ->
 encloses (down (l+a)) (up (u+b)) (x+y).
Proof.
 intros [L U] [A B]. destruct (neighbour_enclosure (l+a)).
 destruct (neighbour_enclosure (u+b)). split; lra.
Qed.
Theorem sub_enclosure l u a b x y :
 encloses l u x -> encloses a b y ->
 encloses (down (l-b)) (up (u-a)) (x-y).
Proof.
 intros [L U] [A B]. destruct (neighbour_enclosure (l-b)).
 destruct (neighbour_enclosure (u-a)). split; lra.
Qed.
Theorem negate_enclosure l u x :
 encloses l u x -> encloses (-u) (-l) (-x).
Proof. unfold encloses; lra. Qed.

Lemma linear_corners l u x z lo hi : encloses l u x ->
 encloses lo hi (l*z) -> encloses lo hi (u*z) -> encloses lo hi (x*z).
Proof.
 unfold encloses. intros [L U] [A B] [C D].
 destruct (Rle_dec 0 z); split; nra.
Qed.
Theorem product_corners l u a b x y lo hi :
 encloses l u x -> encloses a b y ->
 encloses lo hi (l*a) -> encloses lo hi (l*b) ->
 encloses lo hi (u*a) -> encloses lo hi (u*b) ->
 encloses lo hi (x*y).
Proof.
 intros X Y LA LB UA UB. apply (linear_corners l u x y lo hi X).
 - replace (l*y) with (y*l) by ring.
   apply (linear_corners a b y l lo hi Y); replace (a*l) with (l*a) by ring;
   replace (b*l) with (l*b) by ring; assumption.
 - replace (u*y) with (y*u) by ring.
   apply (linear_corners a b y u lo hi Y); replace (a*u) with (u*a) by ring;
   replace (b*u) with (u*b) by ring; assumption.
Qed.

Theorem reciprocal_enclosure l u x : encloses l u x ->
 (0 < l \/ u < 0) -> encloses (down (/u)) (up (/l)) (/x).
Proof.
 intros [L U] D. destruct (neighbour_enclosure (/u)).
 destruct (neighbour_enclosure (/l)).
 assert (M : forall a b, a <= b -> (0 < a \/ b < 0) -> /b <= /a).
 { intros a b AB [A | B].
   - apply Rinv_le_contravar; assumption.
   - assert (T : /(-a) <= /(-b)).
     { apply Rinv_le_contravar; lra. }
     rewrite <- !Ropp_inv_permute in T by lra. lra. }
 assert (A : /u <= /x) by (apply M; tauto || lra).
 assert (B : /x <= /l) by (apply M; tauto || lra).
 split; lra.
Qed.

Theorem nonnegative_clamp l u x : encloses l u x -> 0 <= x ->
 encloses (Rmax 0 l) u x.
Proof.
 intros [L U] X. split; [apply Rmax_lub; assumption | assumption].
Qed.
Theorem abs_positive l u x : encloses l u x -> 0 <= l ->
 encloses l u (Rabs x).
Proof. intros [L U] P. rewrite Rabs_pos_eq by lra. split; assumption. Qed.
Theorem abs_negative l u x : encloses l u x -> u <= 0 ->
 encloses (-u) (-l) (Rabs x).
Proof. intros [L U] P. rewrite Rabs_left1 by lra. split; lra. Qed.
Theorem abs_crossing l u x : encloses l u x -> l <= 0 -> 0 <= u ->
 encloses 0 (Rmax (-l) u) (Rabs x).
Proof.
 intros [L U] N P. split; [apply Rabs_pos |].
 destruct (Rle_dec 0 x).
 - rewrite Rabs_pos_eq by assumption. eapply Rle_trans; [exact U | apply Rmax_r].
 - rewrite Rabs_left1 by lra. apply Rle_trans with (-l); [lra | apply Rmax_l].
Qed.
Theorem max_enclosure l u a b x y :
 encloses l u x -> encloses a b y ->
 encloses (Rmax l a) (Rmax u b) (Rmax x y).
Proof.
 intros [L U] [A B]. split; apply Rmax_lub.
 - eapply Rle_trans; [exact L | apply Rmax_l].
 - eapply Rle_trans; [exact A | apply Rmax_r].
 - eapply Rle_trans; [exact U | apply Rmax_l].
 - eapply Rle_trans; [exact B | apply Rmax_r].
Qed.
Theorem square_enclosure l u x : encloses l u x -> 0 <= l ->
 encloses (Rmax 0 (down (l*l))) (up (u*u)) (x*x).
Proof.
 intros X L. apply nonnegative_clamp; [|nra].
 apply (monotone_enclosure (fun z => z*z) l u x X).
 intros a b A B C. nra.
Qed.
Theorem exp_enclosure l u x : encloses l u x ->
 encloses (Rmax 0 (down (exp l))) (up (exp u)) (exp x).
Proof.
 intros X. apply nonnegative_clamp; [|left; apply exp_pos].
 apply (monotone_enclosure exp l u x X). intros a b A B C.
 destruct B as [B | B]; [left; apply exp_increasing; assumption | subst; right; reflexivity].
Qed.
Theorem sqrt_enclosure l u x : encloses l u x -> 0 <= l ->
 encloses (Rmax 0 (down (sqrt l))) (up (sqrt u)) (sqrt x).
Proof.
 intros X L. apply nonnegative_clamp; [|apply sqrt_pos].
 apply (monotone_enclosure sqrt l u x X). intros a b A B C.
 apply sqrt_le_1; lra.
Qed.
Theorem ln_enclosure l u x : encloses l u x -> 0 < l ->
 encloses (down (ln l)) (up (ln u)) (ln x).
Proof.
 intros X L. apply (monotone_enclosure ln l u x X). intros a b A B C.
 destruct B as [B | B]; [left; apply ln_increasing; lra | subst; right; reflexivity].
Qed.
