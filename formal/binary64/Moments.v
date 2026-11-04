(* Exact moment identities and propagation of certified absolute errors.
   The primitive rounding and domain contracts belong to IEEE64Add/Mul/Div
   and FiniteInterval; this file does not translate Rust control flow. *)
From Coq Require Import Reals Lra Psatz List.
Open Scope R_scope.

Lemma relative_error_from_result z r e :
  0 <= e <= /2 -> Rabs (r-z) <= e*Rabs z ->
  Rabs (r-z) <= 2*e*Rabs r.
Proof.
  intros E B.
  assert (T : Rabs z <= Rabs r + Rabs (r-z)).
  { replace z with (r + -(r-z)) at 1 by ring.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
  pose proof (Rabs_pos (r-z)).
  assert (M : e*Rabs z <= e*(Rabs r + Rabs (r-z))).
  { apply Rmult_le_compat_l; lra. }
  nra.
Qed.

Lemma add_radius a b x y ea eb :
  Rabs (a-x) <= ea -> Rabs (b-y) <= eb ->
  Rabs ((a+b)-(x+y)) <= ea+eb.
Proof.
  intros A B. replace ((a+b)-(x+y)) with ((a-x)+(b-y)) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

Lemma mul_radius a b x y ea eb :
  Rabs (a-x) <= ea -> Rabs (b-y) <= eb ->
  Rabs (a*b-x*y) <= Rabs a*eb + Rabs b*ea + ea*eb.
Proof.
  intros A B.
  pose proof (Rabs_pos (a-x)) as AX.
  pose proof (Rabs_pos (b-y)) as BY.
  pose proof (Rabs_pos a) as PA.
  pose proof (Rabs_pos b) as PB.
  replace (a*b-x*y) with
    ((a*(b-y)+b*(a-x)) + -((a-x)*(b-y))) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite Rabs_Ropp, Rabs_mult.
  pose proof (Rabs_triang (a*(b-y)) (b*(a-x))) as T.
  rewrite !Rabs_mult in T.
  assert (C : Rabs (a-x)*Rabs (b-y) <= ea*eb).
  { apply Rmult_le_compat; lra. }
  nra.
Qed.

Lemma local_error_composition actual intermediate rounded propagated local :
  Rabs (intermediate-actual) <= propagated ->
  Rabs (rounded-intermediate) <= local ->
  Rabs (rounded-actual) <= propagated+local.
Proof.
  intros A B. replace (rounded-actual) with
    ((intermediate-actual)+(rounded-intermediate)) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

Lemma div_radius a x ea n :
  0 < n -> Rabs (a-x) <= ea -> Rabs (a/n-x/n) <= ea/n.
Proof.
  intros N A. replace (a/n-x/n) with ((a-x)* /n) by (unfold Rdiv; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (/n)).
  - unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat |]; assumption.
  - left. apply Rinv_0_lt_compat. assumption.
Qed.

Lemma project_nonnegative r x e :
  0 <= x -> Rabs (r-x) <= e -> Rabs (Rmax 0 r-x) <= e.
Proof.
  intros X E. destruct (Rle_dec 0 r) as [R|R].
  - rewrite Rmax_right by assumption. exact E.
  - rewrite Rmax_left by lra. rewrite Rabs_left1 by lra.
    rewrite Rabs_left1 in E by lra. lra.
Qed.

Lemma translated_centered_sum n s q d : n <> 0 ->
  (q+2*d*s+n*d*d) - (s+n*d)*(s+n*d)/n = q-s*s/n.
Proof. intro N. field. exact N. Qed.

Lemma chan_combination na nb ma mb qa qb :
  na <> 0 -> nb <> 0 -> na+nb <> 0 ->
  qa+na*ma*ma + qb+nb*mb*mb -
    (na*ma+nb*mb)*(na*ma+nb*mb)/(na+nb) =
  qa+qb+(mb-ma)*(mb-ma)*(na*nb/(na+nb)).
Proof. intros A B N. field. exact N. Qed.

Fixpoint centered_sum (a : R) (xs : list R) : R :=
  match xs with nil => 0 | cons x rest => (x-a)+centered_sum a rest end.
Fixpoint centered_squares (a : R) (xs : list R) : R :=
  match xs with nil => 0 | cons x rest => (x-a)*(x-a)+centered_squares a rest end.

Lemma centered_sum_append a xs ys :
  centered_sum a (xs++ys) = centered_sum a xs + centered_sum a ys.
Proof. induction xs; simpl; [ring | rewrite IHxs; ring]. Qed.

Lemma centered_squares_append a xs ys :
  centered_squares a (xs++ys) = centered_squares a xs + centered_squares a ys.
Proof. induction xs; simpl; [ring | rewrite IHxs; ring]. Qed.

Lemma centered_sum_shift xs a b :
  centered_sum a xs = centered_sum b xs + INR (length xs)*(b-a).
Proof.
  induction xs as [|x xs IH]; cbn [centered_sum length].
  - simpl. ring.
  - rewrite S_INR, IH. ring.
Qed.

Lemma centered_squares_shift xs a b :
  centered_squares a xs = centered_squares b xs +
    2*(b-a)*centered_sum b xs + INR (length xs)*(b-a)*(b-a).
Proof.
  induction xs as [|x xs IH]; cbn [centered_squares centered_sum length].
  - simpl. ring.
  - rewrite S_INR, IH. ring.
Qed.

Lemma anchored_mean xs a : INR (length xs) <> 0 ->
  a + centered_sum a xs / INR (length xs) =
  centered_sum 0 xs / INR (length xs).
Proof.
  intro N. rewrite (centered_sum_shift xs 0 a). field. exact N.
Qed.

Lemma centered_second_moment xs a : INR (length xs) <> 0 ->
  centered_squares (a + centered_sum a xs / INR (length xs)) xs =
  centered_squares a xs -
    centered_sum a xs * centered_sum a xs / INR (length xs).
Proof.
  intro N. rewrite (centered_squares_shift xs
    (a + centered_sum a xs / INR (length xs)) a). field. exact N.
Qed.

Lemma centered_squares_nonnegative xs a : 0 <= centered_squares a xs.
Proof.
  induction xs as [|x xs IH]; cbn [centered_squares]; [lra |].
  pose proof (Rle_0_sqr (x-a)). unfold Rsqr in H. lra.
Qed.

Lemma second_moment_nonnegative xs a : INR (length xs) <> 0 ->
  0 <= centered_squares a xs -
    centered_sum a xs * centered_sum a xs / INR (length xs).
Proof.
  intro N. rewrite <- centered_second_moment by exact N.
  apply centered_squares_nonnegative.
Qed.
