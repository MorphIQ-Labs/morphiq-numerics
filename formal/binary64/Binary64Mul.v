(** Double-word multiplication in binary64, with gradual underflow, meets the
    bounds Muller and Rideau prove in the unbounded-exponent model, on a domain
    stated on the inputs.

    Beyond the sums Binary64Add.v bridges, mul_f64 and mul round products of
    their inputs and call two_prod. A product rounds identically in binary64
    and in the unbounded model when it is zero or at least 2^-1022 in magnitude
    ([round_FLT_FLX]). On two_prod's domain (zero, or at least 2^-969), Dekker's
    algorithm returns RN(a b) and the exact error ([two_prod_exact]), which is
    what Fast2Mult returns in the unbounded model, since there a product's
    rounding error is representable ([mult_error_FLX]). Overflow is outside
    both models; docs/double-word.md states the magnitudes that exclude it. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core Mult_error Relative.
From Double Require Import DWPlus F2Sum DWTimesFP DWTimesDW.
From Binary64 Require Import Binary64Add.
From Binary64 Require Instances.
Require TwoProdBinary64.

Open Scope R_scope.

(** A product, or any value, at least 2^-1022 in magnitude or zero, rounds
    alike in both models. *)
Lemma normal_round z : z = 0 \/ bpow radix2 (-1022) <= Rabs z -> rndF z = rndX z.
Proof.
  intros [-> | H].
  - rewrite (round_0 radix2 (FLT_exp emin prec) (Znearest ne)).
    now rewrite (round_0 radix2 (FLX_exp prec) (Znearest ne)).
  - apply round_FLT_FLX. exact H.
Qed.

Definition two_prod (a b : R) : R * R :=
  (TwoProdBinary64.two_prod_p a b, TwoProdBinary64.two_prod_e a b).

Definition in_two_prod_domain (a b : R) : Prop :=
  a * b = 0 \/ bpow radix2 (-969) <= Rabs (a * b).

Definition normal_or_zero (z : R) : Prop :=
  z = 0 \/ bpow radix2 (-1022) <= Rabs z.

Lemma two_prod_domain_normal a b : in_two_prod_domain a b -> normal_or_zero (a * b).
Proof.
  intros [H | H]; [now left | right].
  apply Rle_trans with (2 := H). apply bpow_le. lia.
Qed.

(** On its domain, the Rust two_prod is Fast2Mult in the unbounded model. *)
Lemma two_prod_eq a b : fmtF a -> fmtF b -> in_two_prod_domain a b ->
  two_prod a b = Fast2Mult prec ne a b.
Proof.
  intros Fa Fb D.
  pose proof (TwoProdBinary64.two_prod_exact a b Fa Fb D) as Ex.
  unfold two_prod, Fast2Mult.
  assert (P : TwoProdBinary64.two_prod_p a b = rndX (a * b)).
  { unfold TwoProdBinary64.two_prod_p.
    exact (normal_round (a * b) (two_prod_domain_normal a b D)). }
  f_equal; [exact P | ].
  assert (E : TwoProdBinary64.two_prod_e a b = a * b - rndX (a * b)) by (rewrite <- P; lra).
  rewrite E. symmetry. apply round_generic; auto with typeclass_instances.
  replace (a * b - rndX (a * b)) with (- (rndX (a * b) - a * b)) by ring.
  apply generic_format_opp, mult_error_FLX; auto with typeclass_instances; now apply fmtF_fmtX.
Qed.

Lemma two_prod_fmt a b : fmtF (fst (two_prod a b)) /\ fmtF (snd (two_prod a b)).
Proof. split; apply fmtF_rnd. Qed.

(** The binary64 algorithms, as the Rust functions compute them. *)
Definition mul_f64 (xh xl y : R) : R * R :=
  let '(ch, cl1) := two_prod xh y in
  let cl2 := rndF (xl * y) in
  let '(th, tl1) := fast_two_sum ch cl2 in
  let tl2 := rndF (tl1 + cl1) in
  fast_two_sum th tl2.

Definition mul (xh xl yh yl : R) : R * R :=
  let '(ch, cl1) := two_prod xh yh in
  let tl1 := rndF (xh * yl) in
  let tl2 := rndF (xl * yh) in
  let cl2 := rndF (tl1 + tl2) in
  let cl3 := rndF (cl1 + cl2) in
  fast_two_sum ch cl3.

Lemma dw_fmt xh xl : double_word prec ne xh xl -> fmtX xh /\ fmtX xl.
Proof. now intros [[Fh Fl] _]. Qed.

(** On its domain, mul_f64 is DWTimesFP in the unbounded model, step by step. *)
Lemma mul_f64_eq xh xl y :
  fmtF xh -> fmtF xl -> fmtF y ->
  in_two_prod_domain xh y -> normal_or_zero (xl * y) ->
  mul_f64 xh xl y = DWTimesFP prec ne xh xl y.
Proof.
  intros Fxh Fxl Fy Dh Dl.
  unfold mul_f64, DWTimesFP. rewrite TwoProd_Fast2Mult.
  rewrite (two_prod_eq xh y Fxh Fy Dh).
  assert (Fch : fmtF (fst (Fast2Mult prec ne xh y)))
    by (rewrite <- (two_prod_eq xh y Fxh Fy Dh); apply two_prod_fmt).
  assert (Fcl1 : fmtF (snd (Fast2Mult prec ne xh y)))
    by (rewrite <- (two_prod_eq xh y Fxh Fy Dh); apply two_prod_fmt).
  destruct (Fast2Mult prec ne xh y) as [ch cl1]. cbn [fst snd] in Fch, Fcl1 |- *.
  rewrite (normal_round _ Dl).
  assert (Fcl2 : fmtF (rndX (xl * y))) by (rewrite <- (normal_round _ Dl); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fch Fcl2).
  destruct (fast_two_sum_fmt _ _ Fch Fcl2) as [Fth Ftl1].
  destruct (F2Sum.Fast2Sum prec ne ch (rndX (xl * y))) as [th tl1].
  cbn [fst snd] in Fth, Ftl1 |- *.
  rewrite (sum_round _ _ Ftl1 Fcl1).
  assert (Ftl2 : fmtF (rndX (tl1 + cl1))) by (rewrite <- (sum_round _ _ Ftl1 Fcl1); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fth Ftl2).
  now destruct (F2Sum.Fast2Sum prec ne th (rndX (tl1 + cl1))).
Qed.

Theorem mul_f64_bound xh xl y :
  fmtF xh -> fmtF xl -> fmtF y -> xh = rndF (xh + xl) ->
  in_two_prod_domain xh y -> normal_or_zero (xl * y) ->
  let '(zh, zl) := mul_f64 xh xl y in
  let xy := (xh + xl) * y in
  Rabs ((zh + zl - xy) / xy) <= 3 / 2 * bpow radix2 (- prec) ^ 2 + 4 * bpow radix2 (- prec) ^ 3.
Proof.
  intros Fxh Fxl Fy E Dh Dl.
  rewrite (mul_f64_eq xh xl y Fxh Fxl Fy Dh Dl).
  exact (Instances.mul_f64_bound xh xl y (dw_of_binary64 xh xl Fxh Fxl E) (fmtF_fmtX y Fy)).
Qed.

Theorem mul_bound xh xl yh yl :
  fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  fmtF yh -> fmtF yl -> yh = rndF (yh + yl) ->
  in_two_prod_domain xh yh -> normal_or_zero (xh * yl) -> normal_or_zero (xl * yh) ->
  let '(zh, zl) := mul xh xl yh yl in
  let xy := (xh + xl) * (yh + yl) in
  Rabs ((zh + zl - xy) / xy) < 5 * (bpow radix2 (- prec) * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Dhh Dhl Dlh.
  pose proof (Instances.mul_bound xh xl yh yl
                (dw_of_binary64 xh xl Fxh Fxl Ex) (dw_of_binary64 yh yl Fyh Fyl Ey)) as B.
  unfold mul.
  rewrite (two_prod_eq xh yh Fxh Fyh Dhh).
  assert (Fcl1 : fmtF (snd (Fast2Mult prec ne xh yh)))
    by (rewrite <- (two_prod_eq xh yh Fxh Fyh Dhh); apply two_prod_fmt).
  assert (Fch : fmtF (fst (Fast2Mult prec ne xh yh)))
    by (rewrite <- (two_prod_eq xh yh Fxh Fyh Dhh); apply two_prod_fmt).
  unfold DWTimesDW1 in B. rewrite TwoProd_Fast2Mult in B.
  destruct (Fast2Mult prec ne xh yh) as [ch cl1] eqn:C. cbn [fst snd] in Fch, Fcl1.
  rewrite (normal_round _ Dhl), (normal_round _ Dlh).
  assert (Ft1 : fmtF (rndX (xh * yl))) by (rewrite <- (normal_round _ Dhl); apply fmtF_rnd).
  assert (Ft2 : fmtF (rndX (xl * yh))) by (rewrite <- (normal_round _ Dlh); apply fmtF_rnd).
  rewrite (sum_round _ _ Ft1 Ft2).
  assert (Fc2 : fmtF (rndX (rndX (xh * yl) + rndX (xl * yh))))
    by (rewrite <- (sum_round _ _ Ft1 Ft2); apply fmtF_rnd).
  rewrite (sum_round _ _ Fcl1 Fc2).
  assert (Fc3 : fmtF (rndX (cl1 + rndX (rndX (xh * yl) + rndX (xl * yh)))))
    by (rewrite <- (sum_round _ _ Fcl1 Fc2); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fch Fc3).
  exact B.
Qed.

(** [mul]'s result is a double-word number: its closing Fast2Sum adds a
    correction at most [6u] relative to the leading product, so it is exact. *)
Theorem mul_dw xh xl yh yl :
  fmtF xh -> fmtF xl -> xh = rndF (xh + xl) ->
  fmtF yh -> fmtF yl -> yh = rndF (yh + yl) ->
  in_two_prod_domain xh yh -> normal_or_zero (xh * yl) -> normal_or_zero (xl * yh) ->
  let '(zh, zl) := mul xh xl yh yl in zh = rndF (zh + zl).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Dhh Dhl Dlh.
  set (u := / 9007199254740992).
  assert (U : 0 < u < / 1000) by (unfold u; lra).
  (* The unbounded model's rounding errs by at most u relatively. *)
  assert (Rel : forall v, Rabs (rndX v - v) <= u * Rabs v).
  { intros v. pose proof (relative_error_N_FLX radix2 prec (ltac:(unfold prec; lia)) ne v) as H.
    replace (/ 2 * bpow radix2 (- prec + 1)) with u in H by (unfold u, prec; simpl; lra). exact H. }
  assert (Up : forall v, Rabs (rndX v) <= (1 + u) * Rabs v).
  { intros v. pose proof (Rel v). pose proof (Rabs_triang_inv (rndX v) v). lra. }
  assert (Lo : forall h l, h = rndX (h + l) -> Rabs l <= 2 * u * Rabs h).
  { intros h l E. pose proof (Rel (h + l)) as H. rewrite <- E in H.
    replace (h - (h + l)) with (- l) in H by ring. rewrite Rabs_Ropp in H.
    assert (A : Rabs l <= u * (Rabs h + Rabs l))
      by (apply Rle_trans with (1 := H); apply Rmult_le_compat_l; [lra | apply Rabs_triang]).
    pose proof (Rabs_pos h). unfold u in *. lra. }
  destruct (dw_of_binary64 xh xl Fxh Fxl Ex) as [_ Ex'].
  destruct (dw_of_binary64 yh yl Fyh Fyl Ey) as [_ Ey'].
  pose proof (Lo _ _ Ex') as Lx. pose proof (Lo _ _ Ey') as Ly.
  unfold mul.
  rewrite (two_prod_eq xh yh Fxh Fyh Dhh).
  assert (Fcl1 : fmtF (snd (Fast2Mult prec ne xh yh)))
    by (rewrite <- (two_prod_eq xh yh Fxh Fyh Dhh); apply two_prod_fmt).
  assert (Fch : fmtF (fst (Fast2Mult prec ne xh yh)))
    by (rewrite <- (two_prod_eq xh yh Fxh Fyh Dhh); apply two_prod_fmt).
  assert (Ch : fst (Fast2Mult prec ne xh yh) = rndX (xh * yh)) by reflexivity.
  assert (Cl : snd (Fast2Mult prec ne xh yh) = rndX (xh * yh - rndX (xh * yh))) by reflexivity.
  destruct (Fast2Mult prec ne xh yh) as [ch cl1]. cbn [fst snd] in Fch, Fcl1, Ch, Cl.
  rewrite (normal_round _ Dhl), (normal_round _ Dlh).
  assert (Ft1 : fmtF (rndX (xh * yl))) by (rewrite <- (normal_round _ Dhl); apply fmtF_rnd).
  assert (Ft2 : fmtF (rndX (xl * yh))) by (rewrite <- (normal_round _ Dlh); apply fmtF_rnd).
  rewrite (sum_round _ _ Ft1 Ft2).
  assert (Fc2 : fmtF (rndX (rndX (xh * yl) + rndX (xl * yh))))
    by (rewrite <- (sum_round _ _ Ft1 Ft2); apply fmtF_rnd).
  rewrite (sum_round _ _ Fcl1 Fc2).
  assert (Fc3 : fmtF (rndX (cl1 + rndX (rndX (xh * yl) + rndX (xl * yh)))))
    by (rewrite <- (sum_round _ _ Fcl1 Fc2); apply fmtF_rnd).
  apply (fast_two_sum_dw _ _ Fch Fc3).
  (* |cl3| <= 6u |xh yh| < (1 - u) |xh yh| <= |ch|. *)
  set (P := Rabs (xh * yh)).
  assert (Hch : (1 - u) * P <= Rabs ch).
  { rewrite Ch. pose proof (Rel (xh * yh)). pose proof (Rabs_triang_inv (xh * yh) (rndX (xh * yh))).
    rewrite Rabs_minus_sym in H. unfold P. lra. }
  assert (Hcl1 : Rabs cl1 <= (1 + u) * (u * P)).
  { rewrite Cl. apply Rle_trans with (1 := Up _). apply Rmult_le_compat_l; [lra | ].
    rewrite Rabs_minus_sym. apply Rel. }
  assert (Hm : forall a b c, Rabs b <= 2 * u * Rabs c -> Rabs (a * b) <= 2 * u * Rabs (a * c)).
  { intros a b c H. rewrite !Rabs_mult.
    replace (2 * u * (Rabs a * Rabs c)) with (Rabs a * (2 * u * Rabs c)) by ring.
    apply Rmult_le_compat_l; [apply Rabs_pos | exact H]. }
  assert (Ht1 : Rabs (rndX (xh * yl)) <= (1 + u) * (2 * u * P)).
  { apply Rle_trans with (1 := Up _). apply Rmult_le_compat_l; [lra | ]. unfold P. apply Hm. exact Ly. }
  assert (Ht2 : Rabs (rndX (xl * yh)) <= (1 + u) * (2 * u * P)).
  { apply Rle_trans with (1 := Up _). apply Rmult_le_compat_l; [lra | ].
    unfold P. rewrite (Rmult_comm xl), (Rmult_comm xh). apply Hm. exact Lx. }
  assert (Hc2 : Rabs (rndX (rndX (xh * yl) + rndX (xl * yh))) <= (1 + u) * (2 * ((1 + u) * (2 * u * P)))).
  { apply Rle_trans with (1 := Up _). apply Rmult_le_compat_l; [lra | ].
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  assert (P0 : 0 <= P) by apply Rabs_pos.
  apply Rle_trans with (1 := Up _).
  apply Rle_trans with ((1 + u) * ((1 + u) * (u * P) + (1 + u) * (2 * ((1 + u) * (2 * u * P))))).
  { apply Rmult_le_compat_l; [lra | ]. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  apply Rle_trans with (2 := Hch). unfold u in *. lra.
Qed.
