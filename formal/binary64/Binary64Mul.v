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
From Flocq Require Import Core Mult_error.
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

Theorem mul_f64_bound xh xl y :
  fmtF xh -> fmtF xl -> fmtF y -> xh = rndF (xh + xl) ->
  in_two_prod_domain xh y -> normal_or_zero (xl * y) ->
  let '(zh, zl) := mul_f64 xh xl y in
  let xy := (xh + xl) * y in
  Rabs ((zh + zl - xy) / xy) <= 3 / 2 * bpow radix2 (- prec) ^ 2 + 4 * bpow radix2 (- prec) ^ 3.
Proof.
  intros Fxh Fxl Fy E Dh Dl.
  pose proof (Instances.mul_f64_bound xh xl y (dw_of_binary64 xh xl Fxh Fxl E) (fmtF_fmtX y Fy)) as B.
  unfold mul_f64.
  rewrite (two_prod_eq xh y Fxh Fy Dh).
  rewrite (normal_round _ Dl).
  assert (Fch : fmtF (fst (Fast2Mult prec ne xh y)))
    by (rewrite <- (two_prod_eq xh y Fxh Fy Dh); apply two_prod_fmt).
  assert (Fcl1 : fmtF (snd (Fast2Mult prec ne xh y)))
    by (rewrite <- (two_prod_eq xh y Fxh Fy Dh); apply two_prod_fmt).
  assert (Fcl2 : fmtF (rndX (xl * y))) by (rewrite <- (normal_round _ Dl); apply fmtF_rnd).
  destruct (Fast2Mult prec ne xh y) as [ch cl1] eqn:C. cbn [fst snd] in Fch, Fcl1.
  unfold DWTimesFP in B. rewrite TwoProd_Fast2Mult, C in B. cbn [fst snd] in B.
  rewrite (fast_two_sum_eq _ _ Fch Fcl2).
  destruct (fast_two_sum_fmt _ _ Fch Fcl2) as [Fth Ftl1].
  set (T := F2Sum.Fast2Sum prec ne ch (rndX (xl * y))) in *.
  destruct T as [th tl1]. cbn [fst snd] in Fth, Ftl1.
  rewrite (sum_round _ _ Ftl1 Fcl1).
  assert (Ftl2 : fmtF (rndX (tl1 + cl1))) by (rewrite <- (sum_round _ _ Ftl1 Fcl1); apply fmtF_rnd).
  rewrite (fast_two_sum_eq _ _ Fth Ftl2).
  exact B.
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
