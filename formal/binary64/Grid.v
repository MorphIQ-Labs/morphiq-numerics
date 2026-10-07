(** Granularity: [on_grid q x] says [x] is an integer multiple of [2^q]. Sums,
    differences and products stay on a grid, every rounding keeps a value on
    any grid it was on, and a nonzero value on [2^q]'s grid is at least [2^q]
    in magnitude. A floating-point number at least [2^m] in magnitude is on
    [2^(m - 52)]'s grid. Together these bound a nonzero computed remainder from
    below by its operands' magnitudes. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.

Open Scope R_scope.

Definition on_grid (q : Z) (x : R) : Prop :=
  exists k : Z, x = IZR k * bpow radix2 q.

Lemma grid_0 q : on_grid q 0.
Proof. exists 0%Z. simpl. ring. Qed.

Lemma grid_plus q x y : on_grid q x -> on_grid q y -> on_grid q (x + y).
Proof. intros [k ->] [l ->]. exists (k + l)%Z. rewrite plus_IZR. ring. Qed.

Lemma grid_opp q x : on_grid q x -> on_grid q (- x).
Proof. intros [k ->]. exists (- k)%Z. rewrite opp_IZR. ring. Qed.

Lemma grid_minus q x y : on_grid q x -> on_grid q y -> on_grid q (x - y).
Proof. intros Hx Hy. unfold Rminus. apply grid_plus; [exact Hx | now apply grid_opp]. Qed.

Lemma grid_mult q r x y : on_grid q x -> on_grid r y -> on_grid (q + r) (x * y).
Proof. intros [k ->] [l ->]. exists (k * l)%Z. rewrite mult_IZR, bpow_plus. ring. Qed.

(** A grid is also on every finer grid. *)
Lemma grid_le q q' x : (q' <= q)%Z -> on_grid q x -> on_grid q' x.
Proof.
  intros H [k ->]. exists (k * Zpower radix2 (q - q'))%Z.
  rewrite mult_IZR, IZR_Zpower by lia.
  replace q with ((q - q') + q')%Z at 1 by ring. rewrite bpow_plus. ring.
Qed.

Lemma grid_fmt fexp x : generic_format radix2 fexp x -> on_grid (cexp radix2 fexp x) x.
Proof. intros F. exists (Ztrunc (scaled_mantissa radix2 fexp x)). exact F. Qed.

(** Rounding keeps a value on its grid: either the rounding's own exponent is
    at least the grid's, or the value is representable and returned as is. *)
Lemma grid_round fexp {Vexp : Valid_exp fexp} rnd {Vrnd : Valid_rnd rnd} q x :
  on_grid q x -> on_grid q (round radix2 fexp rnd x).
Proof.
  intros G. destruct G as [k Hx].
  destruct (Z_le_gt_dec q (cexp radix2 fexp x)) as [H | H].
  - apply grid_le with (cexp radix2 fexp x); [exact H | ].
    exists (rnd (scaled_mantissa radix2 fexp x)). reflexivity.
  - assert (F : generic_format radix2 fexp x).
    { rewrite Hx. change (IZR k * bpow radix2 q) with (F2R (Float radix2 k q)).
      apply generic_format_F2R. intros _.
      change (F2R (Float radix2 k q)) with (IZR k * bpow radix2 q).
      rewrite <- Hx. lia. }
    rewrite round_generic by assumption. now exists k.
Qed.

Lemma grid_nonzero q x : on_grid q x -> x <> 0 -> bpow radix2 q <= Rabs x.
Proof.
  intros [k ->] Hn.
  assert (Hk : k <> 0%Z) by (intros ->; apply Hn; simpl; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 q)) by apply bpow_ge_0.
  rewrite <- abs_IZR.
  assert (1 <= IZR (Z.abs k)) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 q). nra.
Qed.

(** A floating-point number at least [2^m] in magnitude is on [2^(m - 52)]'s
    grid, for any format whose exponents keep at most 53 significant bits. *)
Lemma grid_fmt_bound fexp m x :
  (forall e, (e - 53 <= fexp e)%Z) -> generic_format radix2 fexp x ->
  x = 0 \/ bpow radix2 m <= Rabs x -> on_grid (m - 52) x.
Proof.
  intros Hf F [-> | Hx]; [apply grid_0 | ].
  apply grid_le with (cexp radix2 fexp x); [ | now apply grid_fmt].
  unfold cexp. specialize (Hf (mag radix2 x)).
  assert (M : (m + 1 <= mag radix2 x)%Z)
    by (apply mag_ge_bpow; replace (m + 1 - 1)%Z with m by ring; exact Hx).
  lia.
Qed.

(** The double-word additions round sums and differences of their inputs, so
    their results stay on any grid the inputs share. *)
From Binary64 Require Import Binary64Add.

Lemma grid_two_sum q a b : on_grid q a -> on_grid q b ->
  on_grid q (fst (two_sum a b)) /\ on_grid q (snd (two_sum a b)).
Proof.
  intros Ga Gb. unfold two_sum; cbv zeta; cbn [fst snd].
  split; repeat first [assumption | apply grid_round | apply grid_plus | apply grid_minus
                       | apply grid_opp | exact _].
Qed.

Lemma grid_fast_two_sum q a b : on_grid q a -> on_grid q b ->
  on_grid q (fst (fast_two_sum a b)) /\ on_grid q (snd (fast_two_sum a b)).
Proof.
  intros Ga Gb. unfold fast_two_sum; cbv zeta; cbn [fst snd].
  split; repeat first [assumption | apply grid_round | apply grid_plus | apply grid_minus
                       | apply grid_opp | exact _].
Qed.

Lemma grid_add_f64 q xh xl y : on_grid q xh -> on_grid q xl -> on_grid q y ->
  on_grid q (fst (add_f64 xh xl y)) /\ on_grid q (snd (add_f64 xh xl y)).
Proof.
  intros Gh Gl Gy. unfold add_f64.
  destruct (grid_two_sum q xh y Gh Gy) as [Gs Gt].
  destruct (two_sum xh y) as [sh sl]. cbn [fst snd] in Gs, Gt.
  apply grid_fast_two_sum; [exact Gs | ].
  repeat first [assumption | apply grid_round | apply grid_plus | exact _].
Qed.

Lemma grid_add q xh xl yh yl : on_grid q xh -> on_grid q xl -> on_grid q yh -> on_grid q yl ->
  on_grid q (fst (add xh xl yh yl)) /\ on_grid q (snd (add xh xl yh yl)).
Proof.
  intros Gxh Gxl Gyh Gyl. unfold add.
  destruct (grid_two_sum q xh yh Gxh Gyh) as [Gsh Gsl].
  destruct (grid_two_sum q xl yl Gxl Gyl) as [Gth Gtl].
  destruct (two_sum xh yh) as [sh sl]. destruct (two_sum xl yl) as [th tl]. cbn [fst snd] in *.
  assert (Gc : on_grid q (rndF (sl + th)))
    by (repeat first [assumption | apply grid_round | apply grid_plus | exact _]).
  destruct (grid_fast_two_sum q sh (rndF (sl + th)) Gsh Gc) as [Gvh Gvl].
  destruct (fast_two_sum sh (rndF (sl + th))) as [vh vl]. cbn [fst snd] in *.
  apply grid_fast_two_sum; [exact Gvh | ].
  repeat first [assumption | apply grid_round | apply grid_plus | exact _].
Qed.
