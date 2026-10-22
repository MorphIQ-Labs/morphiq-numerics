(** The odd part of a binary64 value, as atan2's tiny-ratio test extracts it from the
    encoding: [x = m 2^e] with [m] odd. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Zwf.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import Ln1pLemmas AsinTables AsinKernel Atan2Kernel.
Open Scope Z_scope.

Lemma land_lnot x : Z.land x (Z.lnot x) = 0.
Proof.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lnot_spec by lia. rewrite Z.bits_0.
  destruct (Z.testbit x k); reflexivity.
Qed.

(** The lowest set bit of [m] is [2^v] where [m = o 2^v] with [o] odd. *)
Lemma lowbit_spec m : 0 < m -> exists v o, 0 <= v /\ Z.odd o = true /\ 0 < o /\ m = o * 2 ^ v /\ Z.land m (- m) = 2 ^ v.
Proof.
  induction m as [m IH] using (well_founded_induction_type (Zwf_well_founded 0)).
  intros Hm. destruct (Z.Even_or_Odd m) as [[m' Hev] | Hodd].
  - assert (Hm' : 0 < m') by lia.
    destruct (IH m' ltac:(unfold Zwf; lia) Hm') as [v [o [Hv [Ho [Ho0 [Hmo Hl]]]]]].
    exists (v + 1), o. refine (conj _ (conj Ho (conj Ho0 (conj _ _)))); [lia | | ].
    + rewrite Z.pow_add_r by lia. rewrite Hev, Hmo. ring.
    + assert (E : Z.land m (- m) = Z.shiftl (Z.land m' (- m')) 1).
      { rewrite Z.shiftl_land. f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite Hev; ring. }
      rewrite E, Hl, Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. ring.
  - exists 0, m. refine (conj (Z.le_refl 0) (conj _ (conj Hm (conj _ _)))).
    + rewrite Z.odd_spec. exact Hodd.
    + ring.
    + destruct Hodd as [x Hx].
      apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
      destruct (Z.eq_dec k 0) as [-> | Hk0].
      * rewrite Hx. replace (- (2 * x + 1)) with (2 * (- x - 1) + 1) by ring.
        rewrite !Z.testbit_odd_0. reflexivity.
      * assert (Hk1 : 0 <= k - 1) by lia.
        assert (Hks : k = Z.succ (k - 1)) by lia. rewrite Hks.
        replace (2 ^ 0) with (2 * 0 + 1) by reflexivity.
        rewrite Hx. replace (- (2 * x + 1)) with (2 * (- x - 1) + 1) by ring.
        rewrite !Z.testbit_odd_succ by exact Hk1.
        replace (- x - 1) with (Z.lnot x) by (unfold Z.lnot; lia).
        pose proof (land_lnot x) as L.
        assert (Hb : Z.testbit (Z.land x (Z.lnot x)) (k - 1) = false) by (rewrite L; apply Z.bits_0).
        rewrite Z.land_spec in Hb. rewrite Hb, Z.bits_0. reflexivity.
Qed.

