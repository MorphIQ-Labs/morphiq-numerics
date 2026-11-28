(** The slice reductions of [reduce.rs] (docs/reduce.md): their transcription on
    IEEE 754 binary64, the error bounds of Ogita, Rump and Oishi, and the rule
    for NaN results.

    Each bound is stated for a finite result. In IEEE 754 an overflow or a
    non-finite operand never produces a finite result further on, so a finite
    result shows that no operation overflowed: the transforms below recover
    that for every intermediate operation. *)

From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core Relative Plus_error IEEE754.Binary IEEE754.Bits.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul.
Require TwoProdBinary64.
Import ListNotations.

Open Scope R_scope.

(** * Rounding errors *)

Definition u : R := / 9007199254740992.                               (* 2^-53 *)
Definition gamma (k : nat) : R := INR k * u / (1 - INR k * u).

Lemma u_pos : 0 < u.
Proof. unfold u. apply Rinv_0_lt_compat. lra. Qed.

Lemma gamma_den k : INR k * u < 1 -> 0 < 1 - INR k * u.
Proof. lra. Qed.

Lemma ku_pos k : 0 <= INR k * u.
Proof. apply Rmult_le_pos; [apply pos_INR | apply Rlt_le, u_pos]. Qed.

Lemma gamma_pos k : INR k * u < 1 -> 0 <= gamma k.
Proof.
  intros H. unfold gamma, Rdiv. apply Rmult_le_pos; [apply ku_pos | ].
  apply Rlt_le, Rinv_0_lt_compat, gamma_den, H.
Qed.

Lemma gamma_0 : gamma 0 = 0.
Proof. unfold gamma. simpl. unfold Rdiv. ring. Qed.

Lemma ku_mono j k : (j <= k)%nat -> INR j * u <= INR k * u.
Proof. intros H. apply Rmult_le_compat_r; [apply Rlt_le, u_pos | apply le_INR, H]. Qed.

Lemma gamma_mono j k : (j <= k)%nat -> INR k * u < 1 -> gamma j <= gamma k.
Proof.
  intros Hjk Hk. pose proof (ku_mono j k Hjk) as M. pose proof (ku_pos j) as P.
  assert (Dj : 0 < 1 - INR j * u) by lra. assert (Dk : 0 < 1 - INR k * u) by lra.
  unfold gamma. apply Rmult_le_reg_r with (1 - INR j * u); [exact Dj | ].
  apply Rmult_le_reg_r with (1 - INR k * u); [exact Dk | ].
  replace (INR j * u / (1 - INR j * u) * (1 - INR j * u) * (1 - INR k * u))
    with (INR j * u * (1 - INR k * u)) by (field; lra).
  replace (INR k * u / (1 - INR k * u) * (1 - INR j * u) * (1 - INR k * u))
    with (INR k * u * (1 - INR j * u)) by (field; lra).
  nra.
Qed.

(** One more rounding: [γ_k + u·(1 + γ_k) <= γ_(k+1)]. *)
Lemma gamma_step k : INR (S k) * u < 1 -> gamma k + u * (1 + gamma k) <= gamma (S k).
Proof.
  intros H. rewrite S_INR in H. pose proof (ku_pos k) as P. pose proof u_pos as U.
  assert (D1 : 0 < 1 - INR k * u) by lra.
  assert (D2 : 0 < 1 - (INR k * u + u)) by lra.
  unfold gamma. rewrite S_INR. replace ((INR k + 1) * u) with (INR k * u + u) by ring.
  set (x := INR k * u) in *.
  replace (x / (1 - x) + u * (1 + x / (1 - x))) with ((x + u) / (1 - x)) by (field; lra).
  unfold Rdiv. apply Rmult_le_compat_l; [lra | ].
  apply Rinv_le; lra.
Qed.

Lemma plus_error_u a b : fmtF a -> fmtF b -> Rabs (rndF (a + b) - (a + b)) <= u * Rabs (a + b).
Proof.
  intros Fa Fb.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (a + b))) as [H | H].
  - pose proof (relative_error_N_FLT radix2 emin prec ltac:(unfold prec; lia) ne (a + b) H) as E.
    change (bpow radix2 (- prec + 1)) with (/ 4503599627370496) in E. unfold u. lra.
  - assert (F : fmtF (a + b)).
    { apply FLT_format_plus_small; auto with typeclass_instances.
      apply Rlt_le, Rlt_le_trans with (1 := H). apply bpow_le; unfold emin, prec; lia. }
    rewrite round_generic by auto with typeclass_instances.
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0.
    apply Rmult_le_pos; [apply Rlt_le, u_pos | apply Rabs_pos].
Qed.

(** Rounding to nearest is no further from the sum than either operand is. *)
Lemma plus_error_term a b : fmtF a -> Rabs (rndF (a + b) - (a + b)) <= Rabs b.
Proof.
  intros Fa.
  destruct (round_N_pt radix2 (FLT_exp emin prec) ne (a + b)) as [_ N].
  specialize (N a Fa). replace (a - (a + b)) with (- b) in N by ring.
  now rewrite Rabs_Ropp in N.
Qed.

Lemma plus_residual_fmt a b : fmtF a -> fmtF b -> fmtF (a + b - rndF (a + b)).
Proof.
  intros Fa Fb. replace (a + b - rndF (a + b)) with (- (rndF (a + b) - (a + b))) by ring.
  apply generic_format_opp. apply plus_error; auto with typeclass_instances.
Qed.

(** * Sums over the reals *)

Fixpoint total (l : list R) : R := match l with [] => 0 | a :: r => a + total r end.
Fixpoint atotal (l : list R) : R := match l with [] => 0 | a :: r => Rabs a + atotal r end.

Lemma atotal_pos l : 0 <= atotal l.
Proof. induction l as [ | a l IH]; simpl; [lra | pose proof (Rabs_pos a); lra]. Qed.

(** Recursive summation from [p], and the rounding error of each addition. *)
Definition rsum (p : R) (l : list R) : R := fold_left (fun acc a => rndF (acc + a)) l p.
Fixpoint errors (p : R) (l : list R) : list R :=
  match l with
  | [] => []
  | a :: r => (p + a - rndF (p + a)) :: errors (rndF (p + a)) r
  end.

Lemma errors_length l : forall p, length (errors p l) = length l.
Proof. induction l as [ | a l IH]; intros p; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma rsum_fmt l : forall p, fmtF p -> fmtF (rsum p l).
Proof.
  unfold rsum. induction l as [ | a l IH]; intros p Fp; simpl; [exact Fp | ].
  apply IH, generic_format_round; auto with typeclass_instances.
Qed.

Lemma errors_fmt l : forall p, fmtF p -> Forall fmtF l -> Forall fmtF (errors p l).
Proof.
  induction l as [ | a l IH]; intros p Fp Fl; simpl; [constructor | ].
  inversion Fl as [ | x y Fa Fr]; subst. constructor; [now apply plus_residual_fmt | ].
  apply IH; [apply generic_format_round; auto with typeclass_instances | exact Fr].
Qed.

(** The errors are exactly what the recursive sum loses. *)
Lemma errors_total l : forall p, rsum p l + total (errors p l) = p + total l.
Proof.
  unfold rsum. induction l as [ | a l IH]; intros p; simpl; [ring | ].
  specialize (IH (rndF (p + a))). lra.
Qed.

(** One step of the running bound. *)
Lemma sum_step k p a s S :
  fmtF p -> fmtF a -> Rabs (p - s) <= gamma k * S -> Rabs s <= S -> 0 <= S ->
  INR (Datatypes.S k) * u < 1 ->
  Rabs (rndF (p + a) - (s + a)) <= gamma (Datatypes.S k) * (S + Rabs a) /\
  Rabs (p + a - rndF (p + a)) <= u * ((1 + gamma k) * (S + Rabs a)).
Proof.
  intros Fp Fa E Hs HS Hk.
  assert (Hk' : INR k * u < 1).
  { apply Rle_lt_trans with (2 := Hk). apply ku_mono. lia. }
  pose proof (gamma_pos k Hk') as G. pose proof (Rabs_pos a) as Pa. pose proof u_pos as U.
  assert (T : Rabs (p + a) <= (1 + gamma k) * (S + Rabs a)).
  { replace (p + a) with ((p - s) + (s + a)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    pose proof (Rabs_triang s a). nra. }
  assert (R : Rabs (p + a - rndF (p + a)) <= u * ((1 + gamma k) * (S + Rabs a))).
  { rewrite Rabs_minus_sym. apply Rle_trans with (1 := plus_error_u p a Fp Fa).
    apply Rmult_le_compat_l; [lra | exact T]. }
  split; [ | exact R].
  replace (rndF (p + a) - (s + a)) with (- (p + a - rndF (p + a)) + (p - s)) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
  apply Rle_trans with (u * ((1 + gamma k) * (S + Rabs a)) + gamma k * (S + Rabs a)).
  { apply Rplus_le_compat; [exact R | ]. apply Rle_trans with (1 := E).
    apply Rmult_le_compat_l; lra. }
  replace (u * ((1 + gamma k) * (S + Rabs a)) + gamma k * (S + Rabs a))
    with ((gamma k + u * (1 + gamma k)) * (S + Rabs a)) by ring.
  apply Rmult_le_compat_r; [lra | apply gamma_step, Hk].
Qed.

(** The recursive sum, and the total magnitude of its errors. *)
Lemma rsum_bounds l : forall k p s S A,
  fmtF p -> Forall fmtF l -> Rabs (p - s) <= gamma k * S -> Rabs s <= S -> 0 <= S ->
  A <= gamma k * S -> INR (k + length l) * u < 1 ->
  Rabs (rsum p l - (s + total l)) <= gamma (k + length l) * (S + atotal l) /\
  A + atotal (errors p l) <= gamma (k + length l) * (S + atotal l).
Proof.
  unfold rsum. induction l as [ | a l IH]; intros k p s S A Fp Fl E Hs HS HA Hk; simpl in *.
  - rewrite Nat.add_0_r, !Rplus_0_r. split; assumption.
  - inversion Fl as [ | x y Fa Fr]; subst.
    assert (Hk1 : INR (Datatypes.S k) * u < 1).
    { apply Rle_lt_trans with (2 := Hk). apply ku_mono. lia. }
    destruct (sum_step k p a s S Fp Fa E Hs HS Hk1) as [E' R].
    pose proof (Rabs_pos a) as Pa.
    assert (Hs' : Rabs (s + a) <= S + Rabs a).
    { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
    assert (Hk0 : INR k * u < 1).
    { apply Rle_lt_trans with (2 := Hk1). apply ku_mono. lia. }
    assert (A' : A + Rabs (p + a - rndF (p + a)) <= gamma (Datatypes.S k) * (S + Rabs a)).
    { pose proof (gamma_pos k Hk0) as G.
      apply Rle_trans with (gamma k * (S + Rabs a) + u * ((1 + gamma k) * (S + Rabs a))).
      - apply Rplus_le_compat; [ | exact R]. apply Rle_trans with (1 := HA).
        apply Rmult_le_compat_l; lra.
      - replace (gamma k * (S + Rabs a) + u * ((1 + gamma k) * (S + Rabs a)))
          with ((gamma k + u * (1 + gamma k)) * (S + Rabs a)) by ring.
        apply Rmult_le_compat_r; [lra | apply gamma_step, Hk1]. }
    replace (k + Datatypes.S (length l))%nat with (Datatypes.S k + length l)%nat in * by lia.
    destruct (IH (Datatypes.S k) (rndF (p + a)) (s + a) (S + Rabs a)
                (A + Rabs (p + a - rndF (p + a)))
                (generic_format_round _ _ _ _) Fr E' Hs' ltac:(lra) A' Hk) as [R1 R2].
    split.
    + replace (s + (a + total l)) with (s + a + total l) by ring.
      replace (S + (Rabs a + atotal l)) with (S + Rabs a + atotal l) by ring. exact R1.
    + replace (S + (Rabs a + atotal l)) with (S + Rabs a + atotal l) by ring.
      rewrite <- Rplus_assoc. exact R2.
Qed.

(** From a first term, which is exact. *)
Lemma rsum_first p l : fmtF p -> Forall fmtF l -> INR (length l) * u < 1 ->
  Rabs (rsum p l - (p + total l)) <= gamma (length l) * (Rabs p + atotal l) /\
  atotal (errors p l) <= gamma (length l) * (Rabs p + atotal l).
Proof.
  intros Fp Fl H.
  destruct (rsum_bounds l 0 p p (Rabs p) 0 Fp Fl) as [R1 R2]; simpl; try assumption.
  - rewrite gamma_0, Rmult_0_l. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra.
  - lra.
  - apply Rabs_pos.
  - rewrite gamma_0. lra.
  - rewrite Rplus_0_l in R2. split; assumption.
Qed.

(** * The real-arithmetic bounds *)

(** Recursive summation, (2.4) of the paper. *)
Theorem sum_real p l : fmtF p -> Forall fmtF l -> INR (length l) * u < 1 ->
  Rabs (rsum p l - total (p :: l)) <= gamma (length l) * atotal (p :: l).
Proof. intros Fp Fl H. exact (proj1 (rsum_first p l Fp Fl H)). Qed.

(** [res = fl(π + σ)] where [σ] approximates what [π] misses. *)
Lemma compensated pi sigma exact e :
  fmtF pi -> fmtF sigma -> Rabs (pi + sigma - exact) <= e ->
  Rabs (rndF (pi + sigma) - exact) <= u * Rabs exact + (1 + u) * e.
Proof.
  intros Fp Fs E. pose proof u_pos as U.
  assert (T : Rabs (pi + sigma) <= Rabs exact + e).
  { replace (pi + sigma) with (exact + (pi + sigma - exact)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  replace (rndF (pi + sigma) - exact)
    with ((rndF (pi + sigma) - (pi + sigma)) + (pi + sigma - exact)) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rle_trans with (u * (Rabs exact + e) + e).
  - apply Rplus_le_compat; [ | exact E].
    apply Rle_trans with (1 := plus_error_u pi sigma Fp Fs).
    apply Rmult_le_compat_l; lra.
  - right. ring.
Qed.

(** Sum2, Proposition 4.5. *)
Theorem sum2_real p l : fmtF p -> Forall fmtF l -> INR (S (length l)) * u < 1 ->
  Rabs (rndF (rsum p l + rsum 0 (errors p l)) - total (p :: l))
  <= u * Rabs (total (p :: l)) + gamma (length l) * gamma (length l) * atotal (p :: l).
Proof.
  intros Fp Fl Hn.
  assert (Hm : INR (length l) * u < 1).
  { apply Rle_lt_trans with (2 := Hn). apply ku_mono. lia. }
  pose proof (gamma_pos _ Hm) as G. pose proof u_pos as U.
  assert (S0 : 0 <= atotal (p :: l)) by apply atotal_pos.
  destruct (rsum_first p l Fp Fl Hm) as [_ A]. change (Rabs p + atotal l) with (atotal (p :: l)) in A.
  pose proof (errors_total l p) as T. change (p + total l) with (total (p :: l)) in T.
  pose proof (errors_fmt l p Fp Fl) as Fq.
  pose proof (errors_length l p) as Len.
  set (q := errors p l) in *.
  assert (E : Rabs (rsum 0 q - total q) * (1 + u)
              <= gamma (length l) * gamma (length l) * atotal (p :: l)).
  { destruct q as [ | q0 qr].
    - unfold rsum. simpl. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0, Rmult_0_l.
      apply Rmult_le_pos; [apply Rmult_le_pos | ]; assumption.
    - inversion Fq as [ | x y F0 Fr]; subst. simpl in Len.
      assert (Z : rsum 0 (q0 :: qr) = rsum q0 qr).
      { unfold rsum. simpl. rewrite Rplus_0_l, round_generic by auto with typeclass_instances.
        reflexivity. }
      rewrite Z. assert (Hr : INR (length qr) * u < 1).
      { apply Rle_lt_trans with (2 := Hm). apply ku_mono. lia. }
      destruct (rsum_first q0 qr F0 Fr Hr) as [B1 _].
      change (q0 + total qr) with (total (q0 :: qr)) in B1.
      change (Rabs q0 + atotal qr) with (atotal (q0 :: qr)) in B1.
      pose proof (gamma_pos _ Hr) as Gr.
      assert (Step : gamma (length qr) * (1 + u) <= gamma (length l)).
      { assert (E1 : S (length qr) = length l) by exact Len.
        pose proof (gamma_step (length qr) ltac:(rewrite E1; exact Hm)) as St.
        rewrite E1 in St. nra. }
      assert (Aq : 0 <= atotal (q0 :: qr)) by apply atotal_pos.
      apply Rle_trans with (gamma (length qr) * atotal (q0 :: qr) * (1 + u)).
      { apply Rmult_le_compat_r; [lra | exact B1]. }
      replace (gamma (length qr) * atotal (q0 :: qr) * (1 + u))
        with (gamma (length qr) * (1 + u) * atotal (q0 :: qr)) by ring.
      apply Rle_trans with (gamma (length l) * atotal (q0 :: qr)).
      { apply Rmult_le_compat_r; assumption. }
      replace (gamma (length l) * gamma (length l) * atotal (p :: l))
        with (gamma (length l) * (gamma (length l) * atotal (p :: l))) by ring.
      apply Rmult_le_compat_l; assumption. }
  assert (Fs : fmtF (rsum 0 q)) by (apply rsum_fmt, generic_format_0).
  assert (D : Rabs (rsum p l + rsum 0 q - total (p :: l)) <= Rabs (rsum 0 q - total q)).
  { right. f_equal. lra. }
  apply Rle_trans with (1 := compensated _ _ _ _ (rsum_fmt l p Fp) Fs D).
  apply Rplus_le_compat_l. rewrite Rmult_comm. exact E.
Qed.

(** ** Products *)

Definition product (xy : R * R) : R := fst xy * snd xy.
Definition rounded (xy : R * R) : R := rndF (product xy).
Definition residual (xy : R * R) : R := product xy - rounded xy.
Definition dot_exact (l : list (R * R)) : R := total (map product l).
Definition dot_abs (l : list (R * R)) : R := atotal (map product l).

Lemma product_error xy : normal_or_zero (product xy) ->
  Rabs (rounded xy - product xy) <= u * Rabs (product xy).
Proof.
  unfold rounded. intros [Z | N].
  - rewrite Z, round_0 by auto with typeclass_instances.
    unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra.
  - pose proof (relative_error_N_FLT radix2 emin prec ltac:(unfold prec; lia) ne _ N) as E.
    change (bpow radix2 (- prec + 1)) with (/ 4503599627370496) in E. unfold u. lra.
Qed.

Lemma products_bounds l : Forall (fun xy => normal_or_zero (product xy)) l ->
  Rabs (total (map rounded l) - dot_exact l) <= u * dot_abs l /\
  atotal (map rounded l) <= (1 + u) * dot_abs l /\
  atotal (map residual l) <= u * dot_abs l.
Proof.
  unfold dot_exact, dot_abs. induction 1 as [ | a l Ha Hl [IH1 [IH2 IH3]]]; simpl.
  - unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra.
  - pose proof (product_error a Ha) as E.
    split; [ | split].
    + replace (rounded a + total (map rounded l) - (product a + total (map product l)))
        with ((rounded a - product a) + (total (map rounded l) - total (map product l))) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). lra.
    + assert (Rabs (rounded a) <= (1 + u) * Rabs (product a)); [ | lra].
      replace (rounded a) with (product a + (rounded a - product a)) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). lra.
    + unfold residual at 1. rewrite Rabs_minus_sym. lra.
Qed.

Lemma rounded_fmt l : Forall fmtF (map rounded l).
Proof.
  apply Forall_forall. intros x H. apply in_map_iff in H as [a [<- _]].
  apply generic_format_round; auto with typeclass_instances.
Qed.

(** The ordinary dot product: [γ_n], from the paper's (2.2) and (2.4). *)
Theorem dot_real a l : Forall (fun xy => normal_or_zero (product xy)) (a :: l) ->
  INR (S (length l)) * u < 1 ->
  Rabs (rsum (rounded a) (map rounded l) - dot_exact (a :: l))
  <= gamma (S (length l)) * dot_abs (a :: l).
Proof.
  intros H Hn.
  assert (Hm : INR (length l) * u < 1).
  { apply Rle_lt_trans with (2 := Hn). apply ku_mono. lia. }
  pose proof (gamma_pos _ Hm) as G. pose proof u_pos as U.
  destruct (products_bounds _ H) as [B1 [B2 _]].
  assert (Fa : fmtF (rounded a)) by (apply generic_format_round; auto with typeclass_instances).
  destruct (rsum_first (rounded a) (map rounded l) Fa (rounded_fmt l)) as [R _];
    [rewrite map_length; exact Hm | ].
  rewrite map_length in R.
  change (rounded a + total (map rounded l)) with (total (map rounded (a :: l))) in R.
  change (Rabs (rounded a) + atotal (map rounded l)) with (atotal (map rounded (a :: l))) in R.
  assert (S0 : 0 <= dot_abs (a :: l)) by apply atotal_pos.
  replace (rsum (rounded a) (map rounded l) - dot_exact (a :: l))
    with ((rsum (rounded a) (map rounded l) - total (map rounded (a :: l)))
          + (total (map rounded (a :: l)) - dot_exact (a :: l))) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rle_trans with ((gamma (length l) * (1 + u) + u) * dot_abs (a :: l)).
  - replace ((gamma (length l) * (1 + u) + u) * dot_abs (a :: l))
      with (gamma (length l) * ((1 + u) * dot_abs (a :: l)) + u * dot_abs (a :: l)) by ring.
    apply Rplus_le_compat; [ | exact B1].
    apply Rle_trans with (1 := R). apply Rmult_le_compat_l; assumption.
  - apply Rmult_le_compat_r; [exact S0 | ].
    pose proof (gamma_step _ Hn). lra.
Qed.

(** Dot2's error terms, [fl(q + r)] for each later pair. *)
Fixpoint corrections (q r : list R) : list R :=
  match q, r with a :: q', b :: r' => rndF (a + b) :: corrections q' r' | _, _ => [] end.

Lemma corrections_bounds q : forall r, Forall fmtF q -> Forall fmtF r -> length q = length r ->
  length (corrections q r) = length q /\ Forall fmtF (corrections q r) /\
  Rabs (total (corrections q r) - (total q + total r)) <= u * (atotal q + atotal r) /\
  atotal (corrections q r) <= (1 + u) * (atotal q + atotal r).
Proof.
  pose proof u_pos as U.
  induction q as [ | a q IH]; intros [ | b r] Fq Fr Len; try discriminate; simpl.
  - repeat split; [constructor | | lra].
    replace (0 - (0 + 0)) with 0 by ring. rewrite Rabs_R0. lra.
  - inversion Fq as [ | x1 y1 Fa Fq']; subst. inversion Fr as [ | x2 y2 Fb Fr']; subst.
    simpl in Len. injection Len as Len.
    destruct (IH r Fq' Fr' Len) as [L [F [E A]]].
    pose proof (plus_error_u a b Fa Fb) as Er. pose proof (Rabs_triang a b) as T.
    assert (Er' : Rabs (rndF (a + b) - (a + b)) <= u * (Rabs a + Rabs b)).
    { apply Rle_trans with (1 := Er). apply Rmult_le_compat_l; lra. }
    repeat split.
    + now rewrite L.
    + constructor; [apply generic_format_round; auto with typeclass_instances | exact F].
    + replace (rndF (a + b) + total (corrections q r) - (a + total q + (b + total r)))
        with ((rndF (a + b) - (a + b)) + (total (corrections q r) - (total q + total r))) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). lra.
    + assert (Rabs (rndF (a + b)) <= (1 + u) * (Rabs a + Rabs b)); [ | lra].
      replace (rndF (a + b)) with ((a + b) + (rndF (a + b) - (a + b))) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). lra.
Qed.

(** The identity that makes the constant come out as [γ_n²]. *)
Lemma dot2_factor m : INR (S m) * u < 1 ->
  let F := gamma m * (1 + u) + u in
  0 <= F /\ (1 + u) * (F * F) <= gamma (S m) * gamma (S m).
Proof.
  intros Hn F. rewrite S_INR in Hn. pose proof (ku_pos m) as P. pose proof u_pos as U.
  assert (Dm : 0 < 1 - INR m * u) by lra.
  set (w := 1 - (INR m * u + u)).
  assert (Dn : 0 < w) by (unfold w; lra).
  assert (W1 : w <= 1) by (unfold w; lra).
  assert (EF : F = (INR m * u + u) / (1 - INR m * u)) by (unfold F, gamma; field; lra).
  assert (EG : gamma (S m) = (INR m * u + u) / w).
  { unfold gamma, w. rewrite S_INR. f_equal; ring. }
  assert (EW : 1 - INR m * u = w + u) by (unfold w; ring).
  assert (N : 0 <= INR m * u + u) by lra.
  split.
  - rewrite EF. unfold Rdiv. apply Rmult_le_pos; [exact N | ]. apply Rlt_le, Rinv_0_lt_compat, Dm.
  - rewrite EF, EG, EW. set (x := INR m * u + u) in *.
    assert (D2 : 0 < w + u) by lra.
    assert (K : (1 + u) * (w * w) <= (w + u) * (w + u)).
    { assert (P1 : 0 <= u * (w * (2 - w))).
      { apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]. }
      assert (P2 : 0 <= u * u) by (apply Rmult_le_pos; lra).
      replace ((w + u) * (w + u)) with ((1 + u) * (w * w) + (u * (w * (2 - w)) + u * u)) by ring.
      lra. }
    replace ((1 + u) * (x / (w + u) * (x / (w + u))))
      with (x * x * ((1 + u) / ((w + u) * (w + u)))) by (field; lra).
    replace (x / w * (x / w)) with (x * x * (1 / (w * w))) by (field; lra).
    apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | ].
    apply Rmult_le_reg_r with ((w + u) * (w + u)); [apply Rmult_lt_0_compat; lra | ].
    apply Rmult_le_reg_r with (w * w); [apply Rmult_lt_0_compat; lra | ].
    replace ((1 + u) / ((w + u) * (w + u)) * ((w + u) * (w + u)) * (w * w))
      with ((1 + u) * (w * w)) by (field; lra).
    replace (1 / (w * w) * ((w + u) * (w + u)) * (w * w))
      with ((w + u) * (w + u)) by (field; lra).
    exact K.
Qed.

(** Dot2, Proposition 5.5, with every product's error exact. *)
Theorem dot2_real a l : Forall (fun xy => normal_or_zero (product xy)) (a :: l) ->
  Forall (fun xy => fmtF (residual xy)) (a :: l) ->
  INR (S (length l)) * u < 1 ->
  let h := rounded a in
  let hs := map rounded l in
  Rabs (rndF (rsum h hs + rsum (residual a) (corrections (errors h hs) (map residual l)))
        - dot_exact (a :: l))
  <= u * Rabs (dot_exact (a :: l))
     + gamma (S (length l)) * gamma (S (length l)) * dot_abs (a :: l).
Proof.
  intros H Hr Hn h hs.
  set (m := length l) in *.
  assert (Hm : INR m * u < 1).
  { apply Rle_lt_trans with (2 := Hn). apply ku_mono. lia. }
  pose proof (gamma_pos _ Hm) as G. pose proof u_pos as U.
  destruct (products_bounds _ H) as [_ [B2 B3]].
  assert (Fh : fmtF h) by (apply generic_format_round; auto with typeclass_instances).
  assert (Fhs : Forall fmtF hs) by apply rounded_fmt.
  assert (Lhs : length hs = m) by apply map_length.
  inversion Hr as [ | x y Fr0 Frl]; subst x y.
  assert (Frs : Forall fmtF (map residual l)).
  { apply Forall_forall. intros v V. apply in_map_iff in V as [e [<- I]].
    rewrite Forall_forall in Frl. exact (Frl e I). }
  destruct (rsum_first h hs Fh Fhs ltac:(rewrite Lhs; exact Hm)) as [_ Aq]. rewrite Lhs in Aq.
  change (Rabs h + atotal hs) with (atotal (map rounded (a :: l))) in Aq.
  pose proof (errors_total hs h) as Tq.
  pose proof (errors_fmt hs h Fh Fhs) as Fq.
  set (q := errors h hs) in *.
  assert (Lq : length q = length (map residual l)).
  { unfold q. rewrite errors_length, Lhs, map_length. reflexivity. }
  destruct (corrections_bounds q (map residual l) Fq Frs Lq) as [Lc [Fc [Ec Ac]]].
  set (c := corrections q (map residual l)) in *.
  assert (Lc' : length c = m).
  { rewrite Lc, Lq, map_length. reflexivity. }
  destruct (rsum_first (residual a) c Fr0 Fc ltac:(rewrite Lc'; exact Hm)) as [Es _].
  rewrite Lc' in Es.
  set (s := rsum (residual a) c) in *.
  set (W := residual a + total q + total (map residual l)).
  set (T := Rabs (residual a) + atotal q + atotal (map residual l)).
  set (S := dot_abs (a :: l)).
  assert (S0 : 0 <= S) by apply atotal_pos.
  destruct (dot2_factor m Hn) as [F0 Fsq]. set (F := gamma m * (1 + u) + u) in *.
  (* the corrections' sum approximates W *)
  assert (Aq0 : 0 <= atotal q) by apply atotal_pos.
  assert (Ar0 : 0 <= atotal (map residual l)) by apply atotal_pos.
  assert (E1 : Rabs (s - W) <= F * T).
  { replace (s - W) with ((s - (residual a + total c))
                          + (total c - (total q + total (map residual l)))) by (unfold W; ring).
    apply Rle_trans with (1 := Rabs_triang _ _).
    assert (P : gamma m * (Rabs (residual a) + atotal c)
                <= gamma m * (Rabs (residual a) + (1 + u) * (atotal q + atotal (map residual l)))).
    { apply Rmult_le_compat_l; lra. }
    pose proof (Rabs_pos (residual a)) as Pr.
    apply Rle_trans with (gamma m * (Rabs (residual a) + (1 + u) * (atotal q + atotal (map residual l)))
                          + u * (atotal q + atotal (map residual l))).
    - apply Rplus_le_compat; [apply Rle_trans with (1 := Es); exact P | exact Ec].
    - unfold F, T.
      assert (0 <= (gamma m * u + u) * Rabs (residual a))
        by (apply Rmult_le_pos; [pose proof (Rmult_le_pos _ _ G (Rlt_le _ _ U)); lra | exact Pr]).
      lra. }
  (* and those magnitudes are at most F times the exact ones *)
  assert (TS : T <= F * S).
  { unfold T. change (atotal (map residual (a :: l)))
      with (Rabs (residual a) + atotal (map residual l)) in B3.
    assert (Aqb : atotal q <= gamma m * ((1 + u) * S)).
    { apply Rle_trans with (1 := Aq). apply Rmult_le_compat_l; [exact G | exact B2]. }
    unfold F, S in *. lra. }
  assert (E2 : Rabs (s - W) <= F * F * S).
  { apply Rle_trans with (1 := E1). rewrite Rmult_assoc. apply Rmult_le_compat_l; assumption. }
  (* the exact value is the leading sum plus W *)
  assert (Dec : rsum h hs + W = dot_exact (a :: l)).
  { unfold W, dot_exact. simpl.
    assert (Sum : total hs + total (map residual l) = total (map product l)).
    { unfold hs. clear. induction l as [ | e l IH]; simpl; [ring | ].
      unfold residual at 1. lra. }
    unfold residual at 1. fold h. lra. }
  assert (Fs : fmtF s) by (apply rsum_fmt, Fr0).
  assert (D : Rabs (rsum h hs + s - dot_exact (a :: l)) <= Rabs (s - W)).
  { right. f_equal. lra. }
  apply Rle_trans with (1 := compensated _ _ _ _ (rsum_fmt hs h Fh) Fs D).
  apply Rplus_le_compat_l. fold S.
  apply Rle_trans with ((1 + u) * (F * F * S)).
  - apply Rmult_le_compat_l; lra.
  - rewrite <- Rmult_assoc. apply Rmult_le_compat_r; assumption.
Qed.

(** * Finite results show that nothing overflowed *)

Lemma fadd_inv x y : finite (fadd x y) ->
  finite x /\ finite y /\ B (fadd x y) = rndF (B x + B y).
Proof.
  intros F.
  assert (Fin : finite x /\ finite y).
  { destruct x as [sx | sx | sx px Hx | sx mx ex Hx]; destruct y as [sy | sy | sy py Hy | sy my ey Hy];
      try (split; reflexivity); exfalso; revert F; unfold fadd, b64_plus; simpl;
      try discriminate; destruct (Bool.eqb sx sy); discriminate. }
  destruct Fin as [Fx Fy]. split; [exact Fx | split; [exact Fy | ]].
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y Fx Fy) as C.
  destruct (Rlt_bool _ _).
  - exact (proj1 C).
  - destruct C as [C _]. exfalso. unfold fadd, b64_plus in F.
    rewrite <- is_finite_FF_B2FF, C in F. discriminate.
Qed.

Lemma fsub_inv x y : finite (fsub x y) ->
  finite x /\ finite y /\ B (fsub x y) = rndF (B x - B y).
Proof.
  intros F.
  assert (Fin : finite x /\ finite y).
  { destruct x as [sx | sx | sx px Hx | sx mx ex Hx]; destruct y as [sy | sy | sy py Hy | sy my ey Hy];
      try (split; reflexivity); exfalso; revert F; unfold fsub, b64_minus; simpl;
      try discriminate; destruct (Bool.eqb sx (negb sy)); discriminate. }
  destruct Fin as [Fx Fy]. split; [exact Fx | split; [exact Fy | ]].
  pose proof (Bminus_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y Fx Fy) as C.
  destruct (Rlt_bool _ _).
  - exact (proj1 C).
  - destruct C as [C _]. exfalso. unfold fsub, b64_minus in F.
    rewrite <- is_finite_FF_B2FF, C in F. discriminate.
Qed.

Lemma fmul_inv x y : finite (fmul x y) ->
  finite x /\ finite y /\ B (fmul x y) = rndF (B x * B y).
Proof.
  intros F.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_nan_pl64 mode_NE x y) as C.
  destruct (Rlt_bool _ _).
  - destruct C as [C1 [C2 _]]. unfold fmul, b64_mult in F. rewrite C2 in F.
    apply andb_true_iff in F as [Fx Fy]. split; [exact Fx | split; [exact Fy | exact C1]].
  - exfalso. unfold fmul, b64_mult in F. rewrite <- is_finite_FF_B2FF, C in F. discriminate.
Qed.

Lemma two_sum_inv a b : finite (snd (two_sum64 a b)) ->
  finite a /\ finite b /\ finite (fst (two_sum64 a b)) /\
  B (fst (two_sum64 a b)) = rndF (B a + B b) /\
  B (fst (two_sum64 a b)) + B (snd (two_sum64 a b)) = B a + B b.
Proof.
  unfold two_sum64. cbn [fst snd]. intros F.
  destruct (fadd_inv _ _ F) as [Fda [Fdb Er]].
  destruct (fsub_inv _ _ Fda) as [Fa [Fa' Eda]].
  destruct (fsub_inv _ _ Fdb) as [Fb [Fb' Edb]].
  destruct (fsub_inv _ _ Fa') as [Fs [_ Ea']].
  destruct (fsub_inv _ _ Fb') as [_ [_ Eb']].
  destruct (fadd_inv _ _ Fs) as [_ [_ Es]].
  split; [exact Fa | split; [exact Fb | split; [exact Fs | split; [exact Es | ]]]].
  assert (M : two_sum (B a) (B b)
              = (B (fadd a b), B (fadd (fsub a (fsub (fadd a b) b))
                                       (fsub b (fsub (fadd a b) (fsub (fadd a b) b)))))).
  { unfold two_sum. rewrite Er, Eda, Edb, Eb', Ea', Es. reflexivity. }
  rewrite (two_sum_eq _ _ (B_fmt a) (B_fmt b)) in M. injection M as M1 M2.
  rewrite <- M1, <- M2.
  rewrite (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl (B a) (B b)
             (fmtF_fmtX _ (B_fmt a)) (fmtF_fmtX _ (B_fmt b))). ring.
Qed.

Lemma two_prod_inv a b : finite (snd (two_prod64 a b)) ->
  finite (fst (two_prod64 a b)) /\ B (fst (two_prod64 a b)) = rndF (B a * B b) /\
  finite a /\ finite b /\
  (in_two_prod_domain (B a) (B b) ->
   B (fst (two_prod64 a b)) + B (snd (two_prod64 a b)) = B a * B b).
Proof.
  unfold two_prod64, split64. cbn [fst snd]. intros F.
  destruct (splitter_ok) as [_ Ec].
  destruct (fadd_inv _ _ F) as [F3 [F4 E4]].
  destruct (fadd_inv _ _ F3) as [F2 [F5 E3]].
  destruct (fadd_inv _ _ F2) as [F1 [F6 E2]].
  destruct (fsub_inv _ _ F1) as [F7 [Fp E1]].
  destruct (fmul_inv _ _ Fp) as [Fa [Fb Ep]].
  destruct (fmul_inv _ _ F7) as [Fah [Fbh E7]].
  destruct (fmul_inv _ _ F6) as [_ [Fbl E6]].
  destruct (fmul_inv _ _ F5) as [Fal [_ E5]].
  destruct (fmul_inv _ _ F4) as [_ [_ E4']].
  destruct (fsub_inv _ _ Fal) as [_ [_ Eal]].
  destruct (fsub_inv _ _ Fbl) as [_ [_ Ebl]].
  destruct (fadd_inv _ _ Fah) as [Fqa [Fpa Eah]].
  destruct (fadd_inv _ _ Fbh) as [Fqb [Fpb Ebh]].
  destruct (fsub_inv _ _ Fqa) as [_ [_ Eqa]].
  destruct (fsub_inv _ _ Fqb) as [_ [_ Eqb]].
  destruct (fmul_inv _ _ Fpa) as [_ [_ Epa]].
  destruct (fmul_inv _ _ Fpb) as [_ [_ Epb]].
  split; [exact Fp | split; [exact Ep | split; [exact Fa | split; [exact Fb | ]]]].
  intros D.
  assert (Hah : forall x, B (fadd (fsub x (fmul x splitter)) (fmul x splitter))
                = rndF (rndF (B x - rndF (B x * (bpow radix2 27 + 1))) + rndF (B x * (bpow radix2 27 + 1)))
                -> B (fadd (fsub x (fmul x splitter)) (fmul x splitter)) = TwoProdBinary64.split_head (B x)).
  { intros x H. exact H. }
  assert (Ha : B (fadd (fsub a (fmul a splitter)) (fmul a splitter)) = TwoProdBinary64.split_head (B a)).
  { apply Hah. rewrite Eah, Eqa, Epa, Ec. reflexivity. }
  assert (Hb : B (fadd (fsub b (fmul b splitter)) (fmul b splitter)) = TwoProdBinary64.split_head (B b)).
  { apply Hah. rewrite Ebh, Eqb, Epb, Ec. reflexivity. }
  pose proof (TwoProdBinary64.two_prod_exact (B a) (B b) (B_fmt a) (B_fmt b) D) as X.
  assert (E : B (fadd (fadd (fadd (fsub (fmul (fadd (fsub a (fmul a splitter)) (fmul a splitter))
                                              (fadd (fsub b (fmul b splitter)) (fmul b splitter)))
                                        (fmul a b))
                                  (fmul (fadd (fsub a (fmul a splitter)) (fmul a splitter))
                                        (fsub b (fadd (fsub b (fmul b splitter)) (fmul b splitter)))))
                            (fmul (fsub a (fadd (fsub a (fmul a splitter)) (fmul a splitter)))
                                  (fadd (fsub b (fmul b splitter)) (fmul b splitter))))
                      (fmul (fsub a (fadd (fsub a (fmul a splitter)) (fmul a splitter)))
                            (fsub b (fadd (fsub b (fmul b splitter)) (fmul b splitter)))))
              = TwoProdBinary64.two_prod_e (B a) (B b)).
  { rewrite E4, E3, E2, E1, E4', E5, E6, E7, Eal, Ebl, Ep, Ha, Hb.
    unfold TwoProdBinary64.two_prod_e, TwoProdBinary64.two_prod_p, TwoProdBinary64.split_tail.
    cbv zeta. unfold Rminus. rewrite (Rplus_comm (- _)). reflexivity. }
  rewrite E, Ep. symmetry. exact X.
Qed.

(** * The transcription *)

Definition zero : f64 := b64_of_bits 0.
Definition canonical_nan : f64 := b64_of_bits 9221120237041090560.  (* 0x7ff8000000000000 *)
Definition isnan (v : f64) : bool := is_nan 53 1024 v.

(** [nan_result]: the first NaN in index order, [x] before [y]. *)
Fixpoint first_nan (x y : list f64) : option f64 :=
  match x with
  | [] => find isnan y
  | a :: x' =>
      if isnan a then Some a else
      match y with
      | [] => first_nan x' []
      | b :: y' => if isnan b then Some b else first_nan x' y'
      end
  end.

Definition defined (result : f64) (x y : list f64) : f64 :=
  if isnan result then match first_nan x y with Some v => v | None => canonical_nan end
  else result.

Definition sum64 (x : list f64) : f64 :=
  match x with [] => zero | p :: rest => defined (fold_left fadd rest p) x [] end.

Definition sum2_step (st : f64 * f64) (p : f64) : f64 * f64 :=
  let '(next, q) := two_sum64 (fst st) p in (next, fadd (snd st) q).

Definition sum2_64 (x : list f64) : f64 :=
  match x with
  | [] => zero
  | p :: rest =>
      let st := fold_left sum2_step rest (p, zero) in
      defined (fadd (fst st) (snd st)) x []
  end.

Definition dot_step (p : f64) (ab : f64 * f64) : f64 := fadd p (fmul (fst ab) (snd ab)).

Definition dot64 (x y : list f64) : f64 :=
  match combine x y with
  | [] => zero
  | (a, b) :: rest => defined (fold_left dot_step rest (fmul a b)) x y
  end.

Definition dot2_step (st : f64 * f64) (ab : f64 * f64) : f64 * f64 :=
  let '(h, r) := two_prod64 (fst ab) (snd ab) in
  let '(next, q) := two_sum64 (fst st) h in
  (next, fadd (snd st) (fadd q r)).

Definition dot2_64 (x y : list f64) : f64 :=
  match combine x y with
  | [] => zero
  | (a, b) :: rest =>
      let st := fold_left dot2_step rest (two_prod64 a b) in
      defined (fadd (fst st) (snd st)) x y
  end.

Definition sum_squares64 (x : list f64) : f64 := dot64 x x.
Definition sum_squares2_64 (x : list f64) : f64 := dot2_64 x x.

(** [if magnitude > largest { largest = magnitude }]. *)
Definition larger (largest magnitude : f64) : f64 :=
  match Bcompare 53 1024 magnitude largest with Some Gt => magnitude | _ => largest end.

Fixpoint max_abs_from (largest : f64) (x : list f64) : f64 :=
  match x with
  | [] => largest
  | v :: rest =>
      if isnan v then v else
      max_abs_from (larger largest (b64_abs v)) rest
  end.
Definition max_abs64 (x : list f64) : f64 := max_abs_from zero x.

(** * The bounds of the transcription *)

Definition values (x : list f64) : list R := map B x.
Definition pairs (l : list (f64 * f64)) : list (R * R) := map (fun ab => (B (fst ab), B (snd ab))) l.

Lemma values_fmt x : Forall fmtF (values x).
Proof. apply Forall_forall. intros v H. apply in_map_iff in H as [a [<- _]]. apply B_fmt. Qed.

Lemma zero_finite : finite zero.
Proof. reflexivity. Qed.
Lemma zero_val : B zero = 0.
Proof. reflexivity. Qed.

Lemma canonical_is_nan : isnan canonical_nan = true.
Proof. reflexivity. Qed.

Lemma first_nan_is_nan x : forall y v, first_nan x y = Some v -> isnan v = true.
Proof.
  induction x as [ | a x IH]; intros y v; simpl.
  - intros H. exact (proj2 (find_some _ _ H)).
  - destruct (isnan a) eqn:A; [intros H; injection H as <-; exact A | ].
    destruct y as [ | b y]; [apply IH | ].
    destruct (isnan b) eqn:Bn; [intros H; injection H as <-; exact Bn | apply IH].
Qed.

Lemma nan_not_finite v : isnan v = true -> ~ finite v.
Proof. destruct v; unfold isnan; simpl; try discriminate; intros _ H; discriminate. Qed.

Lemma defined_finite r x y : finite (defined r x y) -> defined r x y = r /\ finite r.
Proof.
  unfold defined. destruct (isnan r) eqn:N.
  - intros F. exfalso. destruct (first_nan x y) as [v | ] eqn:E.
    + exact (nan_not_finite v (first_nan_is_nan x y v E) F).
    + exact (nan_not_finite _ canonical_is_nan F).
  - intros F. split; [reflexivity | exact F].
Qed.

Lemma fold_fadd_inv rest : forall p, finite (fold_left fadd rest p) ->
  finite p /\ B (fold_left fadd rest p) = rsum (B p) (values rest).
Proof.
  induction rest as [ | a rest IH]; intros p F; simpl in *.
  - split; [exact F | reflexivity].
  - destruct (IH (fadd p a) F) as [F1 E]. destruct (fadd_inv _ _ F1) as [Fp [_ Ea]].
    split; [exact Fp | ]. rewrite E, Ea. reflexivity.
Qed.

Lemma fold_sum2_inv rest : forall pi sigma,
  let st := fold_left sum2_step rest (pi, sigma) in
  finite (fst st) -> finite (snd st) ->
  finite pi /\ finite sigma /\
  B (fst st) = rsum (B pi) (values rest) /\
  B (snd st) = rsum (B sigma) (errors (B pi) (values rest)).
Proof.
  induction rest as [ | a rest IH]; intros pi sigma st Fp Fs.
  - unfold st in *. simpl in *. repeat split; assumption.
  - unfold st in *. cbn [fold_left] in *.
    assert (Step : sum2_step (pi, sigma) a
                   = (fst (two_sum64 pi a), fadd sigma (snd (two_sum64 pi a)))).
    { unfold sum2_step. cbn [fst snd]. destruct (two_sum64 pi a); reflexivity. }
    rewrite Step in Fp, Fs |- *.
    destruct (two_sum64 pi a) as [next q] eqn:T. cbn [fst snd] in Fp, Fs |- *.
    destruct (IH next (fadd sigma q) Fp Fs) as [Fn [Fsq [E1 E2]]].
    destruct (fadd_inv _ _ Fsq) as [Fsig [Fq Es]].
    pose proof (two_sum_inv pi a) as I. rewrite T in I. cbn [fst snd] in I.
    destruct (I Fq) as [Fpi [_ [_ [En Ex]]]].
    split; [exact Fpi | split; [exact Fsig | ]].
    assert (Eq : B q = B pi + B a - rndF (B pi + B a)) by (rewrite <- En; lra).
    split.
    + rewrite E1, En. reflexivity.
    + rewrite E2, Es, En, Eq. reflexivity.
Qed.

(** [sum]: [γ_(n-1)·S]. *)
Theorem sum_bound x : finite (sum64 x) -> INR (length x) * u < 1 ->
  Rabs (B (sum64 x) - total (values x)) <= gamma (Nat.pred (length x)) * atotal (values x).
Proof.
  destruct x as [ | p rest]; simpl sum64; intros F Hn.
  - simpl. rewrite gamma_0. change (B zero) with 0.
    unfold Rminus. rewrite Ropp_0, Rplus_0_r, Rabs_R0. lra.
  - destruct (defined_finite _ _ _ F) as [E Fr]. rewrite E.
    destruct (fold_fadd_inv rest p Fr) as [_ V]. rewrite V.
    cbn [length Nat.pred]. unfold values at 2 3. cbn [map].
    assert (Hm : INR (length (values rest)) * u < 1).
    { apply Rle_lt_trans with (2 := Hn). apply ku_mono. unfold values. rewrite map_length. cbn [length]. apply Nat.le_succ_diag_r. }
    pose proof (sum_real (B p) (values rest) (B_fmt p) (values_fmt rest) Hm) as R.
    unfold values in R at 3. rewrite map_length in R. exact R.
Qed.

(** [sum2]: [u·|s| + γ_(n-1)²·S]. *)
Theorem sum2_bound x : finite (sum2_64 x) -> INR (length x) * u < 1 ->
  Rabs (B (sum2_64 x) - total (values x))
  <= u * Rabs (total (values x))
     + gamma (Nat.pred (length x)) * gamma (Nat.pred (length x)) * atotal (values x).
Proof.
  destruct x as [ | p rest]; simpl sum2_64; intros F Hn.
  - simpl. rewrite gamma_0. change (B zero) with 0.
    unfold Rminus. rewrite Ropp_0, Rplus_0_r, Rabs_R0. lra.
  - destruct (defined_finite _ _ _ F) as [E Fr]. rewrite E.
    destruct (fadd_inv _ _ Fr) as [Fp [Fs V]]. rewrite V.
    destruct (fold_sum2_inv rest p zero Fp Fs) as [_ [_ [E1 E2]]].
    rewrite E1, E2, zero_val. cbn [length Nat.pred]. unfold values at 3 4 5. cbn [map].
    assert (L : length (values rest) = length rest) by apply map_length.
    assert (Hm : INR (S (length (values rest))) * u < 1) by (rewrite L; exact Hn).
    pose proof (sum2_real (B p) (values rest) (B_fmt p) (values_fmt rest) Hm) as R.
    rewrite L in R. exact R.
Qed.

Lemma fold_dot_inv rest : forall p, finite (fold_left dot_step rest p) ->
  finite p /\ B (fold_left dot_step rest p) = rsum (B p) (map rounded (pairs rest)).
Proof.
  induction rest as [ | a rest IH]; intros p F; simpl in *.
  - split; [exact F | reflexivity].
  - destruct (IH (dot_step p a) F) as [F1 E]. unfold dot_step in F1.
    destruct (fadd_inv _ _ F1) as [Fp [Fm Ea]]. destruct (fmul_inv _ _ Fm) as [_ [_ Em]].
    split; [exact Fp | ]. rewrite E. unfold dot_step. rewrite Ea, Em. reflexivity.
Qed.

(** [dot]: [γ_n·|x|ᵀ|y|] when no product underflows. *)
Theorem dot_bound x y : finite (dot64 x y) -> INR (length (combine x y)) * u < 1 ->
  Forall (fun xy => normal_or_zero (product xy)) (pairs (combine x y)) ->
  Rabs (B (dot64 x y) - dot_exact (pairs (combine x y)))
  <= gamma (length (combine x y)) * dot_abs (pairs (combine x y)).
Proof.
  unfold dot64. destruct (combine x y) as [ | [a b] rest]; intros F Hn H.
  - simpl. rewrite gamma_0. change (B zero) with 0. unfold dot_exact, dot_abs. simpl.
    unfold Rminus. rewrite Ropp_0, Rplus_0_r, Rabs_R0. lra.
  - destruct (defined_finite _ _ _ F) as [E Fr]. rewrite E.
    destruct (fold_dot_inv rest _ Fr) as [Fm V]. destruct (fmul_inv _ _ Fm) as [_ [_ Em]].
    rewrite V, Em. cbn [length]. unfold pairs at 2 3. cbn [map fst snd]. fold (pairs rest).
    change (rndF (B a * B b)) with (rounded (B a, B b)).
    assert (L : length (pairs rest) = length rest) by apply map_length.
    pose proof (dot_real (B a, B b) (pairs rest)) as R. rewrite L in R.
    apply R; [exact H | exact Hn].
Qed.

Lemma fold_dot2_inv rest : forall p s,
  let st := fold_left dot2_step rest (p, s) in
  finite (fst st) -> finite (snd st) ->
  Forall (fun xy => in_two_prod_domain (fst xy) (snd xy)) (pairs rest) ->
  finite p /\ finite s /\
  Forall (fun xy => fmtF (residual xy)) (pairs rest) /\
  B (fst st) = rsum (B p) (map rounded (pairs rest)) /\
  B (snd st) = rsum (B s) (corrections (errors (B p) (map rounded (pairs rest)))
                                       (map residual (pairs rest))).
Proof.
  induction rest as [ | [a b] rest IH]; intros p s st Fp Fs D.
  - unfold st in *. simpl in *. repeat split; try assumption; constructor.
  - unfold st in *. cbn [fold_left] in *. unfold pairs in D. cbn [map fst snd] in D.
    fold (pairs rest) in D. inversion D as [ | x y D0 Dr]; subst x y.
    cbn [fst snd] in D0.
    assert (Step : dot2_step (p, s) (a, b)
                   = (fst (two_sum64 p (fst (two_prod64 a b))),
                      fadd s (fadd (snd (two_sum64 p (fst (two_prod64 a b)))) (snd (two_prod64 a b))))).
    { unfold dot2_step. cbn [fst snd]. destruct (two_prod64 a b) as [h0 r0]. cbn [fst snd].
      destruct (two_sum64 p h0); reflexivity. }
    rewrite Step in Fp, Fs |- *.
    destruct (two_prod64 a b) as [h r] eqn:P. cbn [fst snd] in Fp, Fs |- *.
    destruct (two_sum64 p h) as [next q] eqn:T. cbn [fst snd] in Fp, Fs |- *.
    destruct (IH next (fadd s (fadd q r)) Fp Fs Dr) as [Fn [Fsn [Fres [E1 E2]]]].
    destruct (fadd_inv _ _ Fsn) as [Fsf [Fqr Es]].
    destruct (fadd_inv _ _ Fqr) as [Fq [Fr Eqr]].
    pose proof (two_sum_inv p h) as I. rewrite T in I. cbn [fst snd] in I.
    destruct (I Fq) as [Fpf [_ [_ [En Ex]]]].
    pose proof (two_prod_inv a b) as J. rewrite P in J. cbn [fst snd] in J.
    destruct (J Fr) as [_ [Eh [_ [_ Exact]]]]. specialize (Exact D0).
    assert (Eq : B q = B p + B h - rndF (B p + B h)) by (rewrite <- En; lra).
    assert (Er : B r = residual (B a, B b)).
    { unfold residual, rounded, product. cbn [fst snd]. rewrite <- Eh. lra. }
    split; [exact Fpf | split; [exact Fsf | ]].
    unfold pairs. cbn [map fst snd]. fold (pairs rest).
    change (rounded (B a, B b)) with (rndF (B a * B b)). rewrite <- Eh, <- Er.
    split; [ | split].
    + constructor; [rewrite <- Er; apply B_fmt | exact Fres].
    + rewrite E1, En. reflexivity.
    + rewrite E2, Es, Eqr, En, Eq. reflexivity.
Qed.

Lemma domain_normal l : Forall (fun xy => in_two_prod_domain (fst xy) (snd xy)) l ->
  Forall (fun xy => normal_or_zero (product xy)) l.
Proof.
  intros H. apply Forall_impl with (2 := H). intros [a b] D. apply two_prod_domain_normal, D.
Qed.

(** [dot2]: [u·|xᵀy| + γ_n²·|x|ᵀ|y|] when every [two_prod] is exact. *)
Theorem dot2_bound x y : finite (dot2_64 x y) -> INR (length (combine x y)) * u < 1 ->
  Forall (fun xy => in_two_prod_domain (fst xy) (snd xy)) (pairs (combine x y)) ->
  Rabs (B (dot2_64 x y) - dot_exact (pairs (combine x y)))
  <= u * Rabs (dot_exact (pairs (combine x y)))
     + gamma (length (combine x y)) * gamma (length (combine x y)) * dot_abs (pairs (combine x y)).
Proof.
  unfold dot2_64. destruct (combine x y) as [ | [a b] rest]; intros F Hn D.
  - simpl. rewrite gamma_0. change (B zero) with 0. unfold dot_exact, dot_abs. simpl.
    unfold Rminus. rewrite Ropp_0, Rplus_0_r, Rabs_R0. lra.
  - destruct (defined_finite _ _ _ F) as [E Fr]. rewrite E.
    destruct (fadd_inv _ _ Fr) as [Fp [Fs V]]. rewrite V.
    pose proof (domain_normal _ D) as N.
    unfold pairs in D. cbn [map fst snd] in D. fold (pairs rest) in D.
    inversion D as [ | x0 y0 D0 Dr]; subst x0 y0. cbn [fst snd] in D0.
    destruct (two_prod64 a b) as [h r] eqn:P.
    destruct (fold_dot2_inv rest h r Fp Fs Dr) as [_ [Frf [Fres [E1 E2]]]].
    pose proof (two_prod_inv a b) as J. rewrite P in J. cbn [fst snd] in J.
    destruct (J Frf) as [_ [Eh [_ [_ Exact]]]]. specialize (Exact D0).
    assert (Er : B r = residual (B a, B b)).
    { unfold residual, rounded, product. cbn [fst snd]. rewrite <- Eh. lra. }
    rewrite E1, E2. cbn [length]. unfold pairs at 3 4 5. cbn [map fst snd]. fold (pairs rest).
    rewrite Er, Eh. change (rndF (B a * B b)) with (rounded (B a, B b)).
    assert (L : length (pairs rest) = length rest) by apply map_length.
    pose proof (dot2_real (B a, B b) (pairs rest)) as R. rewrite L in R. cbv zeta in R.
    apply R; [exact N | | exact Hn].
    constructor; [rewrite <- Er; apply B_fmt | exact Fres].
Qed.

(** [sum_squares] and [sum_squares2] are the dot products of a slice with
    itself, with those bounds. *)
Theorem sum_squares_bound x : finite (sum_squares64 x) -> INR (length (combine x x)) * u < 1 ->
  Forall (fun xy => normal_or_zero (product xy)) (pairs (combine x x)) ->
  Rabs (B (sum_squares64 x) - dot_exact (pairs (combine x x)))
  <= gamma (length (combine x x)) * dot_abs (pairs (combine x x)).
Proof. exact (dot_bound x x). Qed.

Theorem sum_squares2_bound x : finite (sum_squares2_64 x) -> INR (length (combine x x)) * u < 1 ->
  Forall (fun xy => in_two_prod_domain (fst xy) (snd xy)) (pairs (combine x x)) ->
  Rabs (B (sum_squares2_64 x) - dot_exact (pairs (combine x x)))
  <= u * Rabs (dot_exact (pairs (combine x x)))
     + gamma (length (combine x x)) * gamma (length (combine x x)) * dot_abs (pairs (combine x x)).
Proof. exact (dot2_bound x x). Qed.

(** For a sum of squares the magnitudes are the exact result itself. *)
Lemma squares_abs x : dot_abs (pairs (combine x x)) = dot_exact (pairs (combine x x)).
Proof.
  unfold dot_abs, dot_exact, pairs. induction x as [ | a x IH]; simpl; [reflexivity | ].
  rewrite IH. unfold product at 1 3. cbn [fst snd]. rewrite Rabs_pos_eq; [reflexivity | nra].
Qed.

(** * Non-finite inputs *)

Lemma fadd_nan_l x y : isnan x = true -> isnan (fadd x y) = true.
Proof. destruct x; unfold isnan; simpl; try discriminate; destruct y; reflexivity. Qed.
Lemma fadd_nan_r x y : isnan y = true -> isnan (fadd x y) = true.
Proof. destruct y; unfold isnan; simpl; try discriminate; destruct x; reflexivity. Qed.
Lemma fmul_nan_l x y : isnan x = true -> isnan (fmul x y) = true.
Proof. destruct x; unfold isnan; simpl; try discriminate; destruct y; reflexivity. Qed.
Lemma fmul_nan_r x y : isnan y = true -> isnan (fmul x y) = true.
Proof. destruct y; unfold isnan; simpl; try discriminate; destruct x; reflexivity. Qed.

Lemma fold_fadd_nan rest : forall p, isnan p = true \/ existsb isnan rest = true ->
  isnan (fold_left fadd rest p) = true.
Proof.
  induction rest as [ | a rest IH]; intros p H; simpl in *.
  - destruct H as [H | H]; [exact H | discriminate].
  - apply IH. destruct H as [H | H]; [left; apply fadd_nan_l, H | ].
    apply orb_true_iff in H as [H | H]; [left; apply fadd_nan_r, H | right; exact H].
Qed.

Lemma first_nan_some x : forall y, existsb isnan x = true \/ existsb isnan y = true ->
  exists v, first_nan x y = Some v.
Proof.
  induction x as [ | a x IH]; intros y H; simpl.
  - destruct H as [H | H]; [discriminate | ].
    destruct (find isnan y) as [v | ] eqn:E; [now exists v | ].
    apply existsb_exists in H as [v [I N]]. rewrite (find_none _ _ E v I) in N. discriminate.
  - destruct (isnan a) eqn:A; [now exists a | ].
    destruct y as [ | b y].
    + apply IH. destruct H as [H | H]; [ | discriminate]. simpl in H. rewrite A in H. now left.
    + destruct (isnan b) eqn:Bn; [now exists b | ]. apply IH.
      simpl in H. rewrite A, Bn in H. exact H.
Qed.

Lemma defined_nan r x y v : isnan r = true -> first_nan x y = Some v -> defined r x y = v.
Proof. intros N E. unfold defined. now rewrite N, E. Qed.

(** With a NaN input, [sum] returns the first one, unchanged. *)
Theorem sum_nan x v : existsb isnan x = true -> first_nan x [] = Some v -> sum64 x = v.
Proof.
  destruct x as [ | p rest]; [discriminate | ]. intros H E. unfold sum64.
  apply defined_nan; [ | exact E]. apply fold_fadd_nan. apply orb_true_iff in H. exact H.
Qed.

Lemma two_sum_fst a b : fst (two_sum64 a b) = fadd a b.
Proof. reflexivity. Qed.

Lemma sum2_step_fst st p : fst (sum2_step st p) = fadd (fst st) p.
Proof. reflexivity. Qed.

Lemma fold_sum2_fst rest : forall st, fst (fold_left sum2_step rest st) = fold_left fadd rest (fst st).
Proof.
  induction rest as [ | a rest IH]; intros st; [reflexivity | ].
  cbn [fold_left]. rewrite IH, sum2_step_fst. reflexivity.
Qed.

Theorem sum2_nan x v : existsb isnan x = true -> first_nan x [] = Some v -> sum2_64 x = v.
Proof.
  destruct x as [ | p rest]; [discriminate | ]. intros H E. unfold sum2_64.
  apply defined_nan; [ | exact E]. apply fadd_nan_l. rewrite fold_sum2_fst. cbn [fst].
  apply fold_fadd_nan. apply orb_true_iff in H. exact H.
Qed.

Definition either_nan (ab : f64 * f64) : bool := isnan (fst ab) || isnan (snd ab).

Lemma combine_nan x : forall y, length x = length y ->
  existsb isnan x = true \/ existsb isnan y = true -> existsb either_nan (combine x y) = true.
Proof.
  induction x as [ | a x IH]; intros [ | b y] L H; try discriminate.
  - destruct H; discriminate.
  - simpl in *. injection L as L. unfold either_nan at 1. cbn [fst snd].
    destruct (isnan a), (isnan b); try reflexivity. simpl in *. apply IH; assumption.
Qed.

Lemma fold_dot_nan rest : forall p, isnan p = true \/ existsb either_nan rest = true ->
  isnan (fold_left dot_step rest p) = true.
Proof.
  induction rest as [ | a rest IH]; intros p H; simpl in *.
  - destruct H as [H | H]; [exact H | discriminate].
  - apply IH. unfold dot_step. destruct H as [H | H]; [left; apply fadd_nan_l, H | ].
    apply orb_true_iff in H as [H | H]; [left; apply fadd_nan_r | right; exact H].
    apply orb_true_iff in H as [H | H]; [apply fmul_nan_l, H | apply fmul_nan_r, H].
Qed.

Theorem dot_nan x y v : length x = length y ->
  existsb isnan x = true \/ existsb isnan y = true -> first_nan x y = Some v -> dot64 x y = v.
Proof.
  intros L H E. pose proof (combine_nan x y L H) as C. unfold dot64.
  destruct (combine x y) as [ | [a b] rest]; [discriminate | ].
  apply defined_nan; [ | exact E]. apply fold_dot_nan. simpl in C.
  apply orb_true_iff in C as [C | C]; [left | right; exact C].
  unfold either_nan in C. cbn [fst snd] in C.
  apply orb_true_iff in C as [C | C]; [apply fmul_nan_l, C | apply fmul_nan_r, C].
Qed.

Lemma dot2_step_fst st ab : fst (dot2_step st ab) = fadd (fst st) (fmul (fst ab) (snd ab)).
Proof. reflexivity. Qed.

Lemma fold_dot2_fst rest : forall st, fst (fold_left dot2_step rest st)
  = fold_left dot_step rest (fst st).
Proof.
  induction rest as [ | a rest IH]; intros st; [reflexivity | ].
  cbn [fold_left]. rewrite IH, dot2_step_fst. reflexivity.
Qed.

Theorem dot2_nan x y v : length x = length y ->
  existsb isnan x = true \/ existsb isnan y = true -> first_nan x y = Some v -> dot2_64 x y = v.
Proof.
  intros L H E. pose proof (combine_nan x y L H) as C. unfold dot2_64.
  destruct (combine x y) as [ | [a b] rest]; [discriminate | ].
  apply defined_nan; [ | exact E]. apply fadd_nan_l. rewrite fold_dot2_fst.
  change (fst (two_prod64 a b)) with (fmul a b). apply fold_dot_nan. simpl in C.
  apply orb_true_iff in C as [C | C]; [left | right; exact C].
  unfold either_nan in C. cbn [fst snd] in C.
  apply orb_true_iff in C as [C | C]; [apply fmul_nan_l, C | apply fmul_nan_r, C].
Qed.

(** A NaN the arithmetic itself creates is the canonical one. *)
Theorem defined_created r x y : isnan r = true -> existsb isnan x = false ->
  existsb isnan y = false -> defined r x y = canonical_nan.
Proof.
  intros N Hx Hy. unfold defined. rewrite N.
  destruct (first_nan x y) as [v | ] eqn:E; [ | reflexivity]. exfalso.
  revert y Hy E. induction x as [ | a x IH]; intros y Hy E; simpl in *.
  - apply find_some in E as [I V].
    assert (existsb isnan y = true) by (apply existsb_exists; exists v; split; assumption).
    congruence.
  - apply orb_false_iff in Hx as [Ha Hx]. rewrite Ha in E.
    destruct y as [ | b y]; [exact (IH Hx [] Hy E) | ].
    simpl in Hy. apply orb_false_iff in Hy as [Hb Hy]. rewrite Hb in E. exact (IH Hx y Hy E).
Qed.

(** * The largest magnitude *)

Lemma max_abs_from_ok x : forall m, finite m -> 0 <= B m -> Forall (fun v => finite v) x ->
  let r := max_abs_from m x in
  finite r /\ B m <= B r /\ Forall (fun v => Rabs (B v) <= B r) x /\
  (B r = B m \/ exists v, In v x /\ B r = Rabs (B v)).
Proof.
  induction x as [ | a x IH]; intros m Fm Pm Fx; simpl.
  - repeat split; [exact Fm | lra | constructor | now left].
  - inversion Fx as [ | p q Fa Fr]; subst p q.
    assert (Na : isnan a = false) by (destruct a; try reflexivity; discriminate).
    rewrite Na.
    assert (Fabs : finite (b64_abs a)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fa).
    assert (Vabs : B (b64_abs a) = Rabs (B a)) by apply B2R_Babs.
    set (n := larger m (b64_abs a)).
    assert (N : finite n /\ B m <= B n /\ Rabs (B a) <= B n /\ (B n = B m \/ B n = Rabs (B a))).
    { unfold n, larger. rewrite Bcompare_correct by assumption.
      destruct (Rcompare (B (b64_abs a)) (B m)) eqn:C.
      - apply Rcompare_Eq_inv in C. rewrite Vabs in C.
        split; [exact Fm | split; [lra | split; [lra | now left]]].
      - apply Rcompare_Lt_inv in C. rewrite Vabs in C.
        split; [exact Fm | split; [lra | split; [lra | now left]]].
      - apply Rcompare_Gt_inv in C. rewrite Vabs in C.
        split; [exact Fabs | split; [rewrite Vabs; lra | split; [rewrite Vabs; lra | now right]]]. }
    destruct N as [Fn [Le [La Which]]].
    destruct (IH n Fn ltac:(lra) Fr) as [R1 [R2 [R3 R4]]].
    cbv zeta in R1, R2, R3, R4 |- *.
    split; [exact R1 | split; [lra | split]].
    + constructor; [lra | exact R3].
    + destruct R4 as [R4 | [v [I V]]].
      * destruct Which as [W | W].
        -- left. rewrite R4. exact W.
        -- right. exists a. split; [now left | rewrite R4; exact W].
      * right. exists v. split; [now right | exact V].
Qed.

(** [max_abs] is exact on finite inputs. *)
Theorem max_abs_exact x : Forall (fun v => finite v) x ->
  let r := max_abs64 x in
  finite r /\ Forall (fun v => Rabs (B v) <= B r) x /\
  (x = [] -> r = zero) /\ (x <> [] -> exists v, In v x /\ B r = Rabs (B v)).
Proof.
  intros Fx r.
  destruct (max_abs_from_ok x zero zero_finite ltac:(rewrite zero_val; lra) Fx)
    as [R1 [_ [R3 R4]]].
  split; [exact R1 | split; [exact R3 | split]].
  - intros ->. reflexivity.
  - intros Ne. destruct R4 as [R4 | R4]; [ | exact R4].
    destruct x as [ | a x]; [congruence | ]. exists a. split; [now left | ].
    inversion R3 as [ | p q La _]; subst p q.
    unfold r, max_abs64. rewrite R4, zero_val in La |- *.
    pose proof (Rabs_pos (B a)). lra.
Qed.

(** A NaN anywhere: [max_abs] returns the first one. *)
Theorem max_abs_nan x : forall v, find isnan x = Some v -> max_abs64 x = v.
Proof.
  unfold max_abs64. generalize zero. induction x as [ | a x IH]; intros m v; simpl; [discriminate | ].
  destruct (isnan a); [intros H; now injection H | apply IH].
Qed.
