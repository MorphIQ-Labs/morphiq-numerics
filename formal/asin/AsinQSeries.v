(** The accurate path's [Q256] Horner series ([AsinKernel.q_series]): each level
    [1 - (s c) h] computed with the [Q256] multiply and add is within [2^-252] of the
    ideal level, whatever its length, since [s c <= 0.31]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec Limbs QRound.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSeries.
Import ListNotations.
Open Scope R_scope.

Lemma q_one_valid : Q256Real.valid q_one /\ qval q_one = 1.
Proof.
  assert (Hv : Limbs.v [0%Z; 0%Z; 0%Z; (2 ^ 63)%Z] = (2 ^ 255)%Z) by (vm_compute; reflexivity).
  unfold q_one. split.
  - split.
    + split; [ | reflexivity]. repeat constructor; unfold Limbs.B; lia.
    + right. unfold normalized. cbn [m]. rewrite Hv. split; [apply Z.pow_le_mono_r; lia | apply Z.pow_lt_mono_r; lia].
  - unfold qval. cbn [m e neg]. rewrite Hv. unfold val, F2R. cbn [Fnum Fexp].
    replace (IZR (2 ^ 255)) with (bpow radix2 255) by (symmetry; apply (IZR_Zpower radix2); lia).
    rewrite <- bpow_plus. replace (255 + -255)%Z with 0%Z by reflexivity. reflexivity.
Qed.

Lemma q_series_cons s m0 e0 steps :
  q_series s ((m0, e0) :: steps) = q_sub q_one (Q256.mul (Q256.mul s (Q256.new false m0 e0)) (q_series s steps)).
Proof.
  unfold q_series. cbn [rev]. rewrite fold_left_app. reflexivity.
Qed.

Lemma q_series_nil s : q_series s [] = q_one.
Proof. reflexivity. Qed.

Lemma bpow_254 : bpow radix2 (-252) = 4 * bpow radix2 (-254) /\ bpow radix2 (-255) = bpow radix2 (-254) / 2 /\
  0 < bpow radix2 (-254) /\ bpow radix2 (-254) <= / 1000000000000000000000000000000000000000000000000000000000000.
Proof.
  split; [ | split; [ | split]].
  - replace (-252)%Z with (-254 + 2)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 2) with 4. ring.
  - replace (-255)%Z with (-254 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field.
  - apply bpow_gt_0.
  - bpow_num. interval with (i_prec 300).
Qed.


Lemma prod3 a b c d : Rabs a <= d -> Rabs b <= d -> Rabs c <= d -> 0 <= d <= / 1000 ->
  Rabs ((1 + a) * (1 + b) * (1 + c) - 1) <= 3.01 * d.
Proof.
  intros Ha Hb Hc [Hd0 Hd1].
  replace ((1 + a) * (1 + b) * (1 + c) - 1) with (a + b + c + (a * b + a * c + b * c) + a * b * c) by ring.
  assert (Hab : Rabs (a * b) <= d * d) by (rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Ha | exact Hb]).
  assert (Hac : Rabs (a * c) <= d * d) by (rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Ha | exact Hc]).
  assert (Hbc : Rabs (b * c) <= d * d) by (rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hb | exact Hc]).
  assert (Habc : Rabs (a * b * c) <= d * d * d).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hab | exact Hc]. }
  assert (Hd2 : d * d <= d / 1000) by nra.
  assert (Hd3 : d * d * d <= d / 1000000) by nra.
  apply Rabs_le_inv in Ha. apply Rabs_le_inv in Hb. apply Rabs_le_inv in Hc.
  apply Rabs_le_inv in Hab. apply Rabs_le_inv in Hac. apply Rabs_le_inv in Hbc. apply Rabs_le_inv in Habc.
  apply Rabs_le. split; lra.
Qed.

(** One level of the series. *)
Lemma series_step_err (s c h : q256) cc H :
  Q256Real.valid s -> Q256Real.valid c -> Q256Real.valid h ->
  0 <= qval s <= 0.62 -> 0 < cc <= / 2 ->
  Rabs (qval c - cc) <= bpow radix2 (-254) * cc ->
  0.69 <= H <= 1 -> Rabs (qval h - H) <= bpow radix2 (-252) ->
  Q256Real.valid (q_sub q_one (Q256.mul (Q256.mul s c) h)) /\
  Rabs (qval (q_sub q_one (Q256.mul (Q256.mul s c) h)) - (1 - qval s * cc * H)) <= bpow radix2 (-252).
Proof.
  intros Vs Vc Vh Hs Hcc Hc HH Hh.
  destruct q_one_valid as [Vone Qone].
  destruct (mul_relative s c Vs Vc) as [V1 [d1 [D1 E1]]].
  destruct (mul_relative (Q256.mul s c) h V1 Vh) as [V2 [d2 [D2 E2]]].
  destruct (neg_any (Q256.mul (Q256.mul s c) h) V2) as [V3 E3].
  destruct (add_any q_one (neg_q (Q256.mul (Q256.mul s c) h)) Vone V3) as [V4 E4].
  unfold q_sub. split; [exact V4 | ].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]].
  set (U := bpow radix2 (-254)) in *.
  set (sv := qval s) in *. set (cv := qval c) in *. set (hv := qval h) in *.
  set (p2 := qval (Q256.mul (Q256.mul s c) h)) in *.
  set (r := qval (Q256.add q_one (neg_q (Q256.mul (Q256.mul s c) h)))) in *.
  rewrite E3, Qone in E4.
  rewrite B255 in D1, D2.
  assert (Hsc : 0 <= sv * cc <= 0.31) by (split; nra).
  set (eps := (cv - cc) / cc).
  assert (Heps : cv = cc * (1 + eps)) by (unfold eps; field; lra).
  assert (Heps' : Rabs eps <= U).
  { unfold eps. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq cc) by lra.
    apply (Rmult_le_reg_r cc); [lra | ]. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  set (P := (1 + eps) * (1 + d1) * (1 + d2)).
  assert (HP : Rabs (P - 1) <= 3.01 * U).
  { unfold P. apply prod3; [exact Heps' | lra | lra | lra]. }
  assert (Hp2 : p2 = sv * cc * hv * P).
  { rewrite E2, E1, Heps. unfold P. ring. }
  assert (Hh0 : Rabs hv <= 1.01).
  { apply Rabs_le_inv in Hh. apply Rabs_le. rewrite B252 in Hh. split; nra. }
  assert (Hdiff : Rabs (p2 - sv * cc * H) <= 0.31 * (4 * U * 1.0001 + 3.01 * U)).
  { replace (p2 - sv * cc * H) with ((sv * cc) * ((hv - H) * P + H * (P - 1))) by (rewrite Hp2; ring).
    rewrite Rabs_mult, (Rabs_pos_eq (sv * cc)) by lra.
    apply Rle_trans with (0.31 * Rabs ((hv - H) * P + H * (P - 1))).
    - apply Rmult_le_compat_r; [apply Rabs_pos | lra].
    - apply Rmult_le_compat_l; [lra | ].
      apply Rle_trans with (Rabs ((hv - H) * P) + Rabs (H * (P - 1))); [apply Rabs_triang | ].
      rewrite !Rabs_mult. rewrite B252 in Hh.
      assert (HPa : Rabs P <= 1.0001) by (apply Rabs_le_inv in HP; apply Rabs_le; split; nra).
      rewrite (Rabs_pos_eq H) by lra.
      pose proof (Rabs_pos (hv - H)). pose proof (Rabs_pos P). pose proof (Rabs_pos (P - 1)).
      nra. }
  assert (Hsch : 0 <= sv * cc * H <= 0.31) by (split; nra).
  assert (Hp2b : Rabs p2 <= 1).
  { apply Rabs_le. apply Rabs_le_inv in Hdiff. split; nra. }
  assert (Hmax : Rmax (Rabs 1) (Rabs (- p2)) <= 1).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_Ropp; exact Hp2b]. }
  assert (HE4 : Rabs (r - (1 + - p2)) <= U).
  { apply Rle_trans with (1 := E4). replace (U) with (U * 1) at 2 by ring. apply Rmult_le_compat_l; [lra | exact Hmax]. }
  replace (r - (1 - sv * cc * H)) with ((r - (1 + - p2)) + (sv * cc * H - p2)) by ring.
  apply Rle_trans with (Rabs (r - (1 + - p2)) + Rabs (sv * cc * H - p2)); [apply Rabs_triang | ].
  rewrite (Rabs_minus_sym (sv * cc * H) p2). rewrite B252. nra.
Qed.

(** The ideal coefficients [cs] approximate the [Q256] constants of [steps]. *)
Fixpoint const_ok (steps : list (list Z * Z)) (cs : list R) : Prop :=
  match steps, cs with
  | nil, nil => True
  | (m0, e0) :: st, cc :: cs' =>
      (0 < cc <= / 2) /\ Rabs (qval (Q256.new false m0 e0) - cc) <= bpow radix2 (-254) * cc /\
      ok4 m0 /\ const_ok st cs'
  | _, _ => False
  end.

Lemma const_ok_forall steps cs : const_ok steps cs -> Forall (fun c => 0 <= c <= / 2) cs.
Proof.
  revert cs. induction steps as [ | [m0 e0] st IH]; intros [ | cc cs'] H; simpl in H; try contradiction.
  - constructor.
  - destruct H as [Hc [_ [_ H']]]. constructor; [lra | exact (IH _ H')].
Qed.

Lemma ser_range cs s : Forall (fun c => 0 <= c <= / 2) cs -> 0 <= s <= 0.62 -> 0.69 <= ser s cs <= 1.
Proof.
  intros F S. induction F as [ | c cs' Hc F IH]; simpl.
  - lra.
  - assert (0 <= s * c <= 0.31) by (split; nra). nra.
Qed.

Theorem series_error steps cs s : const_ok steps cs -> Q256Real.valid s -> 0 <= qval s <= 0.62 ->
  Q256Real.valid (q_series s steps) /\ Rabs (qval (q_series s steps) - ser (qval s) cs) <= bpow radix2 (-252).
Proof.
  revert cs. induction steps as [ | [m0 e0] st IH]; intros [ | cc cs'] Hc Vs Hs; simpl in Hc; try contradiction.
  - destruct q_one_valid as [V Q]. rewrite q_series_nil. split; [exact V | ].
    change (ser (qval s) nil) with 1. rewrite Q.
    replace (1 - 1) with 0 by ring. rewrite Rabs_R0. apply bpow_ge_0.
  - destruct Hc as [Hcc [Hce [Hok Hc']]].
    destruct (IH cs' Hc' Vs Hs) as [Vh Eh].
    pose proof (ser_range cs' (qval s) (const_ok_forall st cs' Hc') Hs) as Hr.
    destruct (series_step_err s (Q256.new false m0 e0) (q_series s st) cc (ser (qval s) cs') Vs
      (new_valid false m0 e0 Hok) Vh Hs Hcc Hce Hr Eh) as [V E].
    rewrite q_series_cons. split; [exact V | ].
    change (ser (qval s) (cc :: cs')) with (1 - qval s * cc * ser (qval s) cs'). exact E.
Qed.

(** Exact checks of the [Q256] constants against [1/den]. *)
Definition limbs_check (l : list Z) : bool :=
  (length l =? 4)%nat && forallb (fun x => (0 <=? x)%Z && (x <? 2 ^ 64)%Z) l.

Definition step_check (den : Z) (st : list Z * Z) : bool :=
  limbs_check (fst st) && (snd st <=? -254)%Z &&
  (Z.abs (den * Limbs.v (fst st) - 2 ^ (- snd st)) <=? 2 ^ (- snd st - 254))%Z.

Fixpoint steps_check (dens : nat -> Z) (j : nat) (steps : list (list Z * Z)) : bool :=
  match steps with
  | nil => true
  | st :: tl => step_check (dens j) st && (2 <=? dens j)%Z && steps_check dens (S j) tl
  end.

Lemma limbs_check_ok l : limbs_check l = true -> ok4 l.
Proof.
  unfold limbs_check. intros H. rewrite andb_true_iff in H. destruct H as [L F].
  apply Nat.eqb_eq in L. split; [ | exact L].
  unfold limbs_ok. rewrite forallb_forall in F. apply Forall_forall. intros x Hx.
  specialize (F x Hx). rewrite andb_true_iff in F. destruct F as [A B'].
  apply Z.leb_le in A. apply Z.ltb_lt in B'. unfold Limbs.B. lia.
Qed.

Lemma step_check_ok den m0 e0 : step_check den (m0, e0) = true -> (2 <= den)%Z ->
  ok4 m0 /\ Rabs (qval (Q256.new false m0 e0) - / IZR den) <= bpow radix2 (-254) * / IZR den.
Proof.
  unfold step_check. cbn [fst snd]. intros H D2.
  repeat rewrite andb_true_iff in H. destruct H as [[Lc Ee] Er].
  apply Z.leb_le in Ee. apply Z.leb_le in Er.
  pose proof (limbs_check_ok _ Lc) as Ok. split; [exact Ok | ].
  rewrite new_val by exact Ok. unfold val.
  unfold F2R. cbn [Fnum Fexp].
  assert (Hd : 0 < IZR den) by (apply IZR_lt; lia).
  set (N := (- e0)%Z) in *.
  assert (HN : (254 <= N)%Z) by (unfold N; lia).
  set (b := bpow radix2 (N - 254)). set (k := bpow radix2 254).
  assert (Pb : 0 < b) by apply bpow_gt_0. assert (Pk : 0 < k) by apply bpow_gt_0.
  assert (HBn : IZR (2 ^ N) = b * k).
  { unfold b, k. rewrite <- bpow_plus. replace (N - 254 + 254)%Z with N by ring. apply IZR_pow2'. lia. }
  assert (Hb2 : IZR (2 ^ (N - 254)) = b) by (unfold b; apply IZR_pow2'; lia).
  assert (E1 : bpow radix2 e0 = / (b * k)).
  { rewrite <- HBn. rewrite IZR_pow2' by lia. replace e0 with (- N)%Z by (unfold N; ring). rewrite bpow_opp. reflexivity. }
  assert (HB : bpow radix2 (-254) = / k) by (unfold k; bpow_num; reflexivity).
  rewrite E1, HB.
  set (X := IZR den * IZR (Limbs.v m0) - b * k).
  assert (HX : Rabs X <= b).
  { unfold X. rewrite <- HBn, <- Hb2. rewrite <- mult_IZR, <- minus_IZR, <- abs_IZR. apply IZR_le. exact Er. }
  assert (Hd0 : IZR den <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Hd).
  assert (Hb0 : b <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Pb).
  assert (Hk0 : k <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Pk).
  assert (Hpos : 0 < IZR den * (b * k)) by (apply Rmult_lt_0_compat; [exact Hd | apply Rmult_lt_0_compat; assumption]).
  assert (Eq : IZR (Limbs.v m0) * / (b * k) - / IZR den = X * / (IZR den * (b * k))).
  { unfold X. field. all: repeat split; assumption. }
  rewrite Eq.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq (/ (IZR den * (b * k)))) by (apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos).
  apply Rle_trans with (b * / (IZR den * (b * k))).
  - apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos | exact HX].
  - apply Req_le. field. all: repeat split; assumption.
Qed.

Lemma steps_check_sound dens f steps : forall j, (forall n, f n = / IZR (dens n)) ->
  steps_check dens j steps = true -> const_ok steps (cs_gen f j (length steps)).
Proof.
  induction steps as [ | [m0 e0] st IH]; intros j Hf C; simpl.
  - exact I.
  - simpl in C. rewrite !andb_true_iff in C. destruct C as [[Cs C2] Cr].
    apply Z.leb_le in C2.
    destruct (step_check_ok (dens j) m0 e0 Cs C2) as [Ok E].
    rewrite Hf. assert (Hd : 2 <= IZR (dens j)) by (change 2 with (IZR 2); apply IZR_le; exact C2).
    refine (conj (conj _ _) (conj E (conj Ok _))).
    + apply Rinv_0_lt_compat; lra.
    + rewrite <- Rinv_involutive with (r := 2) by lra. apply Rinv_le_contravar; lra.
    + exact (IH (S j) Hf Cr).
Qed.

Definition dens_sin (l : nat) : Z := (Z.of_nat (2 * l) * Z.of_nat (2 * l + 1))%Z.
Definition dens_cos (l : nat) : Z := (Z.of_nat (2 * l - 1) * Z.of_nat (2 * l))%Z.

Lemma f_sin_den n : f_sin n = / IZR (dens_sin n).
Proof. unfold f_sin, dens_sin. rewrite mult_IZR, <- !INR_IZR_INZ. reflexivity. Qed.

Lemma f_cos_den n : f_cos n = / IZR (dens_cos n).
Proof. unfold f_cos, dens_cos. rewrite mult_IZR, <- !INR_IZR_INZ. reflexivity. Qed.

Lemma sin_steps_check : steps_check dens_sin 1 asin_sin_steps = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cos_steps_check : steps_check dens_cos 1 asin_cos_steps = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sin_steps_len : length asin_sin_steps = 22%nat.
Proof. reflexivity. Qed.

Lemma cos_steps_len : length asin_cos_steps = 23%nat.
Proof. reflexivity. Qed.

Theorem sin_const_ok : const_ok asin_sin_steps (cs_gen f_sin 1 22).
Proof.
  rewrite <- sin_steps_len. exact (steps_check_sound dens_sin f_sin asin_sin_steps 1 f_sin_den sin_steps_check).
Qed.

Theorem cos_const_ok : const_ok asin_cos_steps (cs_gen f_cos 1 23).
Proof.
  rewrite <- cos_steps_len. exact (steps_check_sound dens_cos f_cos asin_cos_steps 1 f_cos_den cos_steps_check).
Qed.

(** The Horner series is [0.8]-Lipschitz in [s] on the accurate path's range. *)
Lemma ser_lip cs a b : Forall (fun c => 0 <= c <= / 2) cs -> 0 <= a <= 0.62 -> 0 <= b <= 0.62 ->
  Rabs (ser a cs - ser b cs) <= 0.8 * Rabs (a - b).
Proof.
  intros F Ha Hb. induction F as [ | c cs' Hc F IH]; simpl.
  - rewrite Rminus_diag_eq, Rabs_R0 by reflexivity. pose proof (Rabs_pos (a - b)). lra.
  - pose proof (ser_range cs' a F Ha) as Ra. pose proof (ser_range cs' b F Hb) as Rb.
    replace (1 - a * c * ser a cs' - (1 - b * c * ser b cs'))
      with (- (c * ((a - b) * ser a cs' + b * (ser a cs' - ser b cs')))) by ring.
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq c) by lra.
    apply Rle_trans with (c * (Rabs (a - b) + 0.62 * (0.8 * Rabs (a - b)))).
    + apply Rmult_le_compat_l; [lra | ].
      apply Rle_trans with (Rabs ((a - b) * ser a cs') + Rabs (b * (ser a cs' - ser b cs'))); [apply Rabs_triang | ].
      rewrite !Rabs_mult. rewrite (Rabs_pos_eq (ser a cs')) by lra. rewrite (Rabs_pos_eq b) by lra.
      pose proof (Rabs_pos (a - b)). pose proof (Rabs_pos (ser a cs' - ser b cs')).
      nra.
    + pose proof (Rabs_pos (a - b)). nra.
Qed.
