(** The reflective checks of [ln_1p]'s stage tables (docs/ln.md, section 7):
    each table is checked by one boolean computation ([vm_compute]), and
    [rt_check_ok] and [l_check_ok] state what a passing check establishes.

    Values are handled exactly, as dyadic numbers [m·2^e] decoded from the
    binary64 encodings; [ln R[i]] is enclosed by [LnCheck.ln_bounds]. *)

From Coq Require Import ZArith Reals List Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid.
Require Import LnCheck.
Import ListNotations.

Open Scope R_scope.

(** * Dyadic numbers *)

Definition dy : Type := (Z * Z)%type.
Definition dval (x : dy) : R := IZR (fst x) * bpow radix2 (snd x).

Definition dadd (a b : dy) : dy :=
  let t := Z.min (snd a) (snd b) in ((fst a * 2 ^ (snd a - t) + fst b * 2 ^ (snd b - t))%Z, t).
Definition dneg (a : dy) : dy := ((- fst a)%Z, snd a).
Definition dsub (a b : dy) : dy := dadd a (dneg b).
Definition dmul (a b : dy) : dy := ((fst a * fst b)%Z, (snd a + snd b)%Z).
Definition dabs (a : dy) : dy := (Z.abs (fst a), snd a).
Definition dle (a b : dy) : bool :=
  let t := Z.min (snd a) (snd b) in (fst a * 2 ^ (snd a - t) <=? fst b * 2 ^ (snd b - t))%Z.
Definition dmax (a b : dy) : dy := if dle a b then b else a.

Lemma IZR_pow2 k : (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. change (2 ^ k)%Z with (Zpower radix2 k). apply IZR_Zpower, H. Qed.

Lemma shift_val m e t : (t <= e)%Z -> IZR (m * 2 ^ (e - t)) * bpow radix2 t = IZR m * bpow radix2 e.
Proof.
  intros H. rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- bpow_plus.
  f_equal. f_equal. ring.
Qed.

Lemma dval_add a b : dval (dadd a b) = dval a + dval b.
Proof.
  destruct a as [ma ea], b as [mb eb]. unfold dadd, dval. cbn [fst snd].
  rewrite plus_IZR, Rmult_plus_distr_r.
  rewrite <- (shift_val ma ea (Z.min ea eb)) by lia. rewrite <- (shift_val mb eb (Z.min ea eb)) by lia.
  rewrite !mult_IZR. ring.
Qed.

Lemma dval_neg a : dval (dneg a) = - dval a.
Proof. destruct a. unfold dneg, dval. cbn. rewrite opp_IZR. ring. Qed.

Lemma dval_sub a b : dval (dsub a b) = dval a - dval b.
Proof. unfold dsub. rewrite dval_add, dval_neg. ring. Qed.

Lemma dval_mul a b : dval (dmul a b) = dval a * dval b.
Proof. destruct a, b. unfold dmul, dval. cbn. rewrite mult_IZR, bpow_plus. ring. Qed.

Lemma dval_abs a : dval (dabs a) = Rabs (dval a).
Proof.
  destruct a as [m e]. unfold dabs, dval. cbn. rewrite Rabs_mult, Rabs_Zabs.
  rewrite (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0. reflexivity.
Qed.

Lemma dle_ok a b : dle a b = true -> dval a <= dval b.
Proof.
  destruct a as [ma ea], b as [mb eb]. unfold dle, dval. cbn [fst snd]. intros H. apply Z.leb_le in H.
  apply IZR_le in H. rewrite <- (shift_val ma ea (Z.min ea eb)) by lia. rewrite <- (shift_val mb eb (Z.min ea eb)) by lia.
  apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H].
Qed.

Lemma dmax_ok a b : dval a <= dval (dmax a b) /\ dval b <= dval (dmax a b).
Proof.
  unfold dmax. destruct (dle a b) eqn:E.
  - split; [apply dle_ok, E | lra].
  - split; [lra | ]. unfold dle in E. destruct a as [ma ea], b as [mb eb]. unfold dval. cbn [fst snd] in *.
    apply Z.leb_gt in E. apply IZR_lt in E.
    rewrite <- (shift_val ma ea (Z.min ea eb)) by lia. rewrite <- (shift_val mb eb (Z.min ea eb)) by lia.
    apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
Qed.

(** * Decoding *)

Definition dec (n : Z) : option dy :=
  match binary_float_of_bits_aux 52 11 n with
  | F754_finite s m e => Some (cond_Zopp s (Zpos m), e)
  | F754_zero _ => Some (0%Z, 0%Z)
  | _ => None
  end.

Lemma dec_ok n d : dec n = Some d -> finite (b64_of_bits n) /\ B (b64_of_bits n) = dval d.
Proof.
  unfold dec, b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, B2R_FF2B.
  destruct (binary_float_of_bits_aux 52 11 n) as [s | s | s pl | s m e]; intros H; try discriminate;
    injection H as <-.
  - split; [reflexivity | unfold dval; simpl; ring].
  - split; reflexivity.
Qed.

(** [ln(m·2^e)] for [m > 0], enclosed at scale [2^-k] with [n] terms. *)
Definition lnb (d : dy) (k : Z) (n : nat) : Z * Z :=
  if (snd d <? 0)%Z then ln_bounds (fst d) (2 ^ (- snd d)) k n else ln_bounds (fst d * 2 ^ snd d) 1 k n.

Lemma lnb_ok d k n : (0 < fst d)%Z -> (0 <= k)%Z ->
  dval (fst (lnb d k n), (- k)%Z) <= ln (dval d) <= dval (snd (lnb d k n), (- k)%Z).
Proof.
  destruct d as [m e]. unfold lnb, dval. cbn [fst snd]. intros Hm Hk.
  destruct (Z.ltb_spec e 0) as [L | L].
  - replace (IZR m * bpow radix2 e) with (IZR m / IZR (2 ^ (- e))).
    + apply ln_bounds_ok; [exact Hm | apply Z.pow_pos_nonneg; lia | exact Hk].
    + rewrite IZR_pow2 by lia. rewrite bpow_opp. unfold Rdiv. rewrite Rinv_involutive by (apply Rgt_not_eq, bpow_gt_0). reflexivity.
  - replace (IZR m * bpow radix2 e) with (IZR (m * 2 ^ e) / IZR 1).
    + apply ln_bounds_ok; [apply Z.mul_pos_pos; [exact Hm | apply Z.pow_pos_nonneg; lia] | lia | exact Hk].
    + rewrite mult_IZR, IZR_pow2 by lia. unfold Rdiv. rewrite Rinv_1, Rmult_1_r. reflexivity.
Qed.

(** * The bounds the generator checked *)

Record bounds : Type := {
  b_t_err : dy;   (** |-ln R[i] - TH - TL| *)
  b_tl_max : dy;  (** |TL| *)
  b_th_max : dy;  (** |TH| *)
  b_s_min : dy;   (** |TH| - max |y R - 1| over the interval, where R[i] != 1 *)
  b_l_err : dy;   (** |ln 2 - L1 - L0| *)
  b_l0_max : dy   (** |L0| *)
}.

(** * The reciprocals and [-ln R[i]] *)

Definition st_off : Z := 4604543590893355008.   (* bits(0x1.6ap-1) *)
Definition one_bits : Z := 4607182418800017408.  (* bits(1) *)
Definition width : Z := 8796093022208.           (* 2^43 encodings per interval *)
Definition z_max : dy := (1%Z, (-9)%Z).

Definition near_b (i : Z) : bool := (i =? 298)%Z || (i =? 299)%Z || (i =? 300)%Z.

(** On the [2^-43] grid. *)
Definition grid43 (d : dy) : bool := (- 43 <=? snd d)%Z || (fst d mod 2 ^ (- 43 - snd d) =? 0)%Z.

(** The largest [|y·R − 1|] at the interval's end encodings. *)
Definition zbound (i : Z) (r : Z) : option dy :=
  match dec r, dec (st_off + i * width), dec (st_off + (i + 1) * width - 1) with
  | Some R, Some ya, Some yb =>
      Some (dmax (dabs (dsub (dmul ya R) (1%Z, 0%Z))) (dabs (dsub (dmul yb R) (1%Z, 0%Z))))
  | _, _, _ => None
  end.

Definition rt_entry (bd : bounds) (i : Z) (r : Z) (t : Z * Z) : bool :=
  match dec r, zbound i r, dec (fst t), dec (snd t) with
  | Some R, Some zi, Some th, Some tl =>
      (0 <? fst R)%Z && (0 <? r)%Z && (r <? 2 ^ 63)%Z && (r mod 2 ^ 43 =? 0)%Z && (1022 <=? r / 2 ^ 52)%Z && (r / 2 ^ 52 <=? 1023)%Z
      && Bool.eqb (r =? one_bits)%Z (near_b i)
      && dle zi z_max
      && grid43 th && dle (dabs tl) (b_tl_max bd) && dle (dabs th) (b_th_max bd)
      && (let '(lo, hi) := lnb R 110 24 in
          dle (dadd (dadd th tl) (hi, (-110)%Z)) (b_t_err bd)
          && dle (dneg (b_t_err bd)) (dadd (dadd th tl) (lo, (-110)%Z)))
      && (if near_b i then (fst t =? 0)%Z && (snd t =? 0)%Z else dle (dadd zi (b_s_min bd)) (dabs th))
  | _, _, _, _ => false
  end.

Fixpoint rt_from (bd : bounds) (i : Z) (rs : list Z) (ts : list (Z * Z)) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' => rt_entry bd i r t && rt_from bd (i + 1) rs' ts'
  | _, _ => false
  end.

Definition rt_check (bd : bounds) (rs : list Z) (ts : list (Z * Z)) : bool :=
  (Z.of_nat (length rs) =? 512)%Z && rt_from bd 0 rs ts.

(** What a passing check gives about entry [i]: [R = B r], [TH], [TL], and
    the interval's end values [ya], [yb]. *)
Definition rt_entry_ok (bd : bounds) (i : Z) (r : Z) (t : Z * Z) : Prop :=
  let R := B (b64_of_bits r) in
  let th := B (b64_of_bits (fst t)) in
  let tl := B (b64_of_bits (snd t)) in
  let ya := B (b64_of_bits (st_off + i * width)) in
  let yb := B (b64_of_bits (st_off + (i + 1) * width - 1)) in
  finite (b64_of_bits r) /\ finite (b64_of_bits (fst t)) /\ finite (b64_of_bits (snd t)) /\
  (0 < r < 2 ^ 63)%Z /\ (r mod 2 ^ 43 = 0)%Z /\ (1022 <= r / 2 ^ 52 <= 1023)%Z /\
  ((r = one_bits)%Z <-> near_b i = true) /\
  (exists zi, zi <= / 2 ^ 9 /\ Rabs (ya * R - 1) <= zi /\ Rabs (yb * R - 1) <= zi /\
     (near_b i = true -> fst t = 0%Z /\ snd t = 0%Z) /\
     (near_b i = false -> zi + dval (b_s_min bd) <= Rabs th)) /\
  on_grid (-43) th /\ Rabs tl <= dval (b_tl_max bd) /\ Rabs th <= dval (b_th_max bd) /\
  Rabs (th + tl + ln R) <= dval (b_t_err bd).

Lemma zmax_val : dval z_max = / 2 ^ 9.
Proof.
  unfold dval, z_max. cbn [fst snd]. rewrite Rmult_1_l. change (-9)%Z with (- Z.of_nat 9)%Z.
  rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity.
Qed.

Lemma grid43_ok d : grid43 d = true -> on_grid (-43) (dval d).
Proof.
  destruct d as [m e]. unfold grid43, dval. cbn [fst snd]. intros H. apply orb_true_iff in H as [H | H].
  - apply Z.leb_le in H. exists (m * 2 ^ (e + 43))%Z. rewrite mult_IZR, IZR_pow2 by lia.
    rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
  - apply Z.eqb_eq in H. destruct (Z.leb_spec (- 43) e) as [L | L].
    + exists (m * 2 ^ (e + 43))%Z. rewrite mult_IZR, IZR_pow2 by lia.
      rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
    + exists (m / 2 ^ (- 43 - e))%Z.
      assert (P : (0 < 2 ^ (- 43 - e))%Z) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.div_mod m (2 ^ (- 43 - e)) ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
      rewrite D at 1. rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus.
      rewrite Rmult_comm. f_equal. f_equal. ring.
Qed.

Theorem rt_entry_sound bd i r t : rt_entry bd i r t = true -> rt_entry_ok bd i r t.
Proof.
  unfold rt_entry, rt_entry_ok, zbound.
  destruct (dec r) as [R | ] eqn:DR; [ | discriminate].
  destruct (dec (st_off + i * width)) as [ya | ] eqn:DA; [ | discriminate].
  destruct (dec (st_off + (i + 1) * width - 1)) as [yb | ] eqn:DB; [ | discriminate].
  destruct (dec (fst t)) as [th | ] eqn:DH; [ | discriminate].
  destruct (dec (snd t)) as [tl | ] eqn:DL; [ | discriminate].
  destruct (lnb R 110 24) as [lo hi] eqn:LN.
  intros H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[[[[[[Rp H0] H1] H2] H3] H4] Hn] Hz] Hg] Htl] Hth] [Hhi Hlo]] Hs].
  apply Z.ltb_lt in Rp. apply Z.ltb_lt in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (dec_ok _ _ DR) as [FR VR]. destruct (dec_ok _ _ DA) as [FA VA]. destruct (dec_ok _ _ DB) as [FB VB].
  destruct (dec_ok _ _ DH) as [FH VH]. destruct (dec_ok _ _ DL) as [FL VL].
  cbv zeta. rewrite VR, VA, VB, VH, VL.
  split; [exact FR | ]. split; [exact FH | ]. split; [exact FL | ].
  split; [lia | ]. split; [exact H2 | ]. split; [lia | ].
  split.
  { split; intros E.
    - apply Bool.eqb_prop in Hn. rewrite <- Hn. apply Z.eqb_eq. exact E.
    - apply Bool.eqb_prop in Hn. rewrite E in Hn. apply Z.eqb_eq. exact Hn. }
  split.
  { set (zi := dmax (dabs (dsub (dmul ya R) (1%Z, 0%Z))) (dabs (dsub (dmul yb R) (1%Z, 0%Z)))) in *.
    exists (dval zi). destruct (dmax_ok (dabs (dsub (dmul ya R) (1%Z, 0%Z))) (dabs (dsub (dmul yb R) (1%Z, 0%Z))))
      as [M1 M2]. fold zi in M1, M2.
    rewrite dval_abs, dval_sub, dval_mul in M1, M2.
    assert (One : dval (1%Z, 0%Z) = 1) by (unfold dval; simpl; ring). rewrite One in M1, M2.
    split; [rewrite <- zmax_val; apply dle_ok, Hz | ].
    split; [exact M1 | ]. split; [exact M2 | ].
    split.
    - intros Nb. rewrite Nb in Hs. apply andb_true_iff in Hs as [S1 S2].
      apply Z.eqb_eq in S1. apply Z.eqb_eq in S2. split; assumption.
    - intros Nb. rewrite Nb in Hs. apply dle_ok in Hs. rewrite dval_add, dval_abs in Hs. exact Hs. }
  split; [apply grid43_ok, Hg | ].
  split; [rewrite <- dval_abs; apply dle_ok, Htl | ].
  split; [rewrite <- dval_abs; apply dle_ok, Hth | ].
  apply dle_ok in Hhi. apply dle_ok in Hlo. rewrite !dval_add in Hhi, Hlo. rewrite dval_neg in Hlo.
  destruct (lnb_ok R 110 24 Rp ltac:(lia)) as [L1 L2]. rewrite LN in L1, L2. cbn [fst snd Z.opp] in L1, L2.
  apply Rabs_le. lra.
Qed.

Lemma rt_from_ok bd rs : forall ts i0 k, rt_from bd i0 rs ts = true -> (k < length rs)%nat ->
  rt_entry bd (i0 + Z.of_nat k) (nth k rs 0%Z) (nth k ts (0%Z, 0%Z)) = true.
Proof.
  induction rs as [| r rs IH]; intros ts i0 k H Hk; [simpl in Hk; lia | ].
  destruct ts as [| t ts]; [discriminate | ].
  simpl in H. apply andb_true_iff in H as [H1 H2].
  destruct k as [| k].
  - simpl. rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (i0 + Z.of_nat (S k))%Z with (i0 + 1 + Z.of_nat k)%Z by lia.
    apply IH; [exact H2 | simpl in Hk; lia].
Qed.

Theorem rt_check_ok bd rs ts i : rt_check bd rs ts = true -> (i < 512)%nat ->
  rt_entry_ok bd (Z.of_nat i) (nth i rs 0%Z) (nth i ts (0%Z, 0%Z)).
Proof.
  unfold rt_check. intros H Hi. apply andb_true_iff in H as [Hl H]. apply Z.eqb_eq in Hl.
  apply rt_entry_sound. pose proof (rt_from_ok bd rs ts 0 i H ltac:(lia)) as E.
  rewrite Z.add_0_l in E. exact E.
Qed.

(** * [ln 2 = L1 + L0] and [E·ln 2] for stage H *)

Definition el_entry (L1 L0 : dy) (k : Z) (e : Z * Z) : bool :=
  match dec (fst e), dec (snd e) with
  | Some eh, Some el =>
      let x := dmul ((k - 64)%Z, 0%Z) L1 in
      let y := dmul ((k - 64)%Z, 0%Z) L0 in
      dle eh x && dle x eh && dle (dmul (1%Z, 53%Z) (dabs (dsub el y))) (dabs y)
  | _, _ => false
  end.

Fixpoint el_from (L1 L0 : dy) (k : Z) (es : list (Z * Z)) : bool :=
  match es with
  | [] => true
  | e :: es' => el_entry L1 L0 k e && el_from L1 L0 (k + 1) es'
  end.

Definition l_check (bd : bounds) (l1 l0 : Z) (es : list (Z * Z)) : bool :=
  match dec l1, dec l0 with
  | Some L1, Some L0 =>
      grid43 L1 && (0 <? fst L1)%Z && dle L1 (1%Z, 0%Z) && dle (dabs L0) (b_l0_max bd)
      && (let '(lo, hi) := ln_bounds 2 1 110 60 in
          dle (dsub (dadd L1 L0) (lo, (-110)%Z)) (b_l_err bd)
          && dle (dneg (b_l_err bd)) (dsub (dadd L1 L0) (hi, (-110)%Z)))
      && (Z.of_nat (length es) =? 128)%Z && el_from L1 L0 0 es
  | _, _ => false
  end.

Definition l_ok (bd : bounds) (l1 l0 : Z) (es : list (Z * Z)) : Prop :=
  let L1 := B (b64_of_bits l1) in
  let L0 := B (b64_of_bits l0) in
  finite (b64_of_bits l1) /\ finite (b64_of_bits l0) /\
  on_grid (-43) L1 /\ 0 < L1 <= 1 /\ Rabs L0 <= dval (b_l0_max bd) /\
  Rabs (L1 + L0 - ln 2) <= dval (b_l_err bd) /\
  forall k, (k < 128)%nat ->
    let eh := b64_of_bits (fst (nth k es (0%Z, 0%Z))) in
    let el := b64_of_bits (snd (nth k es (0%Z, 0%Z))) in
    finite eh /\ finite el /\ B eh = (INR k - 64) * L1 /\
    Rabs (B el - (INR k - 64) * L0) <= / 2 ^ 53 * Rabs ((INR k - 64) * L0).

Lemma el_from_ok L1 L0 es : forall k0 k, el_from L1 L0 k0 es = true -> (k < length es)%nat ->
  el_entry L1 L0 (k0 + Z.of_nat k) (nth k es (0%Z, 0%Z)) = true.
Proof.
  induction es as [| e es IH]; intros k0 k H Hk; [simpl in Hk; lia | ].
  simpl in H. apply andb_true_iff in H as [H1 H2].
  destruct k as [| k].
  - simpl. rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (k0 + Z.of_nat (S k))%Z with (k0 + 1 + Z.of_nat k)%Z by lia.
    apply IH; [exact H2 | simpl in Hk; lia].
Qed.

Theorem l_check_ok bd l1 l0 es : l_check bd l1 l0 es = true -> l_ok bd l1 l0 es.
Proof.
  unfold l_check, l_ok.
  destruct (dec l1) as [L1 | ] eqn:D1; [ | discriminate].
  destruct (dec l0) as [L0 | ] eqn:D0; [ | discriminate].
  destruct (ln_bounds 2 1 110 60) as [lo hi] eqn:LN.
  intros H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[Hg Hp] H1] H0] [Hlo Hhi]] Hn] He].
  destruct (dec_ok _ _ D1) as [F1 V1]. destruct (dec_ok _ _ D0) as [F0 V0].
  rewrite V1, V0. apply Z.ltb_lt in Hp. apply Z.eqb_eq in Hn.
  pose proof (ln_bounds_ok 2 1 110 60 ltac:(lia) ltac:(lia) ltac:(lia)) as LB. rewrite LN in LB. cbn [fst snd] in LB.
  replace (IZR 2 / IZR 1) with 2 in LB by (unfold Rdiv; rewrite Rinv_1; ring).
  assert (One : dval (1%Z, 0%Z) = 1) by (unfold dval; simpl; ring).
  split; [exact F1 | split; [exact F0 | split; [apply grid43_ok, Hg | split; [split | split; [ | split]]]]].
  - destruct L1 as [m e]. unfold dval. cbn [fst snd] in *. apply Rmult_lt_0_compat; [apply IZR_lt; exact Hp | apply bpow_gt_0].
  - rewrite <- One. apply dle_ok, H1.
  - rewrite <- dval_abs. apply dle_ok, H0.
  - apply dle_ok in Hlo. apply dle_ok in Hhi. rewrite dval_sub, dval_add in Hlo, Hhi. rewrite dval_neg in Hhi.
    assert (Dl : dval (lo, (-110)%Z) = IZR lo * bpow radix2 (- 110)) by reflexivity.
    assert (Dh : dval (hi, (-110)%Z) = IZR hi * bpow radix2 (- 110)) by reflexivity.
    rewrite Dl in Hlo. rewrite Dh in Hhi. cbn [Z.opp] in LB.
    apply Rabs_le. lra.
  - intros k Hk. pose proof (el_from_ok L1 L0 es 0 k He ltac:(lia)) as E. rewrite Z.add_0_l in E.
    unfold el_entry in E.
    destruct (dec (fst (nth k es (0%Z, 0%Z)))) as [eh | ] eqn:DH; [ | discriminate].
    destruct (dec (snd (nth k es (0%Z, 0%Z)))) as [el | ] eqn:DL; [ | discriminate].
    repeat rewrite andb_true_iff in E. destruct E as [[E1 E2] E3].
    destruct (dec_ok _ _ DH) as [FH VH]. destruct (dec_ok _ _ DL) as [FL VL].
    assert (Kv : dval ((Z.of_nat k - 64)%Z, 0%Z) = INR k - 64).
    { unfold dval. cbn [fst snd]. rewrite minus_IZR, INR_IZR_INZ. simpl. ring. }
    apply dle_ok in E1. apply dle_ok in E2. apply dle_ok in E3.
    rewrite dval_mul in E1, E2. rewrite dval_mul, dval_abs, dval_sub, dval_abs, dval_mul in E3.
    rewrite Kv in E1, E2, E3.
    assert (T53 : dval (1%Z, 53%Z) = 2 ^ 53).
    { unfold dval. cbn [fst snd]. rewrite Rmult_1_l. change 53%Z with (Z.of_nat 53).
      rewrite bpow_powerRZ, <- pow_powerRZ. reflexivity. }
    rewrite T53 in E3.
    split; [exact FH | split; [exact FL | split]].
    + rewrite VH. lra.
    + rewrite VL. apply Rmult_le_reg_l with (2 ^ 53); [apply pow_lt; lra | ].
      rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l by (apply pow_nonzero; lra). exact E3.
Qed.
