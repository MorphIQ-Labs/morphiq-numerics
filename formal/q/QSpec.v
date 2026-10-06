(** The arithmetic contract of Q128 and Q256, for any significand width [p]:
    a value is [(−1)^n · m · 2^e] with [m] normalized ([2^(p−1) <= m < 2^p])
    or zero. The operations are specified on integers here and their
    contracts proved in the reals; QTranscription files prove the Rust code
    computes these specifications. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core Digits.

Open Scope Z_scope.

Section Width.

Variable p : Z.
Hypothesis Hp : 2 <= p.

Definition normalized (m : Z) := 2 ^ (p - 1) <= m < 2 ^ p.

Definition val (n : bool) (m e : Z) : R :=
  F2R (Float radix2 (if n then - m else m) e).

Lemma val_abs n m e : 0 <= m -> Rabs (val n m e) = F2R (Float radix2 m e).
Proof.
  intros Hm. unfold val. rewrite <- F2R_Zabs. f_equal. f_equal. destruct n; lia.
Qed.

Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma IZR_pow2 k : 0 <= k -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. destruct k; [reflexivity | reflexivity | lia]. Qed.

(** Multiplication: the exact product of the significands, truncated toward
    zero to [p] bits. *)
Definition mul_m (ma mb : Z) : Z * Z :=
  let P := ma * mb in
  if 2 ^ (2 * p - 1) <=? P then (P / 2 ^ p, p) else (P / 2 ^ (p - 1), p - 1).

Theorem mul_contract ma mb ea eb :
  normalized ma -> normalized mb ->
  let '(m, k) := mul_m ma mb in
  normalized m /\
  (F2R (Float radix2 m (ea + eb + k)) <= F2R (Float radix2 (ma * mb) (ea + eb)))%R /\
  (F2R (Float radix2 (ma * mb) (ea + eb)) - F2R (Float radix2 m (ea + eb + k))
     <= bpow radix2 (1 - p) * F2R (Float radix2 (ma * mb) (ea + eb)))%R.
Proof.
  unfold normalized, mul_m. intros [A1 A2] [B1 B2].
  set (P := ma * mb).
  assert (Plo : 2 ^ (2 * p - 2) <= P).
  { replace (2 * p - 2) with ((p - 1) + (p - 1)) by ring. rewrite Z.pow_add_r by lia. unfold P. nia. }
  assert (Phi : P < 2 ^ (2 * p)).
  { replace (2 * p) with (p + p) by ring. rewrite Z.pow_add_r by lia. unfold P.
    pose proof (pow2_pos (p - 1) ltac:(lia)). nia. }
  (* The truncation by 2^k, for k = p or p − 1 with P >= 2^(k + p − 1). *)
  assert (Gen : forall k, 0 <= k -> 2 ^ (k + p - 1) <= P -> P < 2 ^ (k + p) ->
    normalized (P / 2 ^ k) /\
    (F2R (Float radix2 (P / 2 ^ k) (ea + eb + k)) <= F2R (Float radix2 P (ea + eb)))%R /\
    (F2R (Float radix2 P (ea + eb)) - F2R (Float radix2 (P / 2 ^ k) (ea + eb + k))
       <= bpow radix2 (1 - p) * F2R (Float radix2 P (ea + eb)))%R).
  { intros k Hk L U. pose proof (pow2_pos k Hk) as K.
    pose proof (Z.div_mod P (2 ^ k) ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound P (2 ^ k) K) as M.
    set (q := P / 2 ^ k) in *. set (r := P mod 2 ^ k) in *.
    assert (Ek : F2R (Float radix2 P (ea + eb)) = (IZR (2 ^ k * q + r) * bpow radix2 (ea + eb))%R)
      by (unfold F2R; simpl; rewrite <- D; reflexivity).
    assert (Eq : F2R (Float radix2 q (ea + eb + k)) = (IZR (2 ^ k * q) * bpow radix2 (ea + eb))%R).
    { unfold F2R; simpl. rewrite mult_IZR, IZR_pow2 by lia. rewrite bpow_plus. ring. }
    split; [ | split].
    - unfold normalized. split.
      + apply Z.div_le_lower_bound; [lia | ]. rewrite <- Z.pow_add_r by lia.
        replace (k + (p - 1)) with (k + p - 1) by ring. lia.
      + apply Z.div_lt_upper_bound; [lia | ]. rewrite <- Z.pow_add_r by lia.
        replace (k + p) with (k + p) by ring. lia.
    - rewrite Ek, Eq. apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia].
    - rewrite Ek, Eq. pose proof (bpow_gt_0 radix2 (ea + eb)) as Pe.
      rewrite <- Rmult_minus_distr_r, <- minus_IZR.
      replace (2 ^ k * q + r - 2 ^ k * q) with r by ring.
      rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [lra | ].
      (* r < 2^k <= 2^(1−p)·P *)
      assert (Hr : (IZR r <= IZR (2 ^ k))%R) by (apply IZR_le; lia).
      apply Rle_trans with (1 := Hr).
      rewrite IZR_pow2 by lia. rewrite <- D.
      replace k with ((1 - p) + (k + p - 1)) at 1 by ring. rewrite bpow_plus.
      apply Rmult_le_compat_l; [apply bpow_ge_0 | ].
      rewrite <- IZR_pow2 by lia. apply IZR_le. exact L. }
  destruct (Z.leb_spec (2 ^ (2 * p - 1)) P) as [H | H].
  - apply Gen; [lia | | ]; [replace (p + p - 1) with (2 * p - 1) by ring; exact H | replace (p + p) with (2 * p) by ring; exact Phi].
  - apply Gen; [lia | | ].
    + replace (p - 1 + p - 1) with (2 * p - 2) by ring. exact Plo.
    + replace (p - 1 + p) with (2 * p - 1) by ring. lia.
Qed.

(** Normalization: [m·2^e] with the significand shifted left until its top bit
    is bit [p − 1]; zero stays zero. *)
Definition norm (m e : Z) : Z * Z :=
  if m =? 0 then (0, 0) else
  let s := p - Zdigits radix2 m in (m * 2 ^ s, e - s).

Theorem norm_ok m e : 0 <= m < 2 ^ p ->
  let '(m', e') := norm m e in
  (m = 0 /\ m' = 0 \/ normalized m') /\ F2R (Float radix2 m' e') = F2R (Float radix2 m e).
Proof.
  intros Hm. unfold norm. destruct (Z.eqb_spec m 0) as [-> | Hz].
  - split; [left; lia | ]. unfold F2R; simpl. ring.
  - pose proof (Zdigits_correct radix2 m) as D. rewrite Z.abs_eq in D by lia.
    set (d := Zdigits radix2 m) in *.
    change (Zpower radix2 (d - 1)) with (2 ^ (d - 1)) in D.
    change (Zpower radix2 d) with (2 ^ d) in D.
    assert (Dp : 1 <= d <= p).
    { split.
      - destruct (Z_lt_le_dec d 1) as [L | L]; [ | lia]. exfalso.
        assert (2 ^ d <= 1) by (destruct (Z.eq_dec d 0) as [-> | ]; [reflexivity | rewrite Z.pow_neg_r by lia; lia]).
        lia.
      - destruct (Z_le_gt_dec d p) as [L | L]; [exact L | ]. exfalso.
        assert (2 ^ p <= 2 ^ (d - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
    split.
    + right. unfold normalized.
      replace (2 ^ (p - 1)) with (2 ^ (d - 1) * 2 ^ (p - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
      replace (2 ^ p) with (2 ^ d * 2 ^ (p - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
      pose proof (pow2_pos (p - d) ltac:(lia)). nia.
    + unfold F2R; simpl. rewrite mult_IZR, IZR_pow2 by lia.
      rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

(** Addition of [a] and [b] with [|a| >= |b|], both normalized: [b]'s
    significand truncated to [a]'s grid, then added or subtracted. *)
Definition add_m (same : bool) (ma ea mb eb : Z) : Z * Z :=
  let aligned := mb / 2 ^ (ea - eb) in
  if same then
    let s := ma + aligned in
    if 2 ^ p <=? s then (s / 2, ea + 1) else (s, ea)
  else norm (ma - aligned) ea.

Theorem add_contract (same : bool) ma ea mb eb :
  normalized ma -> normalized mb ->
  (F2R (Float radix2 mb eb) <= F2R (Float radix2 ma ea))%R ->
  let '(m, e) := add_m same ma ea mb eb in
  (m = 0 \/ normalized m) /\
  (Rabs (F2R (Float radix2 m e)
         - (F2R (Float radix2 ma ea) + (if same then 1 else -1) * F2R (Float radix2 mb eb)))
     <= bpow radix2 (2 - p) * F2R (Float radix2 ma ea))%R.
Proof.
  unfold normalized. intros [A1 A2] [B1 B2] Hab.
  (* ea >= eb: otherwise |b| >= 2^(eb + p − 1) > |a|. *)
  assert (Hd : eb <= ea).
  { destruct (Z_le_gt_dec eb ea) as [ | G]; [assumption | exfalso].
    assert (F2R (Float radix2 ma ea) < F2R (Float radix2 mb eb))%R; [ | lra].
    unfold F2R; simpl.
    apply Rlt_le_trans with (bpow radix2 (p + ea)).
    - rewrite (bpow_plus radix2 p ea), <- (IZR_pow2 p) by lia. apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; lia].
    - replace (p + ea) with ((p - 1) + (ea + 1)) by ring. rewrite (bpow_plus radix2 (p - 1)), <- (IZR_pow2 (p - 1)) by lia.
      apply Rmult_le_compat; [apply IZR_le; pose proof (pow2_pos (p - 1) ltac:(lia)); lia | apply bpow_ge_0 | apply IZR_le; lia | apply bpow_le; lia]. }
  set (d := ea - eb).
  pose proof (pow2_pos d ltac:(lia)) as K.
  pose proof (Z.div_mod mb (2 ^ d) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound mb (2 ^ d) K) as M.
  set (q := mb / 2 ^ d) in *. set (r := mb mod 2 ^ d) in *.
  assert (Qb : 0 <= q < 2 ^ p).
  { split; [apply Z.div_pos; lia | ]. apply Z.le_lt_trans with mb; [apply Z.div_le_upper_bound; nia | lia]. }
  (* b = q·2^ea + r·2^eb with 0 <= r·2^eb < 2^ea. *)
  assert (Bv : F2R (Float radix2 mb eb) = (IZR q * bpow radix2 ea + IZR r * bpow radix2 eb)%R).
  { unfold F2R; simpl. rewrite D, plus_IZR, mult_IZR, IZR_pow2 by lia.
    replace ea with (d + eb) at 1 by (unfold d; ring). rewrite bpow_plus. ring. }
  assert (Rb : (0 <= IZR r * bpow radix2 eb < bpow radix2 ea)%R).
  { split; [apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0] | ].
    replace ea with (d + eb) by (unfold d; ring). rewrite (bpow_plus radix2 d eb), <- (IZR_pow2 d) by lia.
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; lia]. }
  assert (Av : (bpow radix2 (ea + 1) <= bpow radix2 (2 - p) * F2R (Float radix2 ma ea))%R).
  { unfold F2R; simpl. replace (ea + 1) with ((2 - p) + ((p - 1) + ea)) by ring.
    rewrite !bpow_plus, <- (IZR_pow2 (p - 1)) by lia.
    apply Rmult_le_compat_l; [apply bpow_ge_0 | ].
    apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia]. }
  pose proof (bpow_gt_0 radix2 ea) as Pe.
  unfold add_m. fold d. fold q. destruct same.
  - (* the same sign *)
    destruct (Z.leb_spec (2 ^ p) (ma + q)) as [C | C].
    + pose proof (Z.div_mod (ma + q) 2 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (ma + q) 2 ltac:(lia)) as M2.
      split.
      * right. split.
        -- apply Z.div_le_lower_bound; [lia | ]. rewrite <- (Z.pow_succ_r 2 (p - 1)) by lia.
           replace (Z.succ (p - 1)) with p by ring. lia.
        -- apply Z.div_lt_upper_bound; [lia | ].
           assert (2 * 2 ^ p = 2 ^ p + 2 ^ p) by ring. lia.
      * assert (Ev : F2R (Float radix2 ((ma + q) / 2) (ea + 1))
                     = (IZR (ma + q) * bpow radix2 ea - IZR ((ma + q) mod 2) * bpow radix2 ea)%R).
        { unfold F2R; simpl. rewrite bpow_plus. change (bpow radix2 1) with 2%R.
          rewrite <- Rmult_minus_distr_r, <- minus_IZR.
          replace (ma + q - (ma + q) mod 2) with (2 * ((ma + q) / 2)) by lia.
          rewrite mult_IZR. ring. }
        rewrite Ev, Bv. unfold F2R; simpl. rewrite plus_IZR.
        assert (Rm : (0 <= IZR ((ma + q) mod 2) <= 1)%R) by (split; apply IZR_le; lia).
        rewrite Rabs_left1; [ | nra].
        apply Rle_trans with (2 := Av). rewrite bpow_plus. change (bpow radix2 1) with 2%R. nra.
    + split.
      * right. split; [ | lia]. pose proof (Z.div_pos mb (2 ^ d)); lia.
      * rewrite Bv. unfold F2R; simpl. rewrite plus_IZR.
        rewrite Rabs_left1 by nra.
        apply Rle_trans with (2 := Av). rewrite bpow_plus. change (bpow radix2 1) with 2%R. nra.
  - (* opposite signs: the difference is exact on a's grid *)
    (* q·2^ea <= |b| <= |a| = ma·2^ea *)
    assert (Qm : q <= ma).
    { apply le_IZR. apply Rmult_le_reg_r with (bpow radix2 ea); [exact Pe | ].
      apply Rle_trans with (F2R (Float radix2 mb eb)); [rewrite Bv; nra | exact Hab]. }
    assert (Mq : 0 <= ma - q < 2 ^ p) by lia.
    pose proof (norm_ok (ma - q) ea Mq) as N. destruct (norm (ma - q) ea) as [m e].
    destruct N as [Nm Nv]. split; [destruct Nm as [[_ ->] | Nn]; [left; reflexivity | right; exact Nn] | ].
    rewrite Nv, Bv. unfold F2R; simpl. rewrite minus_IZR.
    rewrite Rabs_pos_eq by nra.
    apply Rle_trans with (2 := Av). rewrite bpow_plus. change (bpow radix2 1) with 2%R. nra.
Qed.

(** The signed form: [a] the larger in magnitude, the result carries [a]'s sign. *)
Theorem add_signed nb mb eb ns ms es :
  normalized mb -> normalized ms ->
  (F2R (Float radix2 ms es) <= F2R (Float radix2 mb eb))%R ->
  let '(m, e) := add_m (Bool.eqb nb ns) mb eb ms es in
  (m = 0 \/ normalized m) /\
  (Rabs (val nb m e - (val nb mb eb + val ns ms es))
     <= bpow radix2 (2 - p) * F2R (Float radix2 mb eb))%R.
Proof.
  intros Hb Hs Hle.
  pose proof (add_contract (Bool.eqb nb ns) mb eb ms es Hb Hs Hle) as AC.
  destruct (add_m (Bool.eqb nb ns) mb eb ms es) as [m e]. destruct AC as [AM AE].
  split; [exact AM | ].
  assert (V : forall n k x, val n k x = if n then (- F2R (Float radix2 k x))%R else F2R (Float radix2 k x))
    by (intros n k x; unfold val; destruct n; [rewrite F2R_Zopp | ]; reflexivity).
  rewrite !V. destruct nb, ns; simpl in AE;
    match goal with
    | |- (Rabs ?x <= _)%R => idtac
    end;
    [ replace (- F2R (Float radix2 m e) - (- F2R (Float radix2 mb eb) + - F2R (Float radix2 ms es)))%R
        with (- (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + 1 * F2R (Float radix2 ms es))))%R by ring
    | replace (- F2R (Float radix2 m e) - (- F2R (Float radix2 mb eb) + F2R (Float radix2 ms es)))%R
        with (- (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + -1 * F2R (Float radix2 ms es))))%R by ring
    | replace (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + - F2R (Float radix2 ms es)))%R
        with (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + -1 * F2R (Float radix2 ms es)))%R by ring
    | replace (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + F2R (Float radix2 ms es)))%R
        with (F2R (Float radix2 m e) - (F2R (Float radix2 mb eb) + 1 * F2R (Float radix2 ms es)))%R by ring ];
    rewrite ?Rabs_Ropp; exact AE.
Qed.

End Width.
