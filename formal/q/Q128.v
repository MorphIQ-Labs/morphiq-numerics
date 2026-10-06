(** crates/morphiq-numerics/src/q128.rs, transcribed on its fields: [m] a
    u128 as an integer in [[0, 2^128)], each operation with the u128 semantics
    of its Rust counterpart (shifts, masks, wrapping adds, leading_zeros). Each
    is proved to compute the width-128 specification of QSpec.v and QRound.v. *)

From Coq Require Import Bool ZArith Lia Psatz.
From Flocq Require Import Core Digits.
Require Import QSpec QRound Q128Mul.

Open Scope Z_scope.

Record q128 := Q { neg : bool; m : Z; e : Z }.

Definition W := 2 ^ 128.
Definition TOP := 2 ^ 127.
Definition zero := Q false 0 0.

(** u128::leading_zeros of a nonzero [m]. *)
Definition leading_zeros (m : Z) := 128 - Zdigits radix2 m.

Definition new (n : bool) (m e : Z) : q128 :=
  if m =? 0 then zero else
  let s := leading_zeros m in Q n ((Z.shiftl m s) mod W) (e - s).

Theorem new_ok n m0 e0 : 0 <= m0 < W ->
  let r := new n m0 e0 in (m r, e r) = norm 128 m0 e0.
Proof.
  intros H. unfold new, norm. destruct (Z.eqb_spec m0 0) as [-> | Hz]; [reflexivity | ].
  unfold leading_zeros. cbn [m e]. f_equal.
  rewrite Z.shiftl_mul_pow2.
  - apply Z.mod_small.
    pose proof (Zdigits_correct radix2 m0) as D. rewrite Z.abs_eq in D by lia.
    change (Zpower radix2 (Zdigits radix2 m0)) with (2 ^ Zdigits radix2 m0) in D.
    assert (Zdigits radix2 m0 <= 128).
    { destruct (Z_le_gt_dec (Zdigits radix2 m0) 128) as [L | L]; [exact L | exfalso].
      change (Zpower radix2 (Zdigits radix2 m0 - 1)) with (2 ^ (Zdigits radix2 m0 - 1)) in D.
      assert (2 ^ 128 <= 2 ^ (Zdigits radix2 m0 - 1)) by (apply Z.pow_le_mono_r; lia). unfold W in H. lia. }
    assert (0 <= Zdigits radix2 m0) by apply Zdigits_ge_0.
    split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia] | ].
    unfold W. replace (2 ^ 128) with (2 ^ Zdigits radix2 m0 * 2 ^ (128 - Zdigits radix2 m0))
      by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
    apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia | exact (proj2 D)].
  - assert (Zdigits radix2 m0 <= 128); [ | lia].
    pose proof (Zdigits_correct radix2 m0) as D. rewrite Z.abs_eq in D by lia.
    destruct (Z_le_gt_dec (Zdigits radix2 m0) 128) as [L | L]; [exact L | exfalso].
    change (Zpower radix2 (Zdigits radix2 m0 - 1)) with (2 ^ (Zdigits radix2 m0 - 1)) in D.
    assert (2 ^ 128 <= 2 ^ (Zdigits radix2 m0 - 1)) by (apply Z.pow_le_mono_r; lia). unfold W in H. lia.
Qed.

Definition mul (a b : q128) : q128 :=
  if (m a =? 0) || (m b =? 0) then zero else
  let '(hi, lo) := prod128 (m a) (m b) in
  let n := xorb (neg a) (neg b) in
  if negb (Z.land hi TOP =? 0) then Q n hi (e a + e b + 128)
  else Q n (Z.lor ((Z.shiftl hi 1) mod W) (Z.shiftr lo 127)) (e a + e b + 127).

Lemma top_bit x : 0 <= x < W -> (Z.land x TOP =? 0) = (x <? TOP).
Proof.
  intros H. unfold TOP, W in *.
  destruct (Z.ltb_spec x (2 ^ 127)) as [L | L].
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 127) as [-> | Ne].
    + rewrite <- (Z.mod_small x (2 ^ 127)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply andb_false_r.
  - apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit x 127 = true).
    { rewrite Z.testbit_eqb by lia. apply Z.eqb_eq.
      replace (x / 2 ^ 127) with 1; [reflexivity | ].
      apply Z.div_unique with (x - 2 ^ 127); [left; lia | lia]. }
    assert (T2 : Z.testbit (Z.land x (2 ^ 127)) 127 = true).
    { rewrite Z.land_spec, T, Z.pow2_bits_true by lia. reflexivity. }
    rewrite Z0, Z.bits_0 in T2. discriminate.
Qed.

Theorem mul_ok a b : normalized 128 (m a) -> normalized 128 (m b) ->
  let r := mul a b in
  neg r = xorb (neg a) (neg b) /\
  let '(mm, k) := mul_m 128 (m a) (m b) in m r = mm /\ e r = e a + e b + k.
Proof.
  unfold normalized. intros [A1 A2] [B1 B2]. unfold mul.
  replace ((m a =? 0) || (m b =? 0)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 127); lia).
  pose proof (prod128_ok (m a) (m b) ltac:(lia) ltac:(lia)) as P.
  destruct (prod128 (m a) (m b)) as [hi lo]. destruct P as [Pe Plo].
  assert (Hhi : 0 <= hi < W).
  { assert (0 <= m a * m b < 2 ^ 128 * 2 ^ 128) by (split; [nia | apply Z.mul_lt_mono_nonneg; lia]).
    unfold W. split; nia. }
  rewrite top_bit by exact Hhi. unfold mul_m.
  assert (Hc : (2 ^ (2 * 128 - 1) <=? m a * m b) = negb (hi <? TOP)).
  { unfold TOP. rewrite <- Pe. destruct (Z.ltb_spec hi (2 ^ 127)); simpl;
      [apply Z.leb_gt | apply Z.leb_le]; change (2 * 128 - 1) with 255;
      replace (2 ^ 255) with (2 ^ 127 * 2 ^ 128) by reflexivity; nia. }
  rewrite Hc. destruct (hi <? TOP) eqn:L; cbv beta iota zeta; cbn [m e neg negb]; (split; [reflexivity | split; [ | reflexivity]]).
  - (* top bit clear: the product's bits 254 down to 127 *)
    apply Z.ltb_lt in L. unfold TOP in L.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Lb : 0 <= lo / 2 ^ 127 < 2).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]]. change (2 ^ 127 * 2) with (2 ^ 128). lia. }
    rewrite Z.shiftl_mul_pow2, Z.mod_small by (unfold W; lia).
    replace (Z.lor (hi * 2 ^ 1) (lo / 2 ^ 127)) with (hi * 2 + lo / 2 ^ 127).
    + rewrite <- Pe. apply Z.div_unique with (lo mod 2 ^ 127).
      * left. apply Z.mod_pos_bound. lia.
      * pose proof (Z.div_mod lo (2 ^ 127) ltac:(lia)) as Dl. change (128 - 1) with 127.
        rewrite Dl at 1. replace (2 ^ 128) with (2 * 2 ^ 127) by reflexivity. ring.
    + symmetry. rewrite Z.lor_comm.
      replace (hi * 2 ^ 1) with (Z.shiftl hi 1) by (apply Z.shiftl_mul_pow2; lia).
      rewrite (lor_disjoint_low (lo / 2 ^ 127) hi 1) by (change (2 ^ 1) with 2; lia).
      change (2 ^ 1) with 2. ring.
  - (* top bit set: the product's top 128 bits *)
    rewrite <- Pe. apply Z.div_unique with lo; [left; lia | ring].
Qed.

Definition cmp_abs (a b : q128) : comparison :=
  match m a =? 0, m b =? 0 with
  | true, true => Eq
  | true, false => Lt
  | false, true => Gt
  | false, false =>
      if negb (e a =? e b) then (if e a <? e b then Lt else Gt) else Z.compare (m a) (m b)
  end.

Definition mag (x : q128) : R := F2R (Float radix2 (m x) (e x)).

Lemma mag_bounds x : normalized 128 (m x) ->
  (bpow radix2 (e x + 127) <= mag x < bpow radix2 (e x + 128))%R.
Proof.
  unfold normalized, mag, F2R. intros [L U]. simpl.
  rewrite !bpow_plus, <- (IZR_pow2 127), <- (IZR_pow2 128) by lia.
  pose proof (bpow_gt_0 radix2 (e x)).
  rewrite (Rmult_comm (bpow radix2 (e x))), (Rmult_comm (bpow radix2 (e x))).
  split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; try lra; [apply IZR_le | apply IZR_lt]; lia.
Qed.

Theorem cmp_abs_ok a b : normalized 128 (m a) -> normalized 128 (m b) ->
  match cmp_abs a b with
  | Lt => (mag a < mag b)%R
  | _ => (mag b <= mag a)%R
  end.
Proof.
  intros Ha Hb. pose proof (mag_bounds a Ha) as [A1 A2]. pose proof (mag_bounds b Hb) as [B1 B2].
  unfold normalized in *. unfold cmp_abs.
  replace (m a =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 127); lia).
  replace (m b =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 127); lia).
  destruct (Z.eqb_spec (e a) (e b)) as [E | E]; simpl.
  - unfold mag, F2R. simpl. rewrite E.
    destruct (Z.compare_spec (m a) (m b)) as [C | C | C].
    + rewrite C. lra.
    + apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; exact C].
    + apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia].
  - destruct (Z.ltb_spec (e a) (e b)) as [L | L].
    + apply Rlt_le_trans with (1 := A2). apply Rle_trans with (2 := B1). apply bpow_le. lia.
    + apply Rle_trans with (1 := Rlt_le _ _ B2). apply Rle_trans with (2 := A1). apply bpow_le. lia.
Qed.

Definition add (a b : q128) : q128 :=
  if m a =? 0 then b else if m b =? 0 then a else
  let '(big, small) := match cmp_abs a b with Lt => (b, a) | _ => (a, b) end in
  let d := e big - e small in
  let aligned := if 128 <=? d then 0 else Z.shiftr (m small) d in
  if Bool.eqb (neg big) (neg small) then
    let sum := (m big + aligned) mod W in
    if W <=? m big + aligned then Q (neg big) (Z.lor (Z.shiftr sum 1) TOP) (e big + 1)
    else Q (neg big) sum (e big)
  else new (neg big) (m big - aligned) (e big).

Definition qval (x : q128) : R := val (neg x) (m x) (e x).

Lemma val_zero n e0 : val n 0 e0 = 0%R.
Proof. unfold val. destruct n; simpl; apply F2R_0. Qed.

(** The aligned-add step, for [|big| >= |small|]: the specification's
    significand and exponent, under [big]'s sign. *)
Lemma add_step big small : normalized 128 (m big) -> normalized 128 (m small) ->
  (mag small <= mag big)%R ->
  let d := e big - e small in
  let aligned := if 128 <=? d then 0 else Z.shiftr (m small) d in
  let r := if Bool.eqb (neg big) (neg small) then
             let sum := (m big + aligned) mod W in
             if W <=? m big + aligned then Q (neg big) (Z.lor (Z.shiftr sum 1) TOP) (e big + 1)
             else Q (neg big) sum (e big)
           else new (neg big) (m big - aligned) (e big) in
  let '(ms, es) := add_m 128 (Bool.eqb (neg big) (neg small)) (m big) (e big) (m small) (e small) in
  m r = ms /\ qval r = val (neg big) ms es.
Proof.
  intros [G1 G2] [S1 S2] Hle d aligned r.
  assert (Hd : 0 <= d).
  { unfold d. destruct (Z_le_gt_dec (e small) (e big)) as [ | Gt]; [lia | exfalso].
    pose proof (mag_bounds big (conj G1 G2)) as [_ U]. pose proof (mag_bounds small (conj S1 S2)) as [L _].
    assert (bpow radix2 (e big + 128) <= bpow radix2 (e small + 127))%R by (apply bpow_le; lia). lra. }
  assert (Pd : 0 < 2 ^ d) by (apply Z.pow_pos_nonneg; lia).
  assert (Al : aligned = m small / 2 ^ d).
  { unfold aligned. destruct (Z.leb_spec 128 d).
    - symmetry. apply Z.div_small. split; [lia | ].
      apply Z.lt_le_trans with (2 ^ 128); [exact S2 | apply Z.pow_le_mono_r; lia].
    - apply Z.shiftr_div_pow2. lia. }
  assert (Alb : 0 <= aligned <= m small) by (rewrite Al; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  unfold add_m. fold d. rewrite <- Al. unfold r.
  destruct (Bool.eqb (neg big) (neg small)).
  - cbv zeta. unfold W.
    destruct (Z.leb_spec (2 ^ 128) (m big + aligned)) as [C | C]; cbv beta iota zeta.
    + (* the carry: (sum >> 1) | TOP is the halved sum *)
      enough (Hm : Z.lor (Z.shiftr ((m big + aligned) mod 2 ^ 128) 1) TOP = (m big + aligned) / 2)
        by (rewrite Hm; split; reflexivity).
      unfold TOP. rewrite Z.shiftr_div_pow2 by lia.
      replace ((m big + aligned) mod 2 ^ 128) with (m big + aligned - 2 ^ 128)
        by (apply Z.mod_unique with 1; [left; lia | ring]).
      replace (2 ^ 127) with (Z.shiftl 1 127) by reflexivity.
      rewrite lor_disjoint_low.
      * apply Z.div_unique with ((m big + aligned) mod 2).
        -- left. apply Z.mod_pos_bound. lia.
        -- assert (E : (m big + aligned - 2 ^ 128) mod 2 = (m big + aligned) mod 2).
           { replace (m big + aligned - 2 ^ 128) with (m big + aligned + (- 2 ^ 127) * 2) by ring.
             apply Z.mod_add. lia. }
           pose proof (Z.div_mod (m big + aligned - 2 ^ 128) 2 ltac:(lia)).
           rewrite E in H. change (2 ^ 1) with 2. change (2 ^ 127 * 2 ^ 1) with (2 ^ 128) in *.
           change (2 ^ 127 * 2) with (2 ^ 128). lia.
      * split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]]. change (2 ^ 1 * 2 ^ 127) with (2 ^ 128). lia.
      * lia.
      * lia.
    + rewrite Z.mod_small by lia. split; reflexivity.
  - assert (Ab : aligned <= m big).
    { destruct (Z.eq_dec d 0) as [D0 | D1].
      - rewrite Al, D0, Z.pow_0_r, Z.div_1_r. apply le_IZR.
        assert (Ee : e small = e big) by (unfold d in D0; lia).
        unfold mag, F2R in Hle; simpl in Hle. rewrite Ee in Hle.
        apply Rmult_le_reg_r with (bpow radix2 (e big)); [apply bpow_gt_0 | exact Hle].
      - rewrite Al. apply Z.le_trans with (m small / 2).
        + apply Z.div_le_compat_l; [lia | split; [lia | ]].
          change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia.
        + assert (m small / 2 < 2 ^ 127) by (apply Z.div_lt_upper_bound; [lia | ]; change (2 * 2 ^ 127) with (2 ^ 128); lia).
          change (2 ^ (128 - 1)) with (2 ^ 127) in G1. lia. }
    pose proof (new_ok (neg big) (m big - aligned) (e big) ltac:(unfold W; lia)) as N.
    destruct (norm 128 (m big - aligned) (e big)) as [nm ne] eqn:En.
    destruct (new (neg big) (m big - aligned) (e big)) as [rn rm re] eqn:Er.
    cbn [m e neg] in N |- *. inversion N; subst rm re. split; [reflexivity | ].
    unfold qval. cbn [m e neg].
    destruct (Z.eq_dec nm 0) as [-> | Nz]; [rewrite !val_zero; reflexivity | ].
    unfold new in Er. destruct (m big - aligned =? 0).
    + exfalso. apply Nz. unfold zero in Er. inversion Er. reflexivity.
    + inversion Er. reflexivity.
Qed.

Theorem add_ok a b : normalized 128 (m a) -> normalized 128 (m b) ->
  let r := add a b in
  (m r = 0 \/ normalized 128 (m r)) /\
  (Rabs (qval r - (qval a + qval b)) <= bpow radix2 (-126) * Rmax (mag a) (mag b))%R.
Proof.
  intros Ha Hb. pose proof (cmp_abs_ok a b Ha Hb) as Cmp. unfold add.
  replace (m a =? 0) with false by (symmetry; apply Z.eqb_neq; destruct Ha; pose proof (Z.pow_pos_nonneg 2 127); lia).
  replace (m b =? 0) with false by (symmetry; apply Z.eqb_neq; destruct Hb; pose proof (Z.pow_pos_nonneg 2 127); lia).
  assert (Gen : forall big small, normalized 128 (m big) -> normalized 128 (m small) ->
    (mag small <= mag big)%R -> (qval big + qval small = qval a + qval b)%R ->
    Rmax (mag a) (mag b) = mag big ->
    let d := e big - e small in
    let aligned := if 128 <=? d then 0 else Z.shiftr (m small) d in
    let r := if Bool.eqb (neg big) (neg small) then
               let sum := (m big + aligned) mod W in
               if W <=? m big + aligned then Q (neg big) (Z.lor (Z.shiftr sum 1) TOP) (e big + 1)
               else Q (neg big) sum (e big)
             else new (neg big) (m big - aligned) (e big) in
    (m r = 0 \/ normalized 128 (m r)) /\
    (Rabs (qval r - (qval a + qval b)) <= bpow radix2 (-126) * Rmax (mag a) (mag b))%R).
  { intros big small Hg Hs Hle Hsum Hmax d aligned r.
    pose proof (add_step big small Hg Hs Hle) as St. cbv zeta in St. fold d aligned r in St.
    pose proof (add_signed 128 ltac:(lia) (neg big) (m big) (e big) (neg small) (m small) (e small) Hg Hs Hle) as AS.
    destruct (add_m 128 (Bool.eqb (neg big) (neg small)) (m big) (e big) (m small) (e small)) as [ms es].
    destruct St as [Sm Sv]. destruct AS as [AM AE].
    rewrite Sm. split; [exact AM | ].
    rewrite Sv, <- Hsum, Hmax. exact AE. }
  destruct (cmp_abs a b).
  - apply Gen; auto. apply Rmax_left. exact Cmp.
  - apply Gen; auto; [lra | lra | apply Rmax_right; lra].
  - apply Gen; auto. apply Rmax_left. exact Cmp.
Qed.

From Flocq Require Import IEEE754.Binary.

Definition to_f64 (x : q128) : binary_float 53 1024 :=
  if m x =? 0 then B754_zero 53 1024 (neg x) else
  let top := e x + 127 in
  if 1023 <? top then B754_infinity 53 1024 (neg x) else
  let quantum := if -1022 <=? top then top - 52 else -1074 in
  let shift := quantum - e x in
  let kept := if 128 <=? shift then 0 else Z.shiftr (m x) shift in
  let up := if 128 <? shift then false else
              let half := Z.shiftl 1 (shift - 1) in
              let rem := if shift =? 128 then m x else Z.land (m x) (Z.shiftl 1 shift - 1) in
              (half <? rem) || ((rem =? half) && Z.odd kept) in
  bn (signed (neg x) (kept + if up then 1 else 0)) quantum (neg x).

(** Q128::to_f64 rounds to nearest-even: it is [binary_normalize] of the
    exact value, overflow and subnormals included. *)
Theorem to_f64_ok x : normalized 128 (m x) ->
  to_f64 x = bn (signed (neg x) (m x)) (e x) (neg x).
Proof.
  intros Hx. rewrite <- (to_f64_spec_ok 128) by (try lia; exact Hx).
  destruct Hx as [L U]. change (2 ^ (128 - 1)) with (2 ^ 127) in L.
  unfold to_f64, to_f64_spec. replace (e x + 128 - 1) with (e x + 127) by ring.
  destruct (m x =? 0); [reflexivity | ].
  destruct (1023 <? e x + 127); [reflexivity | ]. cbv zeta.
  set (quantum := if -1022 <=? e x + 127 then e x + 127 - 52 else -1074).
  assert (Sh : 75 <= quantum - e x) by (unfold quantum; destruct (Z.leb_spec (-1022) (e x + 127)); lia).
  set (shift := quantum - e x) in *.
  assert (K : (if 128 <=? shift then 0 else Z.shiftr (m x) shift) = m x / 2 ^ shift).
  { destruct (Z.leb_spec 128 shift).
    - symmetry. apply Z.div_small. split; [lia | ].
      apply Z.lt_le_trans with (2 ^ 128); [exact U | apply Z.pow_le_mono_r; lia].
    - apply Z.shiftr_div_pow2. lia. }
  rewrite K. f_equal. f_equal. f_equal. f_equal.
  unfold round_up.
  rewrite Z.shiftl_1_l.
  destruct (Z.ltb_spec 128 shift) as [G | G].
  - (* below half the least subnormal: the remainder is m, below half *)
    rewrite Z.mod_small by (split; [lia | apply Z.lt_le_trans with (2 ^ 128); [exact U | apply Z.pow_le_mono_r; lia]]).
    assert (2 ^ 128 <= 2 ^ (shift - 1)) by (apply Z.pow_le_mono_r; lia).
    replace (2 ^ (shift - 1) <? m x) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (m x =? 2 ^ (shift - 1)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (Z.eqb_spec shift 128) as [E | E].
    + rewrite E, Z.mod_small by lia. reflexivity.
    + rewrite Z.shiftl_1_l.
      replace (2 ^ shift - 1) with (Z.ones shift) by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by lia. reflexivity.
Qed.

(** The multiplication contract on values. *)
Theorem mul_value a b : normalized 128 (m a) -> normalized 128 (m b) ->
  let r := mul a b in
  normalized 128 (m r) /\
  (qval r <= qval a * qval b /\ qval a * qval b - qval r <= bpow radix2 (-127) * (qval a * qval b)
   \/ qval a * qval b <= qval r /\ qval r - qval a * qval b <= - bpow radix2 (-127) * (qval a * qval b))%R.
Proof.
  intros Ha Hb. pose proof (mul_ok a b Ha Hb) as M. pose proof (mul_contract 128 ltac:(lia) (m a) (m b) (e a) (e b) Ha Hb) as C.
  destruct (mul_m 128 (m a) (m b)) as [mm k]. destruct M as [Mn [Mm Me]].
  destruct C as [Cn [C1 C2]].
  cbv zeta. rewrite Mm. split; [exact Cn | ].
  assert (Prod : (qval a * qval b = val (xorb (neg a) (neg b)) (m a * m b) (e a + e b))%R).
  { unfold qval, val, F2R. simpl. rewrite bpow_plus.
    destruct (neg a), (neg b); simpl; rewrite ?opp_IZR, ?mult_IZR; ring. }
  assert (Res : qval (mul a b) = val (xorb (neg a) (neg b)) mm (e a + e b + k)).
  { unfold qval. rewrite Mn, Mm, Me. reflexivity. }
  rewrite Prod, Res. change (1 - 128) with (-127) in C2.
  unfold val. destruct (xorb (neg a) (neg b)).
  - right. rewrite !F2R_Zopp. split; lra.
  - left. split; lra.
Qed.

From Flocq Require Import IEEE754.Bits.

Lemma new_val n m0 e0 : 0 <= m0 < W -> qval (new n m0 e0) = val n m0 e0.
Proof.
  intros H. pose proof (new_ok n m0 e0 H) as N. pose proof (norm_ok 128 ltac:(lia) m0 e0 H) as V.
  destruct (norm 128 m0 e0) as [m' e']. destruct V as [_ V].
  unfold qval. destruct (Z.eqb_spec m0 0) as [-> | Hz].
  - unfold new. simpl. rewrite !val_zero. reflexivity.
  - assert (Nn : neg (new n m0 e0) = n) by (unfold new; destruct (Z.eqb_spec m0 0); [lia | reflexivity]).
    inversion N as [[Hm He]]. rewrite Nn, Hm, He.
    unfold val. destruct n; [rewrite !F2R_Zopp, V | rewrite V]; reflexivity.
Qed.

(** Q128::from_f64, on the binary64 encoding [bits]. *)
Definition from_f64 (bits : Z) : q128 :=
  let biased := Z.land (Z.shiftr bits 52) 2047 in
  let fraction := Z.land bits (2 ^ 52 - 1) in
  let '(sig, ex) := if biased =? 0 then (fraction, -1074) else (Z.lor fraction (2 ^ 52), biased - 1075) in
  new (Z.shiftr bits 63 =? 1) sig ex.

(** It is exact: the value of every finite binary64 encoding. *)
Theorem from_f64_ok bits : 0 <= bits < 2 ^ 64 -> (bits / 2 ^ 52) mod 2 ^ 11 <> 2047 ->
  qval (from_f64 bits) = B2R 53 1024 (b64_of_bits bits).
Proof.
  intros Hb Hf. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B.
  unfold binary_float_of_bits_aux, split_bits.
  change (Zpower 2 52) with (2 ^ 52). change (Zpower 2 11) with (2 ^ 11).
  change (2 ^ 52 * 2 ^ 11) with (2 ^ 63). change (Zpower 2 11 - 1) with 2047.
  unfold from_f64.
  assert (Bi : Z.land (Z.shiftr bits 52) 2047 = (bits / 2 ^ 52) mod 2 ^ 11).
  { rewrite Z.shiftr_div_pow2 by lia. change 2047 with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. }
  assert (Fr : Z.land bits (2 ^ 52 - 1) = bits mod 2 ^ 52).
  { change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. reflexivity. }
  assert (Sg : (Z.shiftr bits 63 =? 1) = Zle_bool (2 ^ 63) bits).
  { rewrite Z.shiftr_div_pow2 by lia. destruct (Zle_bool_spec (2 ^ 63) bits) as [L | L].
    - apply Z.eqb_eq. symmetry. apply Z.div_unique with (bits - 2 ^ 63); [left; lia | ring].
    - apply Z.eqb_neq. rewrite Z.div_small by lia. lia. }
  rewrite Bi, Fr, Sg.
  set (sx := Zle_bool (2 ^ 63) bits). set (mx := bits mod 2 ^ 52). set (ex := (bits / 2 ^ 52) mod 2 ^ 11).
  assert (Mx : 0 <= mx < 2 ^ 52) by (apply Z.mod_pos_bound; lia).
  assert (Ex : 0 <= ex < 2 ^ 11) by (apply Z.mod_pos_bound; lia).
  fold ex in Hf.
  destruct (Z.eqb_spec ex 0) as [E0 | E0].
  - rewrite E0. simpl Zeq_bool. cbv iota.
    rewrite new_val by (unfold W; lia).
    destruct mx as [ | px | px] eqn:Em; [ | | lia].
    + simpl. rewrite val_zero. reflexivity.
    + simpl. unfold val. destruct sx; reflexivity.
  - replace (Zeq_bool ex 0) with false by (symmetry; apply Zeq_bool_false; exact E0).
    replace (Zeq_bool ex 2047) with false by (symmetry; apply Zeq_bool_false; exact Hf).
    cbv iota.
    replace (2 ^ 52) with (Z.shiftl 1 52) at 1 by reflexivity. rewrite (lor_disjoint_low mx 1 52) by lia.
    rewrite new_val by (unfold W; lia).
    replace (mx + 1 * 2 ^ 52) with (mx + 2 ^ 52) by ring.
    assert (Kp : 0 < mx + 2 ^ 52) by lia.
    remember (mx + 2 ^ 52) as k eqn:Ek. clear Ek.
    destruct k as [ | px | px]; [lia | | lia].
    unfold FF2R, val, F2R. simpl Fnum. simpl Fexp.
    replace (ex + -1074 - 1) with (ex - 1075) by ring.
    destruct sx; reflexivity.
Qed.

Definition neg_q (x : q128) : q128 := if m x =? 0 then x else Q (negb (neg x)) (m x) (e x).
Definition mul_pow2 (x : q128) (k : Z) : q128 := if m x =? 0 then x else Q (neg x) (m x) (e x + k).

Theorem neg_ok x : qval (neg_q x) = (- qval x)%R.
Proof.
  unfold neg_q, qval. destruct (Z.eqb_spec (m x) 0) as [E | E].
  - rewrite E, val_zero. ring.
  - unfold val. simpl. destruct (neg x); simpl; rewrite ?F2R_Zopp, ?Ropp_involutive; reflexivity.
Qed.

Theorem mul_pow2_ok x k : qval (mul_pow2 x k) = (qval x * bpow radix2 k)%R.
Proof.
  unfold mul_pow2, qval. destruct (Z.eqb_spec (m x) 0) as [E | E].
  - rewrite E, !val_zero. ring.
  - unfold val, F2R. simpl. rewrite bpow_plus. ring.
Qed.
