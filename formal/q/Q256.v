(** crates/morphiq-numerics/src/q256.rs, transcribed on its fields: the
    significand four u64 limbs, least significant first. Each operation is
    proved to compute the width-256 specification of QSpec.v and QRound.v. *)

From Coq Require Import Bool ZArith Lia Psatz List.
From Flocq Require Import Core Digits IEEE754.Binary IEEE754.Bits.
Import ListNotations.
Require Import QSpec QRound Q128Mul Limbs Digits64 Shifts LimbScan.
Open Scope Z_scope.

Record q256 := Q { neg : bool; m : list Z; e : Z }.

Definition ok4 (l : list Z) := limbs_ok l /\ length l = 4%nat.
Definition zero := Q false [0; 0; 0; 0] 0.

Lemma ok4_zero : ok4 [0; 0; 0; 0].
Proof. split; [repeat constructor; unfold B; lia | reflexivity]. Qed.

Lemma v4_bound l : ok4 l -> 0 <= v l < 2 ^ 256.
Proof. intros [O L]. pose proof (v_bounds l O) as V. rewrite L in V. exact V. Qed.

Definition new (n : bool) (m0 : list Z) (e0 : Z) : q256 :=
  if is_zero m0 then zero else
  let s := leading_zeros m0 in Q n (shl m0 s) (e0 - s).

Theorem new_ok n m0 e0 : ok4 m0 ->
  let r := new n m0 e0 in ok4 (m r) /\ (v (m r), e r) = norm 256 (v m0) e0.
Proof.
  intros [O L]. unfold new, norm. rewrite is_zero_ok by exact O.
  pose proof (v4_bound m0 (conj O L)) as V.
  destruct (Z.eqb_spec (v m0) 0) as [Z0 | Z0]; [split; [exact ok4_zero | reflexivity] | ].
  rewrite leading_zeros_ok by assumption.
  pose proof (Zdigits_correct radix2 (v m0)) as D. rewrite Z.abs_eq in D by lia.
  change (Zpower radix2 (Zdigits radix2 (v m0) - 1)) with (2 ^ (Zdigits radix2 (v m0) - 1)) in D.
  change (Zpower radix2 (Zdigits radix2 (v m0))) with (2 ^ Zdigits radix2 (v m0)) in D.
  assert (Dp : 1 <= Zdigits radix2 (v m0) <= 256).
  { split.
    - destruct (Z_lt_le_dec (Zdigits radix2 (v m0)) 1) as [Lt | Le]; [ | lia]. exfalso.
      assert (2 ^ Zdigits radix2 (v m0) <= 1) by (destruct (Z.eq_dec (Zdigits radix2 (v m0)) 0) as [-> | ]; [reflexivity | rewrite Z.pow_neg_r by lia; lia]). lia.
    - destruct (Z_le_gt_dec (Zdigits radix2 (v m0)) 256) as [Le | Gt]; [exact Le | exfalso].
      assert (2 ^ 256 <= 2 ^ (Zdigits radix2 (v m0) - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  pose proof (shl_ok m0 (256 - Zdigits radix2 (v m0)) O L ltac:(lia)) as [Sv [So Sl]].
  cbn [m e]. split; [split; assumption | ]. f_equal.
  rewrite Sv. apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia] | ].
  replace (2 ^ 256) with (2 ^ Zdigits radix2 (v m0) * 2 ^ (256 - Zdigits radix2 (v m0)))
    by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
  apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia | lia].
Qed.

(** Q256::mul: the 512-bit product, its top 256 bits, or bits 510 down to 255
    when bit 511 is clear. *)
Definition mul (a b : q256) : q256 :=
  if is_zero (m a) || is_zero (m b) then zero else
  let p := mul_limbs (m a) (m b) in
  let hi := skipn 4 p in
  let n := xorb (neg a) (neg b) in
  if Z.shiftr (nth 7 p 0) 63 =? 1 then Q n hi (e a + e b + 256)
  else
    let lo3 := nth 3 p 0 in
    let sh := shl hi 1 in
    Q n (Z.lor (nth 0 sh 0) (Z.shiftr lo3 63) :: skipn 1 sh) (e a + e b + 255).

Lemma firstn_skipn_v (p : list Z) k : v p = v (firstn k p) + B ^ Z.of_nat (length (firstn k p)) * v (skipn k p).
Proof. rewrite <- v_app, firstn_skipn. reflexivity. Qed.

Theorem mul_ok a b : ok4 (m a) -> ok4 (m b) -> normalized 256 (v (m a)) -> normalized 256 (v (m b)) ->
  let r := mul a b in
  ok4 (m r) /\ neg r = xorb (neg a) (neg b) /\
  let '(mm, k) := mul_m 256 (v (m a)) (v (m b)) in v (m r) = mm /\ e r = e a + e b + k.
Proof.
  intros [Oa La] [Ob Lb] Na Nb. destruct Na as [A1 A2]. destruct Nb as [B1 B2].
  unfold mul. rewrite !is_zero_ok by assumption.
  replace (v (m a) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 255); lia).
  replace (v (m b) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 255); lia).
  simpl orb. cbv zeta.
  pose proof (mul_limbs_ok (m a) (m b) La Lb Oa Ob) as [Pv [Po Pl]].
  set (p := mul_limbs (m a) (m b)) in *.
  (* p = lo ++ hi, each four limbs *)
  assert (Lhi : length (skipn 4 p) = 4%nat) by (rewrite skipn_length; lia).
  assert (Ohi : limbs_ok (skipn 4 p)) by (apply limbs_ok_skipn, Po).
  assert (Llo : length (firstn 4 p) = 4%nat) by (rewrite firstn_length; lia).
  assert (Olo : limbs_ok (firstn 4 p)) by (apply limbs_ok_firstn, Po).
  pose proof (firstn_skipn_v p 4) as Sp. rewrite Llo in Sp. change (B ^ Z.of_nat 4) with (2 ^ 256) in Sp.
  pose proof (v4_bound _ (conj Olo Llo)) as Vlo. pose proof (v4_bound _ (conj Ohi Lhi)) as Vhi.
  set (P := v (m a) * v (m b)) in *.
  assert (Hhi : v (skipn 4 p) = P / 2 ^ 256).
  { apply Z.div_unique with (v (firstn 4 p)); [left; lia | ]. rewrite <- Pv, Sp. ring. }
  (* bit 511: the top bit of limb 7 *)
  assert (N7 : nth 7 p 0 = dig (v p) 7) by (rewrite (nth_dig p 7) by (assumption || lia); reflexivity).
  assert (Top : (Z.shiftr (nth 7 p 0) 63 =? 1) = (2 ^ 511 <=? P)).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite N7, Pv. unfold dig.
    assert (P < 2 ^ 512) by (replace (2 ^ 512) with (2 ^ 256 * 2 ^ 256) by reflexivity; nia).
    change (B ^ 7) with (2 ^ 448).
    rewrite Z.mod_small by (split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; [lia | ]; change (2 ^ 448 * B) with (2 ^ 512); lia]).
    rewrite Z.div_div by lia. change (2 ^ 448 * 2 ^ 63) with (2 ^ 511).
    destruct (Z.leb_spec (2 ^ 511) P) as [Ge | Lt].
    - apply Z.eqb_eq. symmetry. apply Z.div_unique with (P - 2 ^ 511); [left; lia | ring].
    - apply Z.eqb_neq. rewrite Z.div_small by nia. lia. }
  rewrite Top. unfold mul_m. fold P.
  change (2 ^ (2 * 256 - 1)) with (2 ^ 511).
  destruct (Z.leb_spec (2 ^ 511) P) as [Ge | Lt]; cbn [m e neg].
  - repeat split; try assumption; try reflexivity.
  - (* bits 510..255: (hi << 1) with lo's top bit in bit 0 *)
    assert (Hh : v (skipn 4 p) < 2 ^ 255).
    { rewrite Hhi. apply Z.div_lt_upper_bound; [lia | ]. change (2 ^ 256 * 2 ^ 255) with (2 ^ 511). lia. }
    pose proof (shl_ok (skipn 4 p) 1 Ohi Lhi ltac:(lia)) as [Shv [Sho Shl]].
    rewrite Z.mod_small in Shv by (split; [pose proof (v_nonneg _ Ohi); lia | change (2 ^ 256) with (2 * 2 ^ 255); lia]).
    set (sh := shl (skipn 4 p) 1) in *.
    destruct sh as [ | s0 rest] eqn:Esh; [discriminate | ].
    inversion Sho as [ | ? ? S0 Srest]; subst.
    (* s0 = (hi mod 2^63)·2, and the carried bit is bit 255 of P *)
    assert (Ev : s0 = (v (skipn 4 p) mod 2 ^ 63) * 2).
    { cbn [v] in Shv. change (2 ^ 1) with 2 in Shv. pose proof (v_nonneg _ Srest). pose proof B_pos.
      assert (s0 = (v (skipn 4 p) * 2) mod B).
      { rewrite <- Shv. rewrite Z.mul_comm with (n := B), Z.mod_add by lia. symmetry. apply Z.mod_small. exact S0. }
      rewrite H1. unfold B. change (2 ^ 64) with (2 ^ 63 * 2). apply Z.mul_mod_distr_r; lia. }
    assert (Ms : 0 <= v (skipn 4 p) mod 2 ^ 63 < 2 ^ 63) by (apply Z.mod_pos_bound; lia).
    assert (Bit : Z.shiftr (nth 3 p 0) 63 = (P / 2 ^ 255) mod 2).
    { rewrite Z.shiftr_div_pow2 by lia. rewrite (nth_dig p 3) by (assumption || lia). rewrite Pv. unfold dig.
      change (B ^ Z.of_nat 3) with (2 ^ 192). unfold B.
      change (2 ^ 64) with (2 ^ 63 * 2). rewrite Z.rem_mul_r || idtac.
      rewrite (Z.mul_comm (2 ^ 63)), Z.div_add by lia.
      rewrite (Z.div_small ((P / 2 ^ 192) mod 2 ^ 63)) by (apply Z.mod_pos_bound; lia).
      rewrite Z.div_div by lia. reflexivity. all: lia. }
    assert (L3 : 0 <= Z.shiftr (nth 3 p 0) 63 <= 1) by (rewrite Bit; pose proof (Z.mod_pos_bound (P / 2 ^ 255) 2); lia).
    assert (Or : Z.lor s0 (Z.shiftr (nth 3 p 0) 63) = s0 + Z.shiftr (nth 3 p 0) 63).
    { rewrite Ev.
      replace ((v (skipn 4 p) mod 2 ^ 63) * 2) with (Z.shiftl (v (skipn 4 p) mod 2 ^ 63) 1)
        by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite Z.lor_comm, lor_disjoint_low by (try lia; change (2 ^ 1) with 2; lia).
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. ring. }
    cbn [nth skipn]. repeat split.
    + constructor; [ | exact Srest]. rewrite Or, Ev. unfold B. split; [lia | ]. change (2 ^ 64) with (2 * 2 ^ 63). lia.
    + cbn [length]. cbn [length] in Shl. exact Shl.
    + cbn [v]. rewrite Or.
      assert (Vsh : s0 + B * v rest = v (skipn 4 p) * 2) by (cbn [v] in Shv; change (2 ^ 1) with 2 in Shv; lia).
      replace (s0 + Z.shiftr (nth 3 p 0) 63 + B * v rest) with (v (skipn 4 p) * 2 + Z.shiftr (nth 3 p 0) 63) by lia.
      rewrite Bit, Hhi. change (256 - 1) with 255.
      pose proof (Z.div_mod (P / 2 ^ 255) 2 ltac:(lia)) as D.
      rewrite Z.div_div in D by lia. change (2 ^ 255 * 2) with (2 ^ 256) in D. lia.
Qed.

Definition qval (x : q256) : R := val (neg x) (v (m x)) (e x).
Definition mag (x : q256) : R := F2R (Float radix2 (v (m x)) (e x)).

Lemma val_zero n e0 : val n 0 e0 = 0%R.
Proof. unfold val. destruct n; simpl; apply F2R_0. Qed.

Definition cmp_abs (a b : q256) : comparison :=
  match is_zero (m a), is_zero (m b) with
  | true, true => Eq
  | true, false => Lt
  | false, true => Gt
  | false, false => match Z.compare (e a) (e b) with Eq => cmp (m a) (m b) | c => c end
  end.

Lemma mag_bounds x : normalized 256 (v (m x)) ->
  (bpow radix2 (e x + 255) <= mag x < bpow radix2 (e x + 256))%R.
Proof.
  unfold normalized, mag, F2R. intros [L U]. simpl.
  rewrite !bpow_plus, <- (IZR_pow2 255), <- (IZR_pow2 256) by lia.
  pose proof (bpow_gt_0 radix2 (e x)).
  rewrite (Rmult_comm (bpow radix2 (e x))), (Rmult_comm (bpow radix2 (e x))).
  split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; try lra; [apply IZR_le | apply IZR_lt]; lia.
Qed.

Theorem cmp_abs_ok a b : ok4 (m a) -> ok4 (m b) -> normalized 256 (v (m a)) -> normalized 256 (v (m b)) ->
  match cmp_abs a b with
  | Lt => (mag a < mag b)%R
  | _ => (mag b <= mag a)%R
  end.
Proof.
  intros [Oa La] [Ob Lb] Ha Hb. pose proof (mag_bounds a Ha) as [A1 A2]. pose proof (mag_bounds b Hb) as [B1 B2].
  unfold normalized in *. unfold cmp_abs. rewrite !is_zero_ok by assumption.
  replace (v (m a) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 255); lia).
  replace (v (m b) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 255); lia).
  destruct (Z.compare_spec (e a) (e b)) as [E | Lt | Gt].
  - rewrite cmp_ok by assumption. unfold mag, F2R. simpl. rewrite E.
    destruct (Z.compare_spec (v (m a)) (v (m b))) as [C | C | C].
    + rewrite C. lra.
    + apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; exact C].
    + apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia].
  - apply Rlt_le_trans with (1 := A2). apply Rle_trans with (2 := B1). apply bpow_le. lia.
  - apply Rle_trans with (1 := Rlt_le _ _ B2). apply Rle_trans with (2 := A1). apply bpow_le. lia.
Qed.

(** [m[3] |= 1 << 63] *)
Definition set_top (l : list Z) : list Z := firstn 3 l ++ [Z.lor (nth 3 l 0) (2 ^ 63)] ++ skipn 4 l.

Lemma set_top_ok l : ok4 l -> v l < 2 ^ 255 -> ok4 (set_top l) /\ v (set_top l) = v l + 2 ^ 255.
Proof.
  intros [O L] H.
  destruct l as [ | l0 [ | l1 [ | l2 [ | l3 [ | ? ?]]]]]; try discriminate.
  inversion O as [ | ? ? X0 P1]; subst. inversion P1 as [ | ? ? X1 P2]; subst.
  inversion P2 as [ | ? ? X2 P3]; subst. inversion P3 as [ | ? ? X3 _]; subst.
  unfold set_top. cbn [firstn skipn nth app]. cbn [v] in *.
  assert (L3 : l3 < 2 ^ 63) by (unfold B in *; nia).
  assert (Or : Z.lor l3 (2 ^ 63) = l3 + 2 ^ 63).
  { replace (2 ^ 63) with (Z.shiftl 1 63) at 1 by reflexivity.
    rewrite lor_disjoint_low by lia. ring. }
  rewrite Or. split.
  - split; [ | reflexivity]. repeat constructor; unfold B in *; lia.
  - unfold B. ring.
Qed.

Definition add_limbs (a b : list Z) : list Z * bool := let '(s, c) := add_chain a b 0 in (s, negb (c =? 0)).
Definition sub_limbs (a b : list Z) : list Z := fst (sub_chain a b 0).

Definition add_ordered (big small : q256) : q256 :=
  let aligned := shr (m small) (e big - e small) in
  if Bool.eqb (neg big) (neg small) then
    let '(sum, carry) := add_limbs (m big) aligned in
    if carry then Q (neg big) (set_top (shr sum 1)) (e big + 1)
    else Q (neg big) sum (e big)
  else new (neg big) (sub_limbs (m big) aligned) (e big).

Definition add (a b : q256) : q256 :=
  if is_zero (m a) then b else if is_zero (m b) then a else
  match cmp_abs a b with Lt => add_ordered b a | _ => add_ordered a b end.

Lemma add_ordered_ok big small : ok4 (m big) -> ok4 (m small) ->
  normalized 256 (v (m big)) -> normalized 256 (v (m small)) -> (mag small <= mag big)%R ->
  let r := add_ordered big small in
  let '(ms, es) := add_m 256 (Bool.eqb (neg big) (neg small)) (v (m big)) (e big) (v (m small)) (e small) in
  ok4 (m r) /\ v (m r) = ms /\ qval r = val (neg big) ms es.
Proof.
  intros [Og Lg] [Os Ls] [G1 G2] [S1 S2] Hle.
  assert (Hd : e small <= e big).
  { destruct (Z_le_gt_dec (e small) (e big)) as [ | Gt]; [lia | exfalso].
    pose proof (mag_bounds big (conj G1 G2)) as [_ U]. pose proof (mag_bounds small (conj S1 S2)) as [L _].
    assert (bpow radix2 (e big + 256) <= bpow radix2 (e small + 255))%R by (apply bpow_le; lia). lra. }
  set (d := e big - e small).
  pose proof (shr_ok (m small) d Os Ls ltac:(lia)) as [Av [Ao Al]].
  set (aligned := shr (m small) d) in *.
  assert (Pd : 0 < 2 ^ d) by (apply Z.pow_pos_nonneg; lia).
  assert (Alb : 0 <= v aligned <= v (m small)) by (rewrite Av; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  unfold add_ordered, add_m. fold d aligned. rewrite <- Av.
  destruct (Bool.eqb (neg big) (neg small)).
  - unfold add_limbs. pose proof (add_chain_ok (m big) aligned 0 ltac:(lia) Og Ao ltac:(lia)) as AC.
    destruct (add_chain (m big) aligned 0) as [sum c]. destruct AC as [Sv [So [Sc Sl]]].
    rewrite Lg in Sv, Sl. change (B ^ Z.of_nat 4) with (2 ^ 256) in Sv.
    pose proof (v4_bound sum (conj So Sl)) as Sb.
    destruct (Z.eqb_spec c 0) as [C0 | C1]; cbv beta iota; cbn [negb].
    + subst c. replace (2 ^ 256 <=? v (m big) + v aligned) with false
        by (symmetry; apply Z.leb_gt; lia).
      assert (Sv' : v sum = v (m big) + v aligned) by lia.
      cbn [m neg e]. split; [split; assumption | split; [exact Sv' | ]]. unfold qval. cbn [m neg e]. rewrite Sv'. reflexivity.
    + assert (c = 1) by lia. subst c.
      replace (2 ^ 256 <=? v (m big) + v aligned) with true by (symmetry; apply Z.leb_le; lia).
      pose proof (shr_ok sum 1 So Sl ltac:(lia)) as [Hv [Ho Hl]].
      assert (Half : v (shr sum 1) < 2 ^ 255) by (rewrite Hv; apply Z.div_lt_upper_bound; [lia | ]; change (2 ^ 1 * 2 ^ 255) with (2 ^ 256); lia).
      pose proof (set_top_ok (shr sum 1) (conj Ho Hl) Half) as [To Tv].
      assert (Mv : v (set_top (shr sum 1)) = (v (m big) + v aligned) / 2).
      { rewrite Tv, Hv. change (2 ^ 1) with 2. apply Z.div_unique with ((v (m big) + v aligned) mod 2).
        - left. apply Z.mod_pos_bound. lia.
        - pose proof (Z.div_mod (v sum) 2 ltac:(lia)). pose proof (Z.div_mod (v (m big) + v aligned) 2 ltac:(lia)).
          assert (v sum mod 2 = (v (m big) + v aligned) mod 2).
          { replace (v (m big) + v aligned) with (v sum + 2 ^ 255 * 2) by lia. rewrite Z.mod_add by lia. reflexivity. }
          lia. }
      cbn [m neg e]. split; [exact To | split; [exact Mv | ]]. unfold qval. cbn [m neg e]. rewrite Mv. reflexivity.
  - assert (Ab : v aligned <= v (m big)).
    { destruct (Z.eq_dec d 0) as [D0 | D1].
      - rewrite Av, D0, Z.pow_0_r, Z.div_1_r. apply le_IZR.
        assert (Ee : e small = e big) by (unfold d in D0; lia).
        unfold mag, F2R in Hle; simpl in Hle. rewrite Ee in Hle.
        apply Rmult_le_reg_r with (bpow radix2 (e big)); [apply bpow_gt_0 | exact Hle].
      - rewrite Av. apply Z.le_trans with (v (m small) / 2).
        + apply Z.div_le_compat_l; [lia | split; [lia | ]]. change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia.
        + assert (v (m small) / 2 < 2 ^ 255) by (apply Z.div_lt_upper_bound; [lia | ]; change (2 * 2 ^ 255) with (2 ^ 256); lia).
          change (2 ^ (256 - 1)) with (2 ^ 255) in G1. lia. }
    unfold sub_limbs. pose proof (sub_chain_exact (m big) aligned ltac:(lia) Og Ao Ab) as SC.
    destruct (sub_chain (m big) aligned 0) as [dl br]. destruct SC as [Dv [Do Dl]]. cbn [fst].
    rewrite Lg in Dl.
    pose proof (new_ok (neg big) dl (e big) (conj Do Dl)) as [No Ne].
    rewrite Dv in Ne. destruct (norm 256 (v (m big) - v aligned) (e big)) as [nm ne] eqn:En.
    injection Ne as Hm He. split; [exact No | split; [exact Hm | ]].
    unfold qval. rewrite Hm, He.
    destruct (Z.eq_dec nm 0) as [-> | Nz]; [rewrite !val_zero; reflexivity | ].
    unfold new. rewrite is_zero_ok by assumption.
    destruct (Z.eqb_spec (v dl) 0) as [Z0 | Z0].
    + exfalso. apply Nz. unfold new in Hm. rewrite is_zero_ok, Z0 in Hm by assumption. simpl in Hm. lia.
    + reflexivity.
Qed.

Theorem add_ok a b : ok4 (m a) -> ok4 (m b) -> normalized 256 (v (m a)) -> normalized 256 (v (m b)) ->
  let r := add a b in
  ok4 (m r) /\ (v (m r) = 0 \/ normalized 256 (v (m r))) /\
  (Rabs (qval r - (qval a + qval b)) <= bpow radix2 (-254) * Rmax (mag a) (mag b))%R.
Proof.
  intros Oa Ob Ha Hb. pose proof (cmp_abs_ok a b Oa Ob Ha Hb) as Cmp. unfold add.
  rewrite !is_zero_ok by (apply Oa || apply Ob).
  replace (v (m a) =? 0) with false by (symmetry; apply Z.eqb_neq; destruct Ha; pose proof (Z.pow_pos_nonneg 2 255); lia).
  replace (v (m b) =? 0) with false by (symmetry; apply Z.eqb_neq; destruct Hb; pose proof (Z.pow_pos_nonneg 2 255); lia).
  assert (Gen : forall big small, ok4 (m big) -> ok4 (m small) ->
    normalized 256 (v (m big)) -> normalized 256 (v (m small)) ->
    (mag small <= mag big)%R -> (qval big + qval small = qval a + qval b)%R ->
    Rmax (mag a) (mag b) = mag big ->
    let r := add_ordered big small in
    ok4 (m r) /\ (v (m r) = 0 \/ normalized 256 (v (m r))) /\
    (Rabs (qval r - (qval a + qval b)) <= bpow radix2 (-254) * Rmax (mag a) (mag b))%R).
  { intros big small Og Os Hg Hs Hle Hsum Hmax r. subst r.
    pose proof (add_ordered_ok big small Og Os Hg Hs Hle) as St.
    pose proof (add_signed 256 ltac:(lia) (neg big) (v (m big)) (e big) (neg small) (v (m small)) (e small) Hg Hs Hle) as AS.
    destruct (add_m 256 (Bool.eqb (neg big) (neg small)) (v (m big)) (e big) (v (m small)) (e small)) as [ms es].
    destruct St as [So [Sm Sv]]. destruct AS as [AM AE].
    split; [exact So | ]. rewrite Sm. split; [exact AM | ].
    rewrite Sv, <- Hsum, Hmax. exact AE. }
  destruct (cmp_abs a b).
  - apply Gen; auto. apply Rmax_left. exact Cmp.
  - apply Gen; auto; [lra | lra | apply Rmax_right; lra].
  - apply Gen; auto. apply Rmax_left. exact Cmp.
Qed.


Definition half4 := [0; 0; 0; 2 ^ 63].

Definition to_f64 (x : q256) : binary_float 53 1024 :=
  if is_zero (m x) then B754_zero 53 1024 (neg x) else
  let top := e x + 255 in
  if 1023 <? top then B754_infinity 53 1024 (neg x) else
  let quantum := if -1022 <=? top then top - 52 else -1074 in
  let shift := quantum - e x in
  let kept := nth 0 (shr (m x) shift) 0 in
  let up := if 256 <? shift then false else
              let rest := if shift =? 256 then m x else shl (m x) (256 - shift) in
              match cmp rest half4 with Gt => true | Eq => Z.odd kept | Lt => false end in
  bn (signed (neg x) (kept + if up then 1 else 0)) quantum (neg x).

(** Q256::to_f64 rounds to nearest-even: [binary_normalize] of the exact value. *)
Theorem to_f64_ok x : ok4 (m x) -> normalized 256 (v (m x)) ->
  to_f64 x = bn (signed (neg x) (v (m x))) (e x) (neg x).
Proof.
  intros [O L] Hx. rewrite <- (to_f64_spec_ok 256) by (try lia; exact Hx).
  destruct Hx as [M1 M2]. change (2 ^ (256 - 1)) with (2 ^ 255) in M1.
  unfold to_f64, to_f64_spec. rewrite is_zero_ok by exact O. replace (e x + 256 - 1) with (e x + 255) by ring.
  destruct (v (m x) =? 0); [reflexivity | ].
  destruct (1023 <? e x + 255); [reflexivity | ]. cbv zeta.
  set (quantum := if -1022 <=? e x + 255 then e x + 255 - 52 else -1074).
  assert (Sh : 203 <= quantum - e x) by (unfold quantum; destruct (Z.leb_spec (-1022) (e x + 255)); lia).
  set (shift := quantum - e x) in *.
  pose proof (shr_ok (m x) shift O L ltac:(lia)) as [Rv [Ro Rl]].
  (* the kept bits fit one limb *)
  assert (Kb : v (m x) / 2 ^ shift < B).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
    apply Z.lt_le_trans with (2 ^ 256); [lia | ]. unfold B. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  assert (K : nth 0 (shr (m x) shift) 0 = v (m x) / 2 ^ shift).
  { rewrite (nth_dig _ 0) by (assumption || lia). rewrite Rv. unfold dig. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, Z.div_1_r. apply Z.mod_small. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | exact Kb]. }
  rewrite K. f_equal. f_equal. f_equal. f_equal.
  unfold round_up.
  destruct (Z.ltb_spec 256 shift) as [G | G].
  - rewrite Z.mod_small by (split; [lia | apply Z.lt_le_trans with (2 ^ 256); [lia | apply Z.pow_le_mono_r; lia]]).
    assert (2 ^ 256 <= 2 ^ (shift - 1)) by (apply Z.pow_le_mono_r; lia).
    replace (2 ^ (shift - 1) <? v (m x)) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (v (m x) =? 2 ^ (shift - 1)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - assert (Hh : v half4 = 2 ^ 255) by reflexivity.
    assert (Oh : ok4 half4) by (split; [repeat constructor; unfold B; lia | reflexivity]).
    (* the discarded bits, scaled to the top: compare them with half *)
    assert (Rest : Z.compare (v (if shift =? 256 then m x else shl (m x) (256 - shift))) (2 ^ 255)
                   = Z.compare (v (m x) mod 2 ^ shift) (2 ^ (shift - 1))).
    { destruct (Z.eqb_spec shift 256) as [E | E].
      - rewrite E, Z.mod_small by lia. reflexivity.
      - pose proof (shl_ok (m x) (256 - shift) O L ltac:(lia)) as [Lv _]. rewrite Lv.
        replace (2 ^ 256) with (2 ^ shift * 2 ^ (256 - shift)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
        rewrite Z.mul_mod_distr_r by (apply Z.pow_nonzero; lia).
        replace (2 ^ 255) with (2 ^ (shift - 1) * 2 ^ (256 - shift)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
        symmetry. apply Zmult_compare_compat_r. apply Z.lt_gt, Z.pow_pos_nonneg; lia. }
    assert (OR : ok4 (if shift =? 256 then m x else shl (m x) (256 - shift))).
    { destruct (shift =? 256); [split; assumption | ].
      pose proof (shl_ok (m x) (256 - shift) O L ltac:(lia)) as [_ [So Sl]]. split; assumption. }
    destruct OR as [OR1 OR2]. destruct Oh as [Oh1 Oh2].
    rewrite cmp_ok by assumption. rewrite Hh, Rest.
    destruct (Z.compare_spec (v (m x) mod 2 ^ shift) (2 ^ (shift - 1))) as [E | Lt | Gt].
    + rewrite E, Z.ltb_irrefl, Z.eqb_refl. reflexivity.
    + replace (2 ^ (shift - 1) <? v (m x) mod 2 ^ shift) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (v (m x) mod 2 ^ shift =? 2 ^ (shift - 1)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + replace (2 ^ (shift - 1) <? v (m x) mod 2 ^ shift) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma new_val n l e0 : ok4 l -> qval (new n l e0) = val n (v l) e0.
Proof.
  intros Ol. destruct (Z.eq_dec (v l) 0) as [Z0 | Z0].
  - unfold new. rewrite is_zero_ok by apply Ol. rewrite Z0. cbv iota beta.
    unfold qval, zero. cbn [neg m e v]. rewrite ?Z.mul_0_r, ?Z.add_0_r, !val_zero. reflexivity.
  - pose proof (new_ok n l e0 Ol) as [_ N]. pose proof (v4_bound l Ol) as Vb.
    pose proof (norm_ok 256 ltac:(lia) (v l) e0 Vb) as V.
    destruct (norm 256 (v l) e0) as [m' e']. destruct V as [_ V]. injection N as Hm He.
    unfold qval. rewrite Hm, He.
    assert (Nn : neg (new n l e0) = n) by (unfold new; rewrite is_zero_ok by apply Ol; destruct (Z.eqb_spec (v l) 0); [lia | reflexivity]).
    rewrite Nn. unfold val. destruct n; [rewrite !F2R_Zopp, V | rewrite V]; reflexivity.
Qed.

Definition from_f64 (bits : Z) : q256 :=
  let biased := Z.land (Z.shiftr bits 52) 2047 in
  let fraction := Z.land bits (2 ^ 52 - 1) in
  let '(sig, ex) := if biased =? 0 then (fraction, -1074) else (Z.lor fraction (2 ^ 52), biased - 1075) in
  new (Z.shiftr bits 63 =? 1) [sig; 0; 0; 0] ex.

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
  assert (Ok : forall s, 0 <= s < 2 ^ 54 -> ok4 [s; 0; 0; 0]) by (intros; split; [repeat constructor; unfold B; lia | reflexivity]).
  destruct (Z.eqb_spec ex 0) as [E0 | E0].
  - rewrite E0. simpl Zeq_bool. cbv iota.
    rewrite new_val by (apply Ok; lia). cbn [v]. rewrite Z.mul_0_r, Z.add_0_r.
    destruct mx as [ | px | px] eqn:Em; [ | | lia].
    + simpl. rewrite val_zero. reflexivity.
    + simpl. unfold val. destruct sx; reflexivity.
  - replace (Zeq_bool ex 0) with false by (symmetry; apply Zeq_bool_false; exact E0).
    replace (Zeq_bool ex 2047) with false by (symmetry; apply Zeq_bool_false; exact Hf).
    cbv iota.
    replace (2 ^ 52) with (Z.shiftl 1 52) at 1 by reflexivity. rewrite (lor_disjoint_low mx 1 52) by lia.
    rewrite new_val by (apply Ok; lia). cbn [v]. rewrite Z.mul_0_r, Z.add_0_r.
    replace (mx + 1 * 2 ^ 52) with (mx + 2 ^ 52) by ring.
    assert (Kp : 0 < mx + 2 ^ 52) by lia.
    remember (mx + 2 ^ 52) as k eqn:Ek. clear Ek.
    destruct k as [ | px | px]; [lia | | lia].
    unfold FF2R, val, F2R. simpl Fnum. simpl Fexp.
    replace (ex + -1074 - 1) with (ex - 1075) by ring.
    destruct sx; reflexivity.
Qed.

Definition neg_q (x : q256) : q256 := if is_zero (m x) then x else Q (negb (neg x)) (m x) (e x).

Theorem neg_ok x : ok4 (m x) -> qval (neg_q x) = (- qval x)%R.
Proof.
  intros [O L]. unfold neg_q, qval. rewrite is_zero_ok by exact O.
  destruct (Z.eqb_spec (v (m x)) 0) as [E | E].
  - rewrite E, val_zero. ring.
  - unfold val. simpl. destruct (neg x); simpl; rewrite ?F2R_Zopp, ?Ropp_involutive; reflexivity.
Qed.

Theorem mul_value a b : ok4 (m a) -> ok4 (m b) -> normalized 256 (v (m a)) -> normalized 256 (v (m b)) ->
  let r := mul a b in
  ok4 (m r) /\ normalized 256 (v (m r)) /\
  (qval r <= qval a * qval b /\ qval a * qval b - qval r <= bpow radix2 (-255) * (qval a * qval b)
   \/ qval a * qval b <= qval r /\ qval r - qval a * qval b <= - bpow radix2 (-255) * (qval a * qval b))%R.
Proof.
  intros Oa Ob Ha Hb. pose proof (mul_ok a b Oa Ob Ha Hb) as M.
  pose proof (mul_contract 256 ltac:(lia) (v (m a)) (v (m b)) (e a) (e b) Ha Hb) as C.
  destruct (mul_m 256 (v (m a)) (v (m b))) as [mm k]. destruct M as [Mo [Mn [Mm Me]]].
  destruct C as [Cn [C1 C2]].
  cbv zeta. rewrite Mm. split; [exact Mo | split; [exact Cn | ]].
  assert (Prod : (qval a * qval b = val (xorb (neg a) (neg b)) (v (m a) * v (m b)) (e a + e b))%R).
  { unfold qval, val, F2R. simpl. rewrite bpow_plus.
    destruct (neg a), (neg b); simpl; rewrite ?opp_IZR, ?mult_IZR; ring. }
  assert (Res : qval (mul a b) = val (xorb (neg a) (neg b)) mm (e a + e b + k)).
  { unfold qval. rewrite Mn, Mm, Me. reflexivity. }
  rewrite Prod, Res. change (1 - 256) with (-255) in C2.
  unfold val. destruct (xorb (neg a) (neg b)).
  - right. rewrite !F2R_Zopp. split; lra.
  - left. split; lra.
Qed.

(** The index of the last nonzero limb ([rposition]). *)
Fixpoint rpos (l : list Z) : option nat :=
  match l with
  | [] => None
  | x :: r => match rpos r with Some k => Some (S k) | None => if x =? 0 then None else Some O end
  end.

Lemma rpos_ok l : limbs_ok l ->
  match rpos l with
  | None => v l = 0
  | Some k => (k < length l)%nat /\ nth k l 0 <> 0 /\ v l = v (firstn k l) + B ^ Z.of_nat k * nth k l 0
  end.
Proof.
  induction 1 as [ | x l Hx Hl IH]; [reflexivity | ]. cbn [rpos].
  destruct (rpos l) as [k | ].
  - destruct IH as [Lk [Nk Vk]]. repeat split.
    + cbn [length]. lia.
    + cbn [nth]. exact Nk.
    + cbn [v firstn nth]. rewrite Vk. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
  - destruct (Z.eqb_spec x 0) as [X0 | X0].
    + cbn [v]. rewrite X0, IH. ring.
    + repeat split; [cbn [length]; lia | exact X0 | ]. cbn [v firstn nth]. rewrite IH. change (Z.of_nat 0) with 0. ring.
Qed.

Lemma nth_dig_any (l : list Z) k : limbs_ok l -> 0 <= k -> nth (Z.to_nat k) l 0 = dig (v l) k.
Proof.
  intros Ok Hk. destruct (Z_lt_le_dec k (Z.of_nat (length l))) as [Lt | Ge].
  - rewrite nth_dig by (try assumption; lia). rewrite Z2Nat.id by lia. reflexivity.
  - rewrite nth_overflow by lia. symmetry. apply (dig_high _ (Z.of_nat (length l))); [ | lia].
    exact (v_bounds l Ok).
Qed.

Definition from_limbs (n : bool) (ms : list Z) (e0 : Z) : q256 :=
  match rpos ms with
  | None => zero
  | Some top =>
      let bits := 64 * Z.of_nat top + 64 - lz64 (nth top ms 0) in
      let drop := Z.max (bits - 256) 0 in
      let words := drop / 64 in let shift := drop mod 64 in
      let out := map (fun i =>
                   let lo := nth (Z.to_nat (i + words)) ms 0 in
                   let hi := nth (Z.to_nat (i + words + 1)) ms 0 in
                   if shift =? 0 then lo else Z.lor (Z.shiftr lo shift) (u64_shl hi (64 - shift))) [0; 1; 2; 3] in
      new n out (e0 + drop)
  end.

(** The kept limbs are the digits of [v ms / 2^drop]. *)
Lemma window_ok (ms : list Z) drop : limbs_ok ms -> 0 <= drop -> 0 <= v ms / 2 ^ drop < 2 ^ 256 ->
  let words := drop / 64 in let shift := drop mod 64 in
  let out := map (fun i =>
               let lo := nth (Z.to_nat (i + words)) ms 0 in
               let hi := nth (Z.to_nat (i + words + 1)) ms 0 in
               if shift =? 0 then lo else Z.lor (Z.shiftr lo shift) (u64_shl hi (64 - shift))) [0; 1; 2; 3] in
  ok4 out /\ v out = v ms / 2 ^ drop.
Proof.
  intros Ok Hd Hq words shift out.
  pose proof (v_nonneg ms Ok) as Vn.
  assert (Sw : drop = 64 * words + shift) by (apply Z.div_mod; lia).
  assert (Hw : 0 <= words) by (apply Z.div_pos; lia).
  assert (Hb : 0 <= shift < 64) by (apply Z.mod_pos_bound; lia).
  assert (EX : v ms / 2 ^ drop = (v ms / B ^ words) / 2 ^ shift).
  { rewrite Z.div_div by (pose proof (PBi words Hw); pose proof (Z.pow_pos_nonneg 2 shift ltac:(lia) ltac:(lia)); lia).
    f_equal. rewrite Sw, Z.pow_add_r, Z.pow_mul_r by lia. reflexivity. }
  set (Y := v ms / B ^ words).
  assert (HY : 0 <= Y) by (apply Z.div_pos; [lia | apply PBi; lia]).
  assert (DY : forall k, 0 <= k -> dig Y k = nth (Z.to_nat (k + words)) ms 0).
  { intros k Hk. unfold Y. rewrite dig_div_words by lia. symmetry. apply nth_dig_any; (assumption || lia). }
  assert (Limb : forall i, 0 <= i < 4 -> nth (Z.to_nat i) out 0 = dig (v ms / 2 ^ drop) i).
  { intros i Hi. unfold out.
    replace (nth (Z.to_nat i) (map _ [0; 1; 2; 3]) 0)
      with (let lo := nth (Z.to_nat (i + words)) ms 0 in
            let hi := nth (Z.to_nat (i + words + 1)) ms 0 in
            if shift =? 0 then lo else Z.lor (Z.shiftr lo shift) (u64_shl hi (64 - shift))).
    2: { destruct (Z.eq_dec i 0) as [-> | ]; [reflexivity | ].
         destruct (Z.eq_dec i 1) as [-> | ]; [reflexivity | ].
         destruct (Z.eq_dec i 2) as [-> | ]; [reflexivity | ].
         assert (i = 3) by lia. subst i. reflexivity. }
    cbv zeta. rewrite EX. fold Y.
    rewrite <- (DY i) by lia. replace (i + words + 1) with (i + 1 + words) by ring. rewrite <- (DY (i + 1)) by lia.
    destruct (Z.eqb_spec shift 0) as [B0 | B1].
    - rewrite B0, Z.pow_0_r, Z.div_1_r. reflexivity.
    - rewrite dig_div_bits by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite u64_shl_mul by lia.
      rewrite Z.lor_comm, (lor_low_high (dig Y (i + 1)) (dig Y i / 2 ^ shift) (64 - shift));
        [ring | | lia | apply dig_bound].
      split; [apply Z.div_pos; [apply dig_bound | apply Z.pow_pos_nonneg; lia] | ].
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
      rewrite <- Z.pow_add_r by lia. replace (shift + (64 - shift)) with 64 by ring. apply dig_bound. }
  assert (Lo : length out = 4%nat) by reflexivity.
  assert (Limb' : forall k, (k < 4)%nat -> nth k out 0 = dig (v ms / 2 ^ drop) (Z.of_nat k)).
  { intros k Hk. rewrite <- (Limb (Z.of_nat k)) by lia. rewrite Nat2Z.id. reflexivity. }
  assert (Oo : limbs_ok out).
  { unfold limbs_ok. apply Forall_forall. intros y Hy. apply (In_nth out y 0) in Hy.
    destruct Hy as [k [Hk Ey]]. rewrite Lo in Hk. rewrite <- Ey, Limb' by exact Hk. apply dig_bound. }
  split; [split; assumption | ].
  rewrite <- (Z.mod_small (v ms / 2 ^ drop) (B ^ Z.of_nat (length out))) by (rewrite Lo; exact Hq).
  apply digits_v; [lia | exact Oo | ]. rewrite Lo. exact Limb'.
Qed.

Theorem from_limbs_ok n ms e0 : limbs_ok ms ->
  let r := from_limbs n ms e0 in
  ok4 (m r) /\
  (v ms = 0 -> v (m r) = 0) /\
  (v ms <> 0 -> normalized 256 (v (m r)) /\ neg r = n /\
     (F2R (Float radix2 (v (m r)) (e r)) <= F2R (Float radix2 (v ms) e0))%R /\
     (F2R (Float radix2 (v ms) e0) - F2R (Float radix2 (v (m r)) (e r))
        <= bpow radix2 (-255) * F2R (Float radix2 (v ms) e0))%R).
Proof.
  intros Ok. pose proof (rpos_ok ms Ok) as R. pose proof (v_nonneg ms Ok) as Vn.
  unfold from_limbs. destruct (rpos ms) as [top | ].
  2: { split; [exact ok4_zero | split; [reflexivity | intros H; contradiction]]. }
  destruct R as [Lt [Nz Vt]].
  assert (Nb : 0 < nth top ms 0 < B).
  { pose proof (nth_dig ms top Ok Lt) as D. pose proof (dig_bound (v ms) (Z.of_nat top)).
    assert (0 <= nth top ms 0) by lia. lia. }
  pose proof (v_bounds _ (limbs_ok_firstn top ms Ok)) as Fb.
  rewrite firstn_length, Nat.min_l in Fb by lia.
  (* the bit length *)
  assert (Bits : 64 * Z.of_nat top + 64 - lz64 (nth top ms 0) = Zdigits radix2 (v ms)).
  { rewrite Vt, Zdigits_shift by (try lia; exact Fb). unfold lz64. ring. }
  rewrite Bits. set (D := Zdigits radix2 (v ms)).
  pose proof (Zdigits_correct radix2 (v ms)) as Dc. rewrite Z.abs_eq in Dc by lia.
  change (Zpower radix2 (D - 1)) with (2 ^ (D - 1)) in Dc. change (Zpower radix2 D) with (2 ^ D) in Dc. fold D in Dc.
  assert (Vpos : 0 < v ms).
  { rewrite Vt. pose proof (v_nonneg _ (limbs_ok_firstn top ms Ok)). pose proof (PBi (Z.of_nat top) ltac:(lia)). nia. }
  assert (D1 : 1 <= D) by (pose proof (Zdigits_gt_0 radix2 (v ms) ltac:(lia)); unfold D; lia).
  set (drop := Z.max (D - 256) 0).
  assert (Hd : 0 <= drop) by (unfold drop; lia).
  assert (Pd : 0 < 2 ^ drop) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 0 <= v ms / 2 ^ drop < 2 ^ 256).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]].
    rewrite <- Z.pow_add_r by lia. apply Z.lt_le_trans with (2 ^ D); [exact (proj2 Dc) | apply Z.pow_le_mono_r; unfold drop; lia]. }
  pose proof (window_ok ms drop Ok Hd Q) as W. cbv zeta in W |- *. destruct W as [Wo Wv].
  set (out := map _ [0; 1; 2; 3]) in *.
  pose proof (new_ok n out (e0 + drop) Wo) as [No Ne].
  pose proof (norm_ok 256 ltac:(lia) (v out) (e0 + drop) (v4_bound out Wo)) as NV.
  destruct (norm 256 (v out) (e0 + drop)) as [nm ne] eqn:En. destruct NV as [Nn Nv]. injection Ne as Hm He.
  split; [exact No | split; [intros; lia | intros _]].
  rewrite Hm, He.
  assert (Qpos : 0 < v out).
  { rewrite Wv. apply Z.div_str_pos. split; [lia | ].
    apply Z.le_trans with (2 ^ (D - 1)); [apply Z.pow_le_mono_r; unfold drop; lia | exact (proj1 Dc)]. }
  split; [destruct Nn as [[Z0 _] | Nn]; [lia | exact Nn] | ].
  split.
  { unfold new. rewrite is_zero_ok by apply Wo. destruct (Z.eqb_spec (v out) 0); [lia | reflexivity]. }
  rewrite Nv, Wv.
  (* v ms = q·2^drop + rem, rem < 2^drop <= 2^−255·v ms *)
  pose proof (Z.div_mod (v ms) (2 ^ drop) ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound (v ms) (2 ^ drop) Pd) as Mr.
  set (q := v ms / 2 ^ drop) in *. set (rem := v ms mod 2 ^ drop) in *.
  assert (Ev : F2R (Float radix2 (v ms) e0) = (IZR (2 ^ drop * q + rem) * bpow radix2 e0)%R)
    by (unfold F2R; simpl; rewrite <- Dm; reflexivity).
  assert (Eq : F2R (Float radix2 q (e0 + drop)) = (IZR (2 ^ drop * q) * bpow radix2 e0)%R).
  { unfold F2R; simpl. rewrite mult_IZR, IZR_pow2 by lia. rewrite bpow_plus. ring. }
  pose proof (bpow_gt_0 radix2 e0) as Pe.
  rewrite Ev, Eq. split.
  - apply Rmult_le_compat_r; [lra | apply IZR_le; lia].
  - rewrite <- Rmult_minus_distr_r, <- minus_IZR. replace (2 ^ drop * q + rem - 2 ^ drop * q) with rem by ring.
    rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [lra | ].
    destruct (Z.eq_dec drop 0) as [D0 | D0].
    + (* nothing dropped: no remainder *)
      assert (R0 : rem = 0) by (unfold rem; rewrite D0, Z.pow_0_r, Z.mod_1_r; reflexivity).
      rewrite R0. apply Rmult_le_pos; [apply bpow_ge_0 | apply IZR_le; lia].
    + (* rem < 2^drop <= 2^−255·v ms *)
      assert (Rd : (IZR rem <= IZR (2 ^ drop))%R) by (apply IZR_le; lia).
      apply Rle_trans with (1 := Rd). rewrite IZR_pow2 by lia. rewrite <- Dm.
      replace drop with ((-255) + (drop + 255)) at 1 by ring. rewrite bpow_plus.
      apply Rmult_le_compat_l; [apply bpow_ge_0 | ].
      rewrite <- IZR_pow2 by lia. apply IZR_le. apply Z.le_trans with (2 ^ (D - 1)); [apply Z.pow_le_mono_r; unfold drop in *; lia | exact (proj1 Dc)].
Qed.
