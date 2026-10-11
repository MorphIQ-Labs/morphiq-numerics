(** ln_1p's stage B (docs/ln.md, section 7), transcribed on binary64 as
    crates/morphiq-numerics/src/ln/stages.rs computes it, and proved: for
    [2^-54 <= |x| < 2^-9], [s + lo] is within [137·2^-59·|x|^3 + 263·2^-114·|x|]
    of [ln(1 + x)] (formal/ln/stage_b_small.g); for [2^-9 <= |x|],
    [−1 < x < 2^1020], within [117·2^-86] (formal/ln/stage_b_total.g); and
    [eps] exceeds that, the test's roundings and [2^-123·|ln(1 + x)|]. So when
    the test passes, its result is [RN(ln(1 + x))], and so is the rounding of
    any real within [2^-123] of [ln(1 + x)] relatively ([stage_b_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingTest RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pCertificates Ln1pApprox Ln1pLemmas.
Import ListNotations.

Open Scope R_scope.

(** * Constants *)

Definition st_bc (k : nat) : f64 := b64_of_bits (nth k st_b_bits 0%Z).
Definition c_mhalf : f64 := b64_of_bits 13826050856027422720.   (* -0.5 *)
Definition c_kb : f64 := b64_of_bits 4377498837804122112.       (* K_B = 2^-51 *)
Definition c_ebr : f64 := b64_of_bits 4147815256808226816.      (* EPS_B_REL = 2^-102 *)
Definition c_eb : f64 := b64_of_bits 4255901647865118720.       (* EPS_B = 2^-78 *)
Definition c_two_53 : f64 := b64_of_bits 4845873199050653696.
Definition c_two_m9 : f64 := b64_of_bits 4566650022153682944.

Lemma c_kb_ok : finite c_kb /\ B c_kb = bpow radix2 (-51).
Proof. exact (enc_pow2 (-51) ltac:(lia)). Qed.
Lemma c_ebr_ok : finite c_ebr /\ B c_ebr = bpow radix2 (-102).
Proof. exact (enc_pow2 (-102) ltac:(lia)). Qed.
Lemma c_eb_ok : finite c_eb /\ B c_eb = bpow radix2 (-78).
Proof. exact (enc_pow2 (-78) ltac:(lia)). Qed.
Lemma c_two_53_ok : finite c_two_53 /\ B c_two_53 = bpow radix2 53.
Proof. exact (enc_pow2 53 ltac:(lia)). Qed.
Lemma c_two_m9_ok : finite c_two_m9 /\ B c_two_m9 = bpow radix2 (-9).
Proof. exact (enc_pow2 (-9) ltac:(lia)). Qed.
Lemma c_mhalf_ok : finite c_mhalf /\ B c_mhalf = - bpow radix2 (-1).
Proof.
  destruct (coef_ok 13826050856027422720 (-4503599627370496) (-53) (-1) (-1) eq_refl ltac:(lia) eq_refl) as [F V].
  unfold c_mhalf. split; [exact F | rewrite V]. simpl. ring.
Qed.

Lemma st_b3_ok : finite (st_bc 0) /\ B (st_bc 0) = b3.
Proof. exact (coef_ok (nth 0 st_b_bits 0%Z) 6004799503160661 (-54) 6004799503160661 (-54) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_b4_ok : finite (st_bc 1) /\ B (st_bc 1) = b4.
Proof. exact (coef_ok (nth 1 st_b_bits 0%Z) (-4503599627370496) (-54) (-1) (-2) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_b5_ok : finite (st_bc 2) /\ B (st_bc 2) = b5.
Proof. exact (coef_ok (nth 2 st_b_bits 0%Z) 7205759404466358 (-55) 3602879702233179 (-54) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_b6_ok : finite (st_bc 3) /\ B (st_bc 3) = b6.
Proof. exact (coef_ok (nth 3 st_b_bits 0%Z) (-6004799503343692) (-55) (-1501199875835923) (-53) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_b7_ok : finite (st_bc 4) /\ B (st_bc 4) = b7.
Proof. exact (coef_ok (nth 4 st_b_bits 0%Z) 5146845780597332 (-55) 1286711445149333 (-53) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_b8_ok : finite (st_bc 5) /\ B (st_bc 5) = b8.
Proof. exact (coef_ok (nth 5 st_b_bits 0%Z) (-9007114324328199) (-56) (-9007114324328199) (-56) eq_refl ltac:(lia) eq_refl). Qed.

(** * The transcription *)

(** [B[0] + v·(B[1] + … + v·B[5])], as [horner] evaluates it. *)
Definition b_horner (v : f64) : f64 :=
  let a := fadd (fmul v (st_bc 5)) (st_bc 4) in
  let a := fadd (fmul v a) (st_bc 3) in
  let a := fadd (fmul v a) (st_bc 2) in
  let a := fadd (fmul v a) (st_bc 1) in
  fadd (fmul v a) (st_bc 0).

Definition stage_b_small_parts (x : f64) : f64 * f64 * f64 :=
  let '(p, pl) := two_prod64 x x in
  let m := fmul c_mhalf p in
  let s := fadd x m in
  let e1 := fsub m (fsub s x) in
  let tail := fmul (fmul x p) (b_horner x) in
  let lo := fadd e1 (fadd (fmul c_mhalf pl) tail) in
  let eps := fmul (b64_abs x) (fadd (fmul p c_kb) c_ebr) in
  (s, lo, eps).

(** [e as f64] for the exponent [e]: exact for [|e| < 2^53]. *)
Definition of_int (e : Z) : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE e 0 false.

Definition stage_b_table_parts (x : f64) : f64 * f64 * f64 :=
  let big := match Bcompare 53 1024 x c_two_53 with Some Lt => false | _ => true end in
  let h := if big then x else split_s0 x in
  let l := if big then c_one else split_l x in
  let hb := bits_of_b64 h in
  let e := rd_e hb in
  let i := rd_i hb in
  let rs := rd_rs hb in
  let z := rd_z h in
  let lr := fmul l rs in
  let ef := of_int e in
  let ln1 := fadd (fmul ef st_l1) (st_th i) in
  let ln0 := fadd (fmul ef st_l0) (st_tl i) in
  let '(p, pl) := two_prod64 z z in
  let s1 := fadd ln1 z in
  let e1 := fsub z (fsub s1 ln1) in
  let m := fmul c_mhalf p in
  let s := fadd s1 m in
  let e2 := fsub m (fsub s s1) in
  let zp := fmul z p in
  let tail := fmul zp (b_horner z) in
  let lrt := fmul lr (fsub (fadd (fsub c_one z) p) zp) in
  let lo := fadd (fadd e1 e2) (fadd (fadd ln0 lrt) (fadd (fmul c_mhalf pl) tail)) in
  (s, lo, c_eb).

Definition stage_b_parts (x : f64) : f64 * f64 * f64 :=
  match Bcompare 53 1024 (b64_abs x) c_two_m9 with
  | Some Lt => stage_b_small_parts x
  | _ => stage_b_table_parts x
  end.

Definition stage_b (x : f64) : option f64 :=
  let '(s, lo, eps) := stage_b_parts x in decide s lo eps.

(** * The small-argument branch, over reals *)

Lemma b_small_compose v x p pl s e1 m tail w lo eps W al be d1 d2 da db :
  v = x - x * x / 2 + x * x * x * W + x * x * x * al ->
  bpow radix2 (-54) <= Rabs x <= bpow radix2 (-9) ->
  p + pl = x * x -> Rabs (p - x * x) <= bpow radix2 (-53) * (x * x) ->
  m = - (p / 2) -> s + e1 = x + m -> Rabs e1 <= bpow radix2 (-53) * Rabs s ->
  tail = x * x * x * (W + be) -> w = (- (pl / 2) + tail) * (1 + d1) -> lo = (e1 + w) * (1 + d2) ->
  IZR (-691) * bpow radix2 (-65) <= al <= IZR 691 * bpow radix2 (-65) ->
  IZR (-655) * bpow radix2 (-62) <= be <= IZR 655 * bpow radix2 (-62) ->
  IZR 681 * bpow radix2 (-11) <= W <= IZR 171 * bpow radix2 (-9) ->
  Rabs d1 <= bpow radix2 (-53) -> Rabs d2 <= bpow radix2 (-53) ->
  Rabs da <= bpow radix2 (-53) -> Rabs db <= bpow radix2 (-53) ->
  eps = Rabs x * ((p * bpow radix2 (-51) + bpow radix2 (-102)) * (1 + da)) * (1 + db) ->
  0 <= eps /\ Rabs lo + eps <= 1 /\
  forall w0, Rabs (w0 - v) <= / 2 ^ 123 * Rabs v -> Rabs (w0 - (s + lo)) + bpow radix2 (-53) * (Rabs lo + eps) <= eps.
Proof.
  intros Hv Hx Hp Hpr Hm Hs He1 Ht Hw Hlo Hal Hbe HW Hd1 Hd2 Hda Hdb Heps.
  assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  rewrite U in Hpr, He1, Hd1, Hd2, Hda, Hdb.
  set (X := Rabs x). assert (X0 : 0 < X) by (unfold X; pose proof (bpow_gt_0 radix2 (-54)); lra).
  assert (Xn : x <> 0) by (intros Z; unfold X in X0; rewrite Z, Rabs_R0 in X0; lra).
  assert (Xs : X <= / 512) by (destruct Hx as [_ H]; change (bpow radix2 (-9)) with (/ 512) in H; exact H).
  assert (X2 : x * x = X * X) by (unfold X; rewrite <- Rabs_mult, Rabs_pos_eq by apply Rle_0_sqr; reflexivity).
  set (pi := pl / (x * x)). set (eta := e1 / x).
  assert (Hpi : Rabs pi <= / 9007199254740992).
  { assert (Pxx : 0 < x * x) by exact (Rsqr_pos_lt x Xn).
    unfold pi. replace pl with (- (p - x * x)) by lra. unfold Rdiv.
    rewrite Rabs_mult, Rabs_Ropp, Rabs_Rinv by lra.
    rewrite (Rabs_pos_eq (x * x)) by lra. apply Rmult_le_reg_r with (x * x); [lra | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact Hpr. }
  (* |s| <= 2 |x|, so |eta| <= 2^-53 (1 + 2^-9) *)
  assert (Hsx : Rabs s <= X * (1 + / 512) + Rabs e1).
  { replace s with (x + m - e1) by lra. rewrite Hm.
    apply Rle_trans with (Rabs x + Rabs (p / 2) + Rabs e1).
    - unfold Rminus. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
      apply Rplus_le_compat_r. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra.
    - assert (Rabs (p / 2) <= X * / 512).
      { unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra.
        assert (Rabs p <= X * X * (1 + / 9007199254740992)).
        { apply Rabs_le_inv in Hpr. rewrite X2 in Hpr. apply Rabs_le. nra. }
        nra. }
      fold X. lra. }
  assert (Heta : Rabs eta <= IZR 519 * bpow radix2 (-62)).
  { unfold eta, Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Xn. fold X. apply Rmult_le_reg_r with X; [lra | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    assert (Rabs e1 <= / 9007199254740992 * (X * (1 + / 512) + Rabs e1)) by (apply Rle_trans with (1 := He1); apply Rmult_le_compat_l; lra).
    bpow_num. nra. }
  assert (R53 : forall d, Rabs d <= / 9007199254740992 -> IZR (-1) * bpow radix2 (-53) <= d <= IZR 1 * bpow radix2 (-53)).
  { intros d Hd. apply (rng_abs d 1). rewrite Rmult_1_l, U. exact Hd. }
  destruct (stage_b_small al be W pi eta x d1 d2 Hal Hbe HW
              (rng_abs pi 259 (-61) ltac:(bpow_num; lra)) (rng_abs eta 519 (-62) Heta)
              ltac:(split; apply Rabs_le_inv in Xs; bpow_num; lra) (R53 d1 Hd1) (R53 d2 Hd2)) as [G3 G1].
  apply abs_rng in G3. apply abs_rng in G1.
  set (Gx3 := al - be - d1 * (W + be) - d2 * (1 + d1) * (W + be)) in *.
  set (Gx1 := x * (d1 + d2 * (1 + d1)) * pi / 2 - d2 * eta) in *.
  assert (Id : v - (s + lo) = x * x * x * Gx3 + x * Gx1).
  { unfold Gx3, Gx1, pi, eta. rewrite Hv, Hlo, Hw, Ht.
    replace s with (x + m - e1) by lra. rewrite Hm. replace p with (x * x - pl) by lra.
    field. exact Xn. }
  set (X3 := X * X * X).
  assert (X3e : Rabs (x * x * x) = X3) by (unfold X3, X; rewrite !Rabs_mult; reflexivity).
  assert (XXs : X * X <= X * / 512) by (apply Rmult_le_compat_l; lra).
  assert (X3s : X3 <= X * / 262144).
  { unfold X3. apply Rle_trans with (X * / 512 * X); [apply Rmult_le_compat_r; lra | ].
    replace (X * / 512 * X) with (X * X * / 512) by ring. apply Rle_trans with (X * / 512 * / 512); [apply Rmult_le_compat_r; lra | lra]. }
  assert (Err : Rabs (v - (s + lo)) <= X3 * (IZR 137 * bpow radix2 (-59)) + X * (IZR 263 * bpow radix2 (-114))).
  { rewrite Id. apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite (Rabs_mult (x * x * x) Gx3), (Rabs_mult x Gx1), X3e. fold X.
    apply Rplus_le_compat; apply Rmult_le_compat_l; try assumption; try lra.
    unfold X3; repeat apply Rmult_le_pos; lra. }
  bpow_num_in Err. bpow_num_in HW. bpow_num_in Hbe.
  (* |lo| *)
  apply Rabs_le_inv in Hd1. apply Rabs_le_inv in Hd2. apply Rabs_le_inv in Hda. apply Rabs_le_inv in Hdb.
  assert (Atail : Rabs tail <= X3 * (171 / 512 + 655 / 4611686018427387904)).
  { rewrite Ht, Rabs_mult, X3e. apply Rmult_le_compat_l; [unfold X3; nra | apply Rabs_le; lra]. }
  assert (Apl : Rabs pl <= X * X * / 9007199254740992).
  { replace pl with (- (p - x * x)) by lra. rewrite Rabs_Ropp, <- X2. lra. }
  assert (Ae1 : Rabs e1 <= X * (519 / 4611686018427387904)).
  { replace e1 with (x * eta) by (unfold eta; field; exact Xn). rewrite Rabs_mult. fold X.
    apply Rmult_le_compat_l; [lra | bpow_num_in Heta; lra]. }
  assert (Aw : Rabs w <= (X * X * / 9007199254740992 / 2 + X3 * (171 / 512 + 655 / 4611686018427387904)) * (1 + / 9007199254740992)).
  { rewrite Hw, Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    - apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. lra.
    - apply Rabs_le. lra. }
  assert (Alo : Rabs lo <= (X * (519 / 4611686018427387904) + (X * X * / 9007199254740992 / 2 + X3 * (171 / 512 + 655 / 4611686018427387904)) * (1 + / 9007199254740992)) * (1 + / 9007199254740992)).
  { rewrite Hlo, Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    - apply Rle_trans with (1 := Rabs_triang _ _). lra.
    - apply Rabs_le. lra. }
  assert (XX : X * X <= X * / 512) by nra.
  (* eps *)
  assert (B51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
  assert (B102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
  rewrite B51, B102 in Heps.
  assert (Plo : X * X * (1 - / 9007199254740992) <= p) by (apply Rabs_le_inv in Hpr; rewrite X2 in Hpr; lra).
  assert (Phi : p <= X * X * (1 + / 9007199254740992)) by (apply Rabs_le_inv in Hpr; rewrite X2 in Hpr; lra).
  set (I1 := p * / 2251799813685248 + / 5070602400912917605986812821504).
  assert (I1p : 0 <= I1) by (unfold I1; assert (0 <= X * X) by nra; nra).
  set (I2 := I1 * (1 + da)).
  assert (I2lo : I1 * (1 - / 9007199254740992) <= I2) by (apply Rmult_le_compat_l; lra).
  assert (I2hi : I2 <= I1 * (1 + / 9007199254740992)) by (apply Rmult_le_compat_l; lra).
  assert (I2p : 0 <= I2) by lra.
  change (Rabs x) with X in Heps. fold I1 in Heps. fold I2 in Heps.
  assert (Elo : X * I2 * (1 - / 9007199254740992) <= eps) by (rewrite Heps; apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra]).
  assert (Ehi : eps <= X * I2 * (1 + / 9007199254740992)) by (rewrite Heps; apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | lra]).
  (* in X3 and X *)
  assert (E3lo : X3 * / 2251799813685248 * (1 - / 9007199254740992) ^ 3 + X * / 5070602400912917605986812821504 * (1 - / 9007199254740992) ^ 2 <= eps).
  { apply Rle_trans with (2 := Elo). unfold X3. unfold I1 in I2lo. simpl. nra. }
  assert (E3hi : eps <= X3 * / 2251799813685248 * (1 + / 9007199254740992) ^ 3 + X * / 5070602400912917605986812821504 * (1 + / 9007199254740992) ^ 2).
  { apply Rle_trans with (1 := Ehi). unfold X3. unfold I1 in I2hi. simpl. nra. }
  simpl in E3lo, E3hi.
  assert (X3p : 0 <= X3) by (unfold X3; nra).
  split; [lra | ]. split; [lra | ].
  intros w0 Hw0.
  assert (Av : Rabs v <= Rabs s + Rabs lo + Rabs (v - (s + lo))).
  { replace v with (s + lo + (v - (s + lo))) at 1 by ring. apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat_r. apply Rabs_triang. }
  assert (Aw0 : Rabs (w0 - (s + lo)) <= Rabs (w0 - v) + Rabs (v - (s + lo))).
  { replace (w0 - (s + lo)) with ((w0 - v) + (v - (s + lo))) by ring. apply Rabs_triang. }
  assert (P123 : 0 < / 2 ^ 123 <= / 10633823966279326983230456482242756608) by (split; [apply Rinv_0_lt_compat, pow_lt; lra | simpl; lra]).
  assert (Hw0' : Rabs (w0 - v) <= / 10633823966279326983230456482242756608 * Rabs v) by (pose proof (Rabs_pos v); nra).
  bpow_num. lra.
Qed.

(** * The table branch, over reals *)

Lemma b_table_compose v N ln1 ln0 z L s1 e1 m s e2 p pl lo W ap u t6 g :
  v = N + (z - z * z / 2 + z * z * z * W + ap) + (u + t6) -> u = L / (1 + z) ->
  Rabs z <= / 512 ->
  s1 + e1 = ln1 + z -> m = - (p / 2) -> s + e2 = s1 + m -> p + pl = z * z ->
  g = lo - (e1 + e2 + ln0 + L * (1 - z + z * z - z * z * z) - pl / 2 + z * z * z * W) ->
  IZR (-533) * bpow radix2 (-95) <= N - ln1 - ln0 <= IZR 533 * bpow radix2 (-95) ->
  IZR (-349) * bpow radix2 (-91) <= ap <= IZR 349 * bpow radix2 (-91) ->
  IZR (-263) * bpow radix2 (-97) <= u + t6 - L * (1 - z + z * z - z * z * z) <= IZR 263 * bpow radix2 (-97) ->
  IZR (-415) * bpow radix2 (-88) <= g <= IZR 415 * bpow radix2 (-88) ->
  Rabs lo <= bpow radix2 (-28) -> Rabs s <= 1024 ->
  0 <= bpow radix2 (-78) /\ Rabs lo + bpow radix2 (-78) <= 1 /\
  forall w0, Rabs (w0 - v) <= / 2 ^ 123 * Rabs v ->
    Rabs (w0 - (s + lo)) + bpow radix2 (-53) * (Rabs lo + bpow radix2 (-78)) <= bpow radix2 (-78).
Proof.
  intros Hv Hu Hz He1 Hm He2 Hp Hg Ht1 Hap Hlt Hgr Hlo Hs.
  assert (Z1 : 1 + z <> 0) by (apply Rabs_le_inv in Hz; lra).
  assert (Id : v - (s + lo) = (N - ln1 - ln0) + ap + (u + t6 - L * (1 - z + z * z - z * z * z)) - g).
  { rewrite Hv, Hg. replace s with (s1 + m - e2) by lra. rewrite Hm. replace p with (z * z - pl) by lra.
    replace s1 with (ln1 + z - e1) by lra. field. }
  pose proof (stage_b_total _ _ _ _ Ht1 Hap Hlt Hgr) as T. apply abs_rng in T.
  replace (N - ln1 - ln0 + ap + (u + t6 - L * (1 - z + z * z - z * z * z)) - g) with (v - (s + lo)) in T by (rewrite Id; ring).
  bpow_num_in T. bpow_num_in Hlo. bpow_num.
  split; [lra | ]. split; [lra | ].
  intros w0 Hw0.
  assert (Av : Rabs v <= Rabs s + Rabs lo + Rabs (v - (s + lo))).
  { replace v with (s + lo + (v - (s + lo))) at 1 by ring. apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat_r. apply Rabs_triang. }
  assert (Aw0 : Rabs (w0 - (s + lo)) <= Rabs (w0 - v) + Rabs (v - (s + lo))).
  { replace (w0 - (s + lo)) with ((w0 - v) + (v - (s + lo))) by ring. apply Rabs_triang. }
  assert (P123 : 0 < / 2 ^ 123 <= / 10633823966279326983230456482242756608) by (split; [apply Rinv_0_lt_compat, pow_lt; lra | simpl; lra]).
  assert (Hw0' : Rabs (w0 - v) <= / 10633823966279326983230456482242756608 * Rabs v) by (pose proof (Rabs_pos v); nra).
  lra.
Qed.
