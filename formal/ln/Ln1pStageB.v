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

(** The table branch after the split [1 + x = h + l]. *)
Definition stage_b_core (h l : f64) : f64 * f64 * f64 :=
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

Definition stage_b_table_parts (x : f64) : f64 * f64 * f64 :=
  let big := match Bcompare 53 1024 x c_two_53 with Some Lt => false | _ => true end in
  let h := if big then x else split_s0 x in
  let l := if big then c_one else split_l x in
  stage_b_core h l.

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

(** * The small-argument branch *)

Lemma b_horner_val v : finite v -> Rabs (B v) <= / 512 ->
  finite (b_horner v) /\ B (b_horner v) = b_w (B v) /\ Rabs (B (b_horner v)) <= 1.
Proof.
  intros Fv Hv.
  destruct st_b3_ok as [F3 B3]. destruct st_b4_ok as [F4 B4]. destruct st_b5_ok as [F5 B5].
  destruct st_b6_ok as [F6 B6]. destruct st_b7_ok as [F7 B7]. destruct st_b8_ok as [F8 B8].
  assert (Hb : Rabs b3 <= / 2 /\ Rabs b4 <= / 2 /\ Rabs b5 <= / 2 /\ Rabs b6 <= / 2 /\ Rabs b7 <= / 2 /\ Rabs b8 <= / 2).
  { unfold b3, b4, b5, b6, b7, b8. bpow_num. repeat split; apply Rabs_le; lra. }
  destruct Hb as [A3 [A4 [A5 [A6 [A7 A8]]]]].
  assert (One : fmtF 1) by (apply (fmt_pow 0); lia).
  assert (Small : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1000)
    by (intros u Hu; apply Rle_trans with 2; [exact Hu | change 2 with (bpow radix2 1); apply bpow_le; lia]).
  assert (Mul : forall a b, Rabs a <= / 512 -> Rabs b <= 1 -> Rabs (a * b) <= / 512)
    by (intros a b Ha Hb'; rewrite Rabs_mult; apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]).
  assert (Step : forall a c, finite a -> finite c -> Rabs (B a) <= 1 -> Rabs (B c) <= / 2 ->
            finite (fadd (fmul v a) c) /\ B (fadd (fmul v a) c) = rndF (rndF (B v * B a) + B c) /\ Rabs (B (fadd (fmul v a) c)) <= 1).
  { intros a c Fa Fc Ha Hc.
    destruct (fmul_s v a Fv Fa) as [F1 V1]; [apply Small; pose proof (Mul _ _ Hv Ha); lra | ].
    assert (A1 : Rabs (B (fmul v a)) <= / 512) by (rewrite V1; apply rnd_bound; [apply (fmt_pow (-9)); lia | change (bpow radix2 (-9)) with (/ 512); apply Mul; assumption]).
    destruct (fadd_s (fmul v a) c F1 Fc) as [F2 V2]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
    split; [exact F2 | split; [rewrite V2, V1; reflexivity | ]].
    rewrite V2. apply rnd_bound; [exact One | apply Rle_trans with (1 := Rabs_triang _ _); lra]. }
  unfold b_horner.
  destruct (Step (st_bc 5) (st_bc 4) F8 F7 ltac:(rewrite B8; lra) ltac:(rewrite B7; lra)) as [G1 [W1 A1]].
  destruct (Step _ (st_bc 3) G1 F6 A1 ltac:(rewrite B6; lra)) as [G2 [W2 A2]].
  destruct (Step _ (st_bc 2) G2 F5 A2 ltac:(rewrite B5; lra)) as [G3 [W3 A3']].
  destruct (Step _ (st_bc 1) G3 F4 A3' ltac:(rewrite B4; lra)) as [G4 [W4 A4']].
  destruct (Step _ (st_bc 0) G4 F3 A4' ltac:(rewrite B3; lra)) as [G5 [W5 A5']].
  split; [exact G5 | split; [ | exact A5']].
  rewrite W5, W4, W3, W2, W1, B3, B4, B5, B6, B7, B8. unfold b_w. cbv zeta.
  change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
  reflexivity.
Qed.

Theorem stage_b_small_eval x : finite x -> bpow radix2 (-54) <= Rabs (B x) < bpow radix2 (-9) ->
  let '(s, lo, eps) := stage_b_small_parts x in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fx [Hx1 Hx2].
  set (X := Rabs (B x)) in *.
  assert (X0 : 0 < X) by (pose proof (bpow_gt_0 radix2 (-54)); lra).
  assert (Xs : X <= / 512) by (change (/ 512) with (bpow radix2 (-9)); lra).
  assert (Xn : B x <> 0) by (intros Z; unfold X in X0; rewrite Z, Rabs_R0 in X0; lra).
  assert (Small : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1000)
    by (intros u Hu; apply Rle_trans with 2; [exact Hu | change 2 with (bpow radix2 1); apply bpow_le; lia]).
  assert (One : fmtF 1) by (apply (fmt_pow 0); lia).
  (* p + pl = x^2 *)
  assert (Dom : in_two_prod_domain (B x) (B x)).
  { right. rewrite Rabs_mult. fold X. apply Rle_trans with (bpow radix2 (-54) * bpow radix2 (-54)).
    - rewrite <- bpow_plus. apply bpow_le. lia.
    - apply Rmult_le_compat; try apply bpow_ge_0; lra. }
  pose proof (two_prod_ieee 0 0 x x Fx Fx ltac:(change (bpow radix2 0) with 1; fold X; lra) ltac:(change (bpow radix2 0) with 1; fold X; lra)
                ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  unfold stage_b_small_parts. destruct (two_prod64 x x) as [p pl]. destruct TP as [Fp [Fpl [Bp Bppl]]].
  cbv zeta.
  assert (XX : B x * B x = X * X) by (unfold X; rewrite <- Rabs_mult, Rabs_pos_eq by apply Rle_0_sqr; reflexivity).
  assert (Xb : bpow radix2 (-108) <= X * X).
  { apply Rle_trans with (bpow radix2 (-54) * bpow radix2 (-54)); [rewrite <- bpow_plus; apply bpow_le; lia | apply Rmult_le_compat; try apply bpow_ge_0; lra]. }
  assert (Prel : Rabs (B p - B x * B x) <= bpow radix2 (-53) * (B x * B x)).
  { rewrite Bp. pose proof (rnd_rel (B x * B x)) as RZ. rewrite (Rabs_pos_eq (B x * B x)) in RZ by apply Rle_0_sqr.
    apply RZ. rewrite XX. apply Rle_trans with (2 := Xb). apply bpow_le. lia. }
  assert (Pp : bpow radix2 (-108) <= Rabs (B p)).
  { rewrite Bp. apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-108)); lia | ]. rewrite XX, Rabs_pos_eq by nra. exact Xb. }
  assert (Ap : Rabs (B p) <= / 262144).
  { rewrite Bp. apply rnd_bound; [apply (fmt_pow (-18)); lia | ]. change (bpow radix2 (-18)) with (/ 262144).
    rewrite XX, Rabs_pos_eq by nra. assert (X * X <= / 512 * / 512) by (apply Rmult_le_compat; lra). lra. }
  (* m = -p/2, exactly *)
  destruct c_mhalf_ok as [Fmh Bmh].
  destruct (fmul_s c_mhalf p Fmh Fp) as [Fm Bm]; [apply Small; rewrite Bmh; change (bpow radix2 (-1)) with (/ 2); rewrite Rabs_mult, Rabs_Ropp, Rabs_pos_eq by lra; lra | ].
  rewrite Bmh in Bm. replace (- bpow radix2 (-1) * B p) with ((- B p) * bpow radix2 (-1)) in Bm by ring.
  rewrite (rnd_scale (- B p) (-1) (-108) (generic_format_opp _ _ _ (B_fmt p)) ltac:(right; rewrite Rabs_Ropp; exact Pp) ltac:(lia)) in Bm.
  set (m := fmul c_mhalf p) in *.
  assert (Bm' : B m = - (B p / 2)) by (rewrite Bm; change (bpow radix2 (-1)) with (/ 2); unfold Rdiv; ring).
  (* s, e1 by Fast2Sum *)
  assert (XX2 : X * X <= X * / 512) by (apply Rmult_le_compat_l; lra).
  assert (Apx : Rabs (B p) <= X * X * 2).
  { apply Rabs_le_inv in Prel. rewrite XX in Prel. bpow_num_in Prel. pose proof (Rle_0_sqr X). unfold Rsqr in *. apply Rabs_le. lra. }
  assert (Am : Rabs (B m) <= / 512 * Rabs (B x)).
  { rewrite Bm', Rabs_Ropp. unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. fold X. lra. }
  pose proof (fast_two_sum_ieee x m Fx Fm
               ltac:(apply Rle_trans with 1; [fold X; lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(apply Rle_trans with 1; [fold X in Am; lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(right; left; fold X in Am |- *; lra)) as FT.
  unfold fast_two_sum64 in FT. cbv beta iota zeta in FT. destruct FT as [Fs [Fe1 [Bs Se1]]].
  set (s := fadd x m) in *. set (e1 := fsub m (fsub s x)) in *.
  assert (Sx : X / 2 <= Rabs (B x + B m)).
  { pose proof (Rabs_triang_inv (B x) (- B m)) as T. replace (B x - - B m) with (B x + B m) in T by ring.
    rewrite Rabs_Ropp in T. fold X in T, Am. lra. }
  assert (Slo : bpow radix2 (-56) <= Rabs (B s)).
  { rewrite Bs. apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-56)); lia | ].
    apply Rle_trans with (2 := Sx). assert (bpow radix2 (-54) = 4 * bpow radix2 (-56)) by (change 4 with (bpow radix2 2); rewrite <- bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 (-56)). fold X in Hx1. lra. }
  assert (He1 : Rabs (B e1) <= bpow radix2 (-53) * Rabs (B s)).
  { pose proof (rnd_err_out (B x + B m)) as R1. rewrite <- Bs in R1.
    specialize (R1 (Rle_trans _ _ _ (bpow_le radix2 (-1022) (-56) ltac:(lia)) Slo)).
    replace (B e1) with (- (B s - (B x + B m))) by lra. rewrite Rabs_Ropp. exact R1. }
  (* the tail *)
  assert (Xb9 : Rabs (B x) <= / 512) by (fold X; lra).
  destruct (b_horner_val x Fx Xb9) as [Fh [Bh Ah]].
  destruct (fmul_s x p Fx Fp) as [Fxp Bxp]; [apply Small; rewrite Rabs_mult; fold X; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra] | ].
  assert (Axp : Rabs (B (fmul x p)) <= 1) by (rewrite Bxp; apply rnd_bound; [exact One | rewrite Rabs_mult; fold X; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]]).
  destruct (fmul_s (fmul x p) (b_horner x) Fxp Fh) as [Ft Bt]; [apply Small; rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra] | ].
  set (tail := fmul (fmul x p) (b_horner x)) in *.
  assert (Tq : B tail = rn (rn (B x * rn (B x * B x)) * b_w (B x))).
  { rewrite Bt, Bxp, Bh, Bp.
    change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
    reflexivity. }
  destruct (stage_b_small_tail (B x) ltac:(fold X; split; [rewrite Rmult_1_l; exact Hx1 | rewrite Rmult_1_l; lra])) as [Tb Wb].
  rewrite <- Tq in Tb.
  set (W := b_W (B x)) in *.
  set (be := (B tail - B x * B x * B x * W) / (B x * B x * B x)).
  assert (X3n : B x * B x * B x <> 0) by (repeat apply Rmult_integral_contrapositive_currified; exact Xn).
  assert (Htail : B tail = B x * B x * B x * (W + be)) by (unfold be; field; exact Xn).
  (* -pl/2, exactly *)
  assert (Gpl : on_grid (-212) (B pl)).
  { assert (Gx : on_grid (-106) (B x)).
    { apply (grid_le (cexp radix2 (FLT_exp emin prec) (B x))); [ | apply grid_fmt, B_fmt].
      unfold cexp, FLT_exp, emin, prec. assert (-53 <= mag radix2 (B x))%Z by (apply mag_ge_bpow; fold X; apply Rle_trans with (2 := Hx1); apply bpow_le; lia). lia. }
    assert (Gxx : on_grid (-212) (B x * B x)) by (replace (-212)%Z with (-106 + -106)%Z by reflexivity; apply grid_mult; exact Gx).
    replace (B pl) with (B x * B x - B p) by lra. apply grid_minus; [exact Gxx | rewrite Bp; apply grid_round; [exact _ | exact _ | exact Gxx]]. }
  destruct (fmul_s c_mhalf pl Fmh Fpl) as [Fmpl Bmpl].
  { apply Small. rewrite Bmh, Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (bpow radix2 (-1))) by apply bpow_ge_0.
    replace (B pl) with (B x * B x - B p) by lra. change (bpow radix2 (-1)) with (/ 2).
    assert (Rabs (B x * B x - B p) <= 1) by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp, XX, Rabs_pos_eq by nra; lra). lra. }
  rewrite Bmh in Bmpl. replace (- bpow radix2 (-1) * B pl) with ((- B pl) * bpow radix2 (-1)) in Bmpl by ring.
  rewrite (rnd_scale (- B pl) (-1) (-212) (generic_format_opp _ _ _ (B_fmt pl))) in Bmpl.
  2: { destruct (Req_dec (B pl) 0) as [Z | N]; [left; rewrite Z; ring | right; rewrite Rabs_Ropp; apply grid_nonzero; assumption]. }
  2: lia.
  set (mpl := fmul c_mhalf pl) in *.
  assert (Bmpl' : B mpl = - (B pl / 2)) by (rewrite Bmpl; change (bpow radix2 (-1)) with (/ 2); unfold Rdiv; ring).
  (* w, lo *)
  assert (Apl : Rabs (B pl) <= 1) by (replace (B pl) with (B x * B x - B p) by lra; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp, XX, Rabs_pos_eq by nra; lra).
  assert (At : Rabs (B tail) <= 1) by (rewrite Bt; apply rnd_bound; [exact One | rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]]).
  destruct (rnd_sum_rel (B mpl) (B tail) (B_fmt _) (B_fmt _)) as [d1 [Hd1 Ed1]].
  destruct (fadd_s mpl tail Fmpl Ft) as [Fw Bw]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Bmpl', Rabs_Ropp; unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra; lra | ].
  rewrite Ed1, Bmpl' in Bw. set (w := fadd mpl tail) in *.
  assert (Aw : Rabs (B w) <= 4) by (rewrite Bw, Rabs_mult; apply Rle_trans with (2 * 2); [apply Rmult_le_compat; try apply Rabs_pos;
    [apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra; lra
    | apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_R1; bpow_num_in Hd1; lra] | lra]).
  assert (Ae1 : Rabs (B e1) <= 1) by (apply Rle_trans with (1 := He1); assert (Rabs (B s) <= 2) by (rewrite Bs; apply rnd_bound; [apply (fmt_pow 1); lia | change (bpow radix2 1) with 2; apply Rle_trans with (1 := Rabs_triang _ _); fold X in Am; lra]); bpow_num; lra).
  destruct (rnd_sum_rel (B e1) (B w) (B_fmt _) (B_fmt _)) as [d2 [Hd2 Ed2]].
  destruct (fadd_s e1 w Fe1 Fw) as [Flo Blo]; [apply Rle_trans with 5; [apply Rle_trans with (1 := Rabs_triang _ _); lra | change 5 with (IZR 5); apply Rle_trans with (bpow radix2 3); [simpl; lra | apply bpow_le; lia]] | ].
  rewrite Ed2 in Blo. set (lo := fadd e1 w) in *.
  (* eps *)
  destruct c_kb_ok as [Fkb Bkb]. destruct c_ebr_ok as [Febr Bebr].
  destruct (fmul_s p c_kb Fp Fkb) as [Fk Bk]; [apply Small; rewrite Bkb, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-51))) by apply bpow_ge_0; bpow_num; lra | ].
  rewrite Bkb, (rnd_scale (B p) (-51) (-108) (B_fmt p) ltac:(right; exact Pp) ltac:(lia)) in Bk.
  destruct (rnd_sum_rel (B p * bpow radix2 (-51)) (bpow radix2 (-102)) ltac:(rewrite <- Bk; apply B_fmt) (fmt_pow (-102) ltac:(lia))) as [da [Hda Eda]].
  destruct (fadd_s (fmul p c_kb) c_ebr Fk Febr) as [Fi Bi]; [apply Small; rewrite Bk, Bebr; bpow_num; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_mult, (Rabs_pos_eq (/ IZR 2251799813685248)), (Rabs_pos_eq (/ IZR 5070602400912917605986812821504)) by lra; lra | ].
  rewrite Bk, Bebr, Eda in Bi.
  pose proof (is_finite_Babs 53 1024 unop_nan_pl64 x) as Fax. fold (b64_abs x) in Fax. rewrite Fx in Fax.
  assert (Bax : B (b64_abs x) = X) by apply B_abs.
  set (I2 := (B p * bpow radix2 (-51) + bpow radix2 (-102)) * (1 + da)) in *.
  assert (I2b : 0 <= I2 <= 1).
  { unfold I2. apply Rabs_le_inv in Hda. bpow_num_in Hda. bpow_num.
    assert (0 <= B p) by (rewrite Bp; apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | apply Rle_0_sqr]).
    apply Rabs_le_inv in Ap. split; [apply Rmult_le_pos; [apply Rplus_le_le_0_compat; [apply Rmult_le_pos; lra | lra] | lra] | ].
    apply Rle_trans with ((/ 262144 * / 2251799813685248 + / 5070602400912917605986812821504) * 2); [ | lra].
    apply Rmult_le_compat; [apply Rplus_le_le_0_compat; [apply Rmult_le_pos; lra | lra] | lra | | lra].
    apply Rplus_le_compat_r. apply Rmult_le_compat_r; lra. }
  assert (XIl : bpow radix2 (-1022) <= Rabs (X * I2)).
  { rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
    assert (I2l : bpow radix2 (-104) <= I2).
    { unfold I2. apply Rabs_le_inv in Hda.
      assert (0 <= B p) by (rewrite Bp; apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | apply Rle_0_sqr]).
      assert (B0 : bpow radix2 (-102) <= B p * bpow radix2 (-51) + bpow radix2 (-102)) by (pose proof (bpow_ge_0 radix2 (-51)); nra).
      apply Rle_trans with (bpow radix2 (-102) * (1 - bpow radix2 (-53))).
      - bpow_num. lra.
      - assert (bpow radix2 (-53) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
        pose proof (bpow_ge_0 radix2 (-102)). apply Rmult_le_compat; lra. }
    apply Rle_trans with (bpow radix2 (-54) * bpow radix2 (-104)).
    - rewrite <- bpow_plus. apply bpow_le. lia.
    - apply Rmult_le_compat; try apply bpow_ge_0; [fold X in Hx1; lra | exact I2l]. }
  destruct (fmul_s (b64_abs x) (fadd (fmul p c_kb) c_ebr) Fax Fi) as [Fe Be].
  { apply Small. rewrite Bax, Bi. fold I2. rewrite Rabs_mult, Rabs_pos_eq, Rabs_pos_eq by lra.
    apply Rle_trans with (1 * 1); [apply Rmult_le_compat; lra | lra]. }
  rewrite Bax, Bi in Be. fold I2 in Be.
  pose proof (rnd_rel (X * I2) XIl) as RX.
  change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) (X * I2)) with (rndF (X * I2)) in RX.
  assert (XIn : X * I2 <> 0) by (intros Z; rewrite Z, Rabs_R0 in XIl; pose proof (bpow_gt_0 radix2 (-1022)); lra).
  set (db := (rndF (X * I2) - X * I2) / (X * I2)).
  assert (Hdb : Rabs db <= bpow radix2 (-53)).
  { unfold db, Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact XIn. apply Rmult_le_reg_r with (Rabs (X * I2)); [apply Rabs_pos_lt, XIn | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, XIn). exact RX. }
  assert (Be' : B (fmul (b64_abs x) (fadd (fmul p c_kb) c_ebr)) = X * I2 * (1 + db)) by (rewrite Be; unfold db; field; split; intros Z; apply XIn; rewrite Z; ring).
  set (eps := fmul (b64_abs x) (fadd (fmul p c_kb) c_ebr)) in *.
  (* ln(1 + x) *)
  pose proof (b_approx (B x) ltac:(simpl; lra)) as BA. fold W in BA.
  set (al := (ln (1 + B x) - B x + B x * B x / 2 - B x * B x * B x * W) / (B x * B x * B x)).
  assert (X3a : Rabs (B x * B x * B x) = X * X * X) by (unfold X; rewrite !Rabs_mult; reflexivity).
  assert (Hal : Rabs al <= IZR 691 * bpow radix2 (-65)).
  { unfold al. apply ratio_bound; [rewrite X3a; repeat apply Rmult_lt_0_compat; lra | ].
    apply Rle_trans with (1 := BA). bpow_num. lra. }
  destruct (b_small_compose (ln (1 + B x)) (B x) (B p) (B pl) (B s) (B e1) (B m) (B tail) (B w) (B lo) (B eps) W al be d1 d2 da db)
    as [Ep [Lo1 Main]].
  - unfold al. field. exact Xn.
  - fold X. split; lra.
  - exact Bppl.
  - exact Prel.
  - exact Bm'.
  - exact Se1.
  - exact He1.
  - exact Htail.
  - exact Bw.
  - exact Blo.
  - apply rng_abs. exact Hal.
  - exact Tb.
  - exact Wb.
  - exact Hd1.
  - exact Hd2.
  - exact Hda.
  - exact Hdb.
  - rewrite Be'. unfold I2. fold X. ring.
  - split; [exact Fs | ]. split; [exact Flo | ]. split; [exact Fe | ]. split; [exact Ep | ].
    split; [ | split; [exact Lo1 | exact Main]].
    rewrite Bs. apply Rle_trans with 1; [apply rnd_bound; [exact One | apply Rle_trans with (1 := Rabs_triang _ _); fold X in Am |- *; lra]
                                       | change 1 with (bpow radix2 0); apply bpow_le; lia].
Qed.
(** * The table branch *)

Lemma of_int_ok E : (Z.abs E < 2 ^ 53)%Z -> finite (of_int E) /\ B (of_int E) = IZR E.
Proof.
  intros H. pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE E 0 false) as C.
  assert (F : F2R (Float radix2 E 0) = IZR E) by (unfold F2R; simpl; ring).
  assert (Fm : fmtF (IZR E)).
  { apply generic_format_FLT. exists (Float radix2 E 0); [unfold F2R; simpl; ring | simpl; lia | simpl; unfold emin; lia]. }
  rewrite F in C. change (round radix2 (FLT_exp (3 - 1024 - 53) 53) (round_mode mode_NE) (IZR E)) with (rndF (IZR E)) in C.
  rewrite (exact_round _ Fm) in C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [exact C2 | exact C1].
  - rewrite <- abs_IZR. apply Rlt_le_trans with (IZR (2 ^ 53)); [apply IZR_lt; exact H | ].
    rewrite IZR_pow2' by lia. apply bpow_le. lia.
Qed.

(** Below [2^k], rounding errs by at most [2^(k-54)]. *)
Lemma err_lt k a : (-1020 <= k)%Z -> Rabs a < bpow radix2 k -> Rabs (rndF a - a) <= bpow radix2 (k - 54).
Proof.
  intros Hk H. apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) a); [apply error_le_half_ulp; try exact _ | ].
  replace (k - 54)%Z with (-1 + (k - 53))%Z by ring. rewrite (bpow_plus radix2 (-1)). change (bpow radix2 (-1)) with (/ 2).
  apply Rmult_le_compat_l; [lra | ].
  destruct (Req_dec a 0) as [Z | N].
  - rewrite Z, ulp_FLT_0 by (unfold Prec_gt_0, prec; lia). unfold emin. apply bpow_le. lia.
  - rewrite ulp_neq_0 by exact N.
    assert (M : (mag radix2 a <= k)%Z) by (apply mag_le_bpow; [exact N | exact H]).
    unfold cexp, FLT_exp, emin, prec in *. apply bpow_le. lia.
Qed.

Lemma fix_of_fmt v : fmtF v -> Gappa_definitions.FIX v (-1074).
Proof.
  intros F. exists (Gappa_definitions.Float2 (Ztrunc (scaled_mantissa radix2 (FLT_exp emin prec) v)) (cexp radix2 (FLT_exp emin prec) v)).
  split.
  - unfold Gappa_definitions.float2R. simpl. symmetry. exact F.
  - simpl. unfold cexp, FLT_exp, emin, prec. lia.
Qed.

Lemma fmt_int m e : (Z.abs m < 2 ^ 53)%Z -> (-1074 <= e)%Z -> fmtF (IZR m * bpow radix2 e).
Proof.
  intros Hm He. apply generic_format_FLT. exists (Float radix2 m e); [unfold F2R; simpl; reflexivity | simpl; lia | simpl; unfold emin; lia].
Qed.

Lemma abs4 a b c d : Rabs (a + b + c + d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  pose proof (Rabs_triang (a + b + c) d). pose proof (Rabs_triang (a + b) c). pose proof (Rabs_triang a b). lra.
Qed.

(** [1 + x = h + l] exactly, by Fast2Sum below [2^53] and as [(x, 1)] above. *)
Lemma b_split x : finite x -> -1 < B x < bpow radix2 1020 ->
  let big := match Bcompare 53 1024 x c_two_53 with Some Lt => false | _ => true end in
  let h := if big then x else split_s0 x in
  let l := if big then c_one else split_l x in
  finite h /\ finite l /\ B h + B l = 1 + B x /\ bpow radix2 (-53) <= B h <= bpow radix2 1020 /\
  Rabs (B l) <= bpow radix2 (-53) * B h /\ (big = false -> B h = rndF (1 + B x)) /\ (big = true -> B h = B x).
Proof.
  intros Fx [H1 H2]. cbv zeta. destruct c_two_53_ok as [F53 B53]. destruct c_one_ok as [F1 B1].
  rewrite (Bcompare_correct 53 1024 x c_two_53 Fx F53), B53.
  destruct (Rcompare_spec (B x) (bpow radix2 53)) as [L | E | G]; cbv beta iota.
  - pose proof (split_ok x Fx (conj H1 L)) as SP. cbv zeta in SP. destruct SP as [Fs [Fl [Bs [Sum [[S0a S0b] Lb]]]]].
    assert (Bu : B (split_s0 x) <= bpow radix2 1020) by (apply Rle_trans with (1 := S0b); apply bpow_le; lia).
    repeat split; try assumption; try lra; try (intros D; discriminate).
  - assert (Gx : bpow radix2 53 <= B x <= bpow radix2 1020) by (rewrite E; split; [lra | apply bpow_le; lia]).
    assert (Lx : bpow radix2 (-53) <= B x) by (apply Rle_trans with (2 := proj1 Gx); apply bpow_le; lia).
    assert (Ll : Rabs (B c_one) <= bpow radix2 (-53) * B x).
    { rewrite B1, Rabs_R1. apply Rle_trans with (bpow radix2 (-53) * bpow radix2 53).
      - rewrite <- bpow_plus. simpl. lra.
      - apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
    repeat split; try assumption; try lra; try (intros D; discriminate).
  - assert (Gx : bpow radix2 53 <= B x <= bpow radix2 1020) by lra.
    assert (Lx : bpow radix2 (-53) <= B x) by (apply Rle_trans with (2 := proj1 Gx); apply bpow_le; lia).
    assert (Ll : Rabs (B c_one) <= bpow radix2 (-53) * B x).
    { rewrite B1, Rabs_R1. apply Rle_trans with (bpow radix2 (-53) * bpow radix2 53).
      - rewrite <- bpow_plus. simpl. lra.
      - apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
    repeat split; try assumption; try lra; try (intros D; discriminate).
Qed.

Lemma stage_b_core_eval x h l : finite x -> finite h -> finite l -> B h + B l = 1 + B x ->
  bpow radix2 (-53) <= B h <= bpow radix2 1020 -> Rabs (B l) <= bpow radix2 (-53) * B h ->
  let '(s, lo, eps) := stage_b_core h l in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fx Fh Fl Sum [Hl Hu] Lb.
  unfold stage_b_core. cbv zeta.
  pose proof (reduce_ok h Fh (conj Hl Hu)) as RD. cbv zeta in RD.
  set (hb := bits_of_b64 h) in *. set (E := rd_e hb) in *. set (i := rd_i hb) in *.
  set (rs := rd_rs hb) in *. set (z := rd_z h) in *.
  destruct RD as [Er [Hi [RR [Yr [Yi [Frs [Brs [Fz [Bz [Zg [[zi [Zi [Zz [Zn Zf]]]] [Fth [Ftl [Gth [Ttl [Tth Terr]]]]]]]]]]]]]]]].
  set (R := B (st_r i)) in *. set (y := B h * bpow radix2 (- E)) in *.
  pose proof (bpow_gt_0 radix2 (-53)) as Pu.
  assert (U53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (Small : forall v, Rabs v <= 1024 -> Rabs v <= bpow radix2 1000).
  { intros v Hv. apply Rle_trans with 1024; [exact Hv | change 1024 with (bpow radix2 10); apply bpow_le; lia]. }
  assert (One : fmtF 1) by (apply (fmt_pow 0); lia).
  destruct c_one_ok as [F1 B1].
  assert (Bhy : B h = y * bpow radix2 E).
  { unfold y. rewrite Rmult_assoc, <- bpow_plus. replace (- E + E)%Z with 0%Z by ring. simpl. ring. }
  (* the tables *)
  pose proof (l_check_ok st_bounds st_l1_bits st_l0_bits st_el_bits st_l_check) as LO.
  destruct LO as [FL1 [FL0 [GL1 [[L1p L1u] [L0b [Lerr _]]]]]].
  fold st_l1 in FL1, GL1, L1p, L1u, Lerr. fold st_l0 in FL0, L0b, Lerr.
  assert (Db : forall d, dval d = IZR (fst d) * bpow radix2 (snd d)) by reflexivity.
  cbn [st_bounds b_l0_max b_l_err b_tl_max b_th_max b_t_err b_s_min] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  rewrite !Db in L0b, Lerr, Ttl, Tth, Terr, Zf. cbn [fst snd] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  bpow_num_in L0b. bpow_num_in Lerr. bpow_num_in Ttl. bpow_num_in Tth. bpow_num_in Terr. bpow_num_in Zf.
  assert (Ln2 : 0.69314718055 <= ln 2 <= 0.69314718056) by (split; interval with (i_prec 64)).
  assert (L1lo : 0.6931 <= B st_l1) by (apply Rabs_le_inv in Lerr; apply Rabs_le_inv in L0b; lra).
  assert (EI : Rabs (IZR E) <= 1020) by (rewrite <- abs_IZR; apply IZR_le; lia).
  (* E as a float, and ln1 = E L1 + TH exactly *)
  destruct (of_int_ok E ltac:(lia)) as [Fef Bef].
  assert (GE : on_grid 0 (IZR E)) by (exists E; simpl; ring).
  assert (GEL : on_grid (-43) (IZR E * B st_l1)) by (replace (-43)%Z with (0 + -43)%Z by reflexivity; apply grid_mult; assumption).
  assert (AEL : Rabs (IZR E * B st_l1) <= 1020).
  { rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) by lra. apply Rle_trans with (1020 * 1); [apply Rmult_le_compat; try lra; apply Rabs_pos | lra]. }
  destruct (fmul_s (of_int E) st_l1 Fef FL1) as [Fm1 Bm1]; [rewrite Bef; apply Small; lra | ].
  rewrite Bef, exact_round in Bm1 by (apply (grid_repr (-43)); [lia | exact GEL | apply Rle_lt_trans with 1020; [exact AEL | change (bpow radix2 (-43 + 53)) with 1024; lra]]).
  assert (Gln1 : on_grid (-43) (IZR E * B st_l1 + B (st_th i))) by (apply grid_plus; assumption).
  destruct (fadd_s (fmul (of_int E) st_l1) (st_th i) Fm1 Fth) as [Fln1 Bln1].
  { apply Small. rewrite Bm1. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite Bm1, exact_round in Bln1.
  2: { apply (grid_repr (-43)); [lia | exact Gln1 | ]. apply Rle_lt_trans with 1021; [apply Rle_trans with (1 := Rabs_triang _ _); lra | change (bpow radix2 (-43 + 53)) with 1024; lra]. }
  set (ln1 := fadd (fmul (of_int E) st_l1) (st_th i)) in *.
  assert (L0b' : Rabs (B st_l0) <= / 17592186044416) by lra.
  assert (Ttl' : Rabs (B (st_tl i)) <= / 17592186044416) by lra.
  assert (Terr' : Rabs (B (st_th i) + B (st_tl i) + ln R) <= / 158456325028528675187087900672) by lra.
  assert (Lerr' : Rabs (B st_l1 + B st_l0 - ln 2) <= / 2535301200456458802993406410752) by lra.
  assert (Th1 : Rabs (B (st_th i)) <= 711 / 2048) by lra.
  assert (Zb : Rabs (B z) <= / 512) by (apply Rle_trans with zi; [exact Zz | apply Rle_trans with (1 := Zi); simpl; lra]).
  apply Rabs_le_inv in Zb as Zb'.
  assert (Pr : forall a b, Rabs a <= 1 -> Rabs b <= 1 -> Rabs (a * b) <= 1)
    by (intros a b Ha Hb; rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]).
  (* ln0 = RN(RN(E L0) + TL) *)
  assert (EL0 : Rabs (IZR E * B st_l0) <= IZR 1020 * bpow radix2 (-44)).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [lra | bpow_num; lra]. }
  destruct (fmul_s (of_int E) st_l0 Fef FL0) as [Fm0 Bm0]; [rewrite Bef; apply Small; bpow_num_in EL0; lra | ].
  rewrite Bef in Bm0.
  assert (Em0 : Rabs (B (fmul (of_int E) st_l0) - IZR E * B st_l0) <= bpow radix2 (-88)).
  { rewrite Bm0. apply (err_lt (-34)); [lia | ]. apply Rle_lt_trans with (1 := EL0). bpow_num. lra. }
  assert (Am0 : Rabs (B (fmul (of_int E) st_l0)) <= IZR 1020 * bpow radix2 (-44)).
  { rewrite Bm0. apply rnd_bound; [apply fmt_int; lia | exact EL0]. }
  destruct (fadd_s (fmul (of_int E) st_l0) (st_tl i) Fm0 Ftl) as [Fln0 Bln0].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). bpow_num_in Am0. lra. }
  set (m0 := fmul (of_int E) st_l0) in *.
  set (ln0 := fadd m0 (st_tl i)) in *.
  assert (Eln0 : Rabs (B ln0 - (B m0 + B (st_tl i))) <= bpow radix2 (-87)).
  { rewrite Bln0. apply (err_lt (-33)); [lia | ]. apply Rle_lt_trans with (1 := Rabs_triang _ _). bpow_num_in Am0. bpow_num. lra. }
  assert (Aln0 : Rabs (B ln0) <= bpow radix2 (-34)).
  { rewrite Bln0. apply rnd_bound; [apply (fmt_pow (-34)); lia | ]. apply Rle_trans with (1 := Rabs_triang _ _). bpow_num_in Am0. bpow_num. lra. }
  set (NN := IZR E * ln 2 - ln R).
  assert (HT1 : IZR (-533) * bpow radix2 (-95) <= NN - B ln1 - B ln0 <= IZR 533 * bpow radix2 (-95)).
  { apply rng_abs.
    replace (NN - B ln1 - B ln0) with (IZR E * (ln 2 - B st_l1 - B st_l0) + - (B (st_th i) + B (st_tl i) + ln R)
       + - (B m0 - IZR E * B st_l0) + - (B ln0 - (B m0 + B (st_tl i)))) by (unfold NN; rewrite Bln1; ring).
    apply Rle_trans with (1 := abs4 _ _ _ _). rewrite !Rabs_Ropp.
    assert (A1 : Rabs (IZR E * (ln 2 - B st_l1 - B st_l0)) <= 1020 * / 2535301200456458802993406410752).
    { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [lra | ].
      replace (ln 2 - B st_l1 - B st_l0) with (- (B st_l1 + B st_l0 - ln 2)) by ring. rewrite Rabs_Ropp. exact Lerr'. }
    bpow_num_in Em0. bpow_num_in Eln0. bpow_num. lra. }
  (* s1 = RN(ln1 + z) and e1, by Fast2Sum *)
  assert (CaseE : (E = 0)%Z \/ 1 <= Rabs (IZR E)).
  { destruct (Z.eq_dec E 0) as [E0 | E0]; [left; exact E0 | right; rewrite <- abs_IZR; apply IZR_le; lia]. }
  assert (BigE : 1 <= Rabs (IZR E) -> 3439 / 10000 * Rabs (IZR E) <= Rabs (B ln1 + B z)).
  { intros HE1. rewrite Bln1. pose proof (Rabs_triang_inv (IZR E * B st_l1) (- (B (st_th i) + B z))) as T.
    replace (IZR E * B st_l1 - - (B (st_th i) + B z)) with (IZR E * B st_l1 + B (st_th i) + B z) in T by ring.
    rewrite Rabs_Ropp in T. rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) in T by lra.
    assert (Rabs (B (st_th i) + B z) <= 711 / 2048 + / 512) by (apply Rle_trans with (1 := Rabs_triang _ _); lra).
    assert (Rabs (IZR E) * B st_l1 >= Rabs (IZR E) * 0.6931) by (apply Rle_ge, Rmult_le_compat_l; [apply Rabs_pos | lra]).
    nra. }
  assert (Pre : B ln1 = 0 \/ Rabs (B z) <= Rabs (B ln1)).
  { destruct CaseE as [E0 | HE1].
    - rewrite E0, Rmult_0_l, Rplus_0_l in Bln1.
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + left. rewrite Bln1. exact (proj1 (Zn eq_refl)).
      + right. rewrite Bln1. specialize (Zf eq_refl). lra.
    - right. pose proof (BigE HE1) as BE. pose proof (Rabs_triang_inv (B ln1 + B z) (B z)) as T.
      replace (B ln1 + B z - B z) with (B ln1) in T by ring. nra. }
  assert (A1z : Rabs (B ln1 + B z) <= 1021).
  { rewrite Bln1. pose proof (Rabs_triang (IZR E * B st_l1 + B (st_th i)) (B z)). pose proof (Rabs_triang (IZR E * B st_l1) (B (st_th i))). lra. }
  pose proof (fast_two_sum_ieee ln1 z Fln1 Fz
               ltac:(apply Rle_trans with 1024; [rewrite Bln1; pose proof (Rabs_triang (IZR E * B st_l1) (B (st_th i))); lra | change 1024 with (bpow radix2 10); apply bpow_le; lia])
               ltac:(apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(destruct Pre as [P | P]; [left; exact P | right; left; exact P])) as FT.
  unfold fast_two_sum64 in FT. cbv beta iota zeta in FT. destruct FT as [Fs1 [Fe1 [Bs1 Se1]]].
  set (s1 := fadd ln1 z) in *. set (e1 := fsub z (fsub s1 ln1)) in *.
  assert (F1021 : fmtF 1021) by (apply generic_format_FLT; exists (Float radix2 1021 0); [unfold F2R; simpl; ring | simpl; lia | simpl; unfold emin; lia]).
  assert (As1 : Rabs (B s1) <= 1021) by (rewrite Bs1; apply rnd_bound; [exact F1021 | exact A1z]).
  assert (He1 : Rabs (B e1) <= bpow radix2 (-44)).
  { replace (B e1) with (- (B s1 - (B ln1 + B z))) by lra. rewrite Rabs_Ropp, Bs1.
    apply (err_lt 10); [lia | ]. apply Rle_lt_trans with (1 := A1z). change (bpow radix2 10) with 1024. lra. }
  (* p + pl = z^2 *)
  assert (Domz : in_two_prod_domain (B z) (B z)).
  { unfold in_two_prod_domain. destruct Zg as [Z0 | Zg']; [left; rewrite Z0; ring | right].
    rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-62) * bpow radix2 (-62));
      [rewrite <- bpow_plus; apply bpow_le; lia | apply Rmult_le_compat; try apply bpow_ge_0; exact Zg']. }
  pose proof (two_prod_ieee 0 0 z z Fz Fz ltac:(change (bpow radix2 0) with 1; lra) ltac:(change (bpow radix2 0) with 1; lra)
                ltac:(lia) ltac:(lia) ltac:(lia) Domz) as TP.
  destruct (two_prod64 z z) as [p pl]. destruct TP as [Fp [Fpl [Bp Bppl]]].
  assert (Gz : on_grid (-115) (B z)).
  { destruct Zg as [Z0 | Zg']; [rewrite Z0; apply grid_0 | ].
    apply (grid_le (cexp radix2 (FLT_exp emin prec) (B z))); [ | apply grid_fmt, B_fmt].
    assert (-61 <= mag radix2 (B z))%Z by (apply mag_ge_bpow; apply Rle_trans with (2 := Zg'); apply bpow_le; lia).
    unfold cexp, FLT_exp, emin, prec. lia. }
  assert (Gzz : on_grid (-230) (B z * B z)) by (replace (-230)%Z with (-115 + -115)%Z by reflexivity; apply grid_mult; exact Gz).
  assert (Gp : on_grid (-230) (B p)) by (rewrite Bp; apply grid_round; [exact _ | exact _ | exact Gzz]).
  assert (Bpl' : B pl = B z * B z - B p) by lra.
  assert (Gpl : on_grid (-230) (B pl)) by (rewrite Bpl'; apply grid_minus; assumption).
  assert (Ap : Rabs (B p) <= Rabs (B z) /\ Rabs (B p) <= bpow radix2 (-18)).
  { rewrite Bp. pose proof (Rabs_pos (B z)) as Pz. split.
    - apply rnd_bound; [apply generic_format_abs, B_fmt | ]. rewrite Rabs_mult.
      apply Rle_trans with (Rabs (B z) * 1); [apply Rmult_le_compat_l; lra | lra].
    - apply rnd_bound; [apply (fmt_pow (-18)); lia | ]. rewrite Rabs_mult.
      apply Rle_trans with (/ 512 * / 512); [apply Rmult_le_compat; lra | change (bpow radix2 (-18)) with (/ 262144); lra]. }
  destruct Ap as [Apz Ap18].
  assert (Ap1 : Rabs (B p) <= 1) by lra.
  assert (Apl : Rabs (B pl) <= 2).
  { rewrite Bpl'. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
    assert (Rabs (B z * B z) <= 1) by (apply Pr; lra). lra. }
  (* m = -p/2, exactly *)
  destruct c_mhalf_ok as [Fmh Bmh].
  assert (Half : forall a, Rabs (- bpow radix2 (-1) * a) = / 2 * Rabs a)
    by (intros a; rewrite Rabs_mult, Rabs_Ropp, Rabs_pos_eq by apply bpow_ge_0; reflexivity).
  destruct (fmul_s c_mhalf p Fmh Fp) as [Fm Bm]; [apply Small; rewrite Bmh, Half; lra | ].
  rewrite Bmh in Bm. replace (- bpow radix2 (-1) * B p) with ((- B p) * bpow radix2 (-1)) in Bm by ring.
  rewrite (rnd_scale (- B p) (-1) (-230) (generic_format_opp _ _ _ (B_fmt p))) in Bm.
  2: { destruct (Req_dec (B p) 0) as [Z0 | N0]; [left; rewrite Z0; ring | right; rewrite Rabs_Ropp; apply grid_nonzero; assumption]. }
  2: lia.
  set (m := fmul c_mhalf p) in *.
  assert (Bm' : B m = - (B p / 2)) by (rewrite Bm; change (bpow radix2 (-1)) with (/ 2); unfold Rdiv; ring).
  assert (Am : Rabs (B m) <= Rabs (B z) / 2 /\ Rabs (B m) <= bpow radix2 (-19)).
  { rewrite Bm', Rabs_Ropp. unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra.
    split; [lra | ]. replace (bpow radix2 (-19)) with (/ 2 * bpow radix2 (-18)) by (change (/ 2) with (bpow radix2 (-1)); rewrite <- bpow_plus; reflexivity). lra. }
  destruct Am as [Amz Am19].
  (* s, e2 by Fast2Sum *)
  assert (Pre2 : Rabs (B m) <= Rabs (B s1)).
  { destruct CaseE as [E0 | HE1].
    - assert (Ln1t : B ln1 = B (st_th i)) by (rewrite Bln1, E0, Rmult_0_l, Rplus_0_l; reflexivity).
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + destruct (Zn eq_refl) as [Th0 _]. rewrite Bs1, Ln1t, Th0, Rplus_0_l, exact_round by apply B_fmt.
        pose proof (Rabs_pos (B z)). lra.
      + specialize (Zf eq_refl). rewrite Bs1. apply Rle_trans with (bpow radix2 (-19)); [lra | ].
        apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-19)); lia | ].
        rewrite Ln1t. pose proof (Rabs_triang_inv (B (st_th i)) (- B z)) as T.
        replace (B (st_th i) - - B z) with (B (st_th i) + B z) in T by ring. rewrite Rabs_Ropp in T. bpow_num. lra.
    - rewrite Bs1. apply Rle_trans with (bpow radix2 (-19)); [lra | ].
      apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-19)); lia | ].
      pose proof (BigE HE1). bpow_num. lra. }
  assert (Am1 : Rabs (B m) <= 1) by (apply Rle_trans with (1 := Am19); change 1 with (bpow radix2 0); apply bpow_le; lia).
  pose proof (fast_two_sum_ieee s1 m Fs1 Fm
               ltac:(apply Rle_trans with 1024; [lra | change 1024 with (bpow radix2 10); apply bpow_le; lia])
               ltac:(apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(right; left; exact Pre2)) as FT2.
  unfold fast_two_sum64 in FT2. cbv beta iota zeta in FT2. destruct FT2 as [Fs [Fe2 [Bs Se2]]].
  set (s := fadd s1 m) in *. set (e2 := fsub m (fsub s s1)) in *.
  assert (He2 : Rabs (B e2) <= bpow radix2 (-44)).
  { replace (B e2) with (- (B s - (B s1 + B m))) by lra. rewrite Rabs_Ropp, Bs.
    apply (err_lt 10); [lia | ]. apply Rle_lt_trans with (1 := Rabs_triang _ _). change (bpow radix2 10) with 1024. lra. }
  assert (As : Rabs (B s) <= 1024).
  { rewrite Bs. apply rnd_bound; [apply (fmt_pow 10); lia | ]. change (bpow radix2 10) with 1024.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  (* the tail and the correction *)
  destruct (b_horner_val z Fz Zb) as [Fhz [Bhz Ahz]].
  destruct (fmul_s z p Fz Fp) as [Fzp Bzp]; [apply Small; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Azp : Rabs (B (fmul z p)) <= 1) by (rewrite Bzp; apply rnd_bound; [exact One | apply Pr; lra]).
  set (zp := fmul z p) in *.
  destruct (fmul_s zp (b_horner z) Fzp Fhz) as [Ft Bt]; [apply Small; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  set (tail := fmul zp (b_horner z)) in *.
  assert (At : Rabs (B tail) <= 1) by (rewrite Bt; apply rnd_bound; [exact One | apply Pr; lra]).
  set (L := B l * B rs).
  assert (Prs : 0 < B rs) by (rewrite Brs; apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]).
  assert (Hsr : B h * B rs = y * R).
  { rewrite Brs, Bhy. rewrite Rmult_assoc, (Rmult_comm (bpow radix2 E)), Rmult_assoc, <- bpow_plus.
    replace (- E + E)%Z with 0%Z by ring. simpl. ring. }
  assert (HL : Rabs L <= bpow radix2 (-53) * (1 + / 512)).
  { unfold L. rewrite Rabs_mult, (Rabs_pos_eq (B rs)) by lra.
    apply Rle_trans with (bpow radix2 (-53) * B h * B rs); [apply Rmult_le_compat_r; lra | ].
    rewrite Rmult_assoc, Hsr. apply Rmult_le_compat_l; [lra | ]. lra. }
  assert (HL1 : Rabs L <= 1) by (apply Rle_trans with (1 := HL); rewrite U53; lra).
  destruct (fmul_s l rs Fl Frs) as [Flr Blr]; [apply Small; fold L; lra | ].
  assert (Alr : Rabs (B (fmul l rs)) <= 1) by (rewrite Blr; apply rnd_bound; [exact One | fold L; exact HL1]).
  set (lr := fmul l rs) in *.
  destruct (fsub_s c_one z F1 Fz) as [Fomz Bomz]; [apply Small; rewrite B1; apply Rabs_le; lra | ].
  rewrite B1 in Bomz.
  assert (Aomz : Rabs (B (fsub c_one z)) <= 2)
    by (rewrite Bomz; apply rnd_bound; [apply (fmt_pow 1); lia | change (bpow radix2 1) with 2; apply Rabs_le; lra]).
  set (omz := fsub c_one z) in *.
  destruct (fadd_s omz p Fomz Fp) as [Fq1 Bq1]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  assert (Aq1 : Rabs (B (fadd omz p)) <= 4)
    by (rewrite Bq1; apply rnd_bound; [apply (fmt_pow 2); lia | change (bpow radix2 2) with 4; apply Rle_trans with (1 := Rabs_triang _ _); lra]).
  set (q1 := fadd omz p) in *.
  destruct (fsub_s q1 zp Fq1 Fzp) as [Fq2 Bq2]; [apply Small; unfold Rminus; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra | ].
  assert (Aq2 : Rabs (B (fsub q1 zp)) <= 8)
    by (rewrite Bq2; apply rnd_bound; [apply (fmt_pow 3); lia | change (bpow radix2 3) with 8; unfold Rminus; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra]).
  set (q2 := fsub q1 zp) in *.
  destruct (fmul_s lr q2 Flr Fq2) as [Flrt Blrt].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 8); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  assert (Alrt : Rabs (B (fmul lr q2)) <= 8).
  { rewrite Blrt. apply rnd_bound; [apply (fmt_pow 3); lia | change (bpow radix2 3) with 8].
    rewrite Rabs_mult. apply Rle_trans with (1 * 8); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  set (lrt := fmul lr q2) in *.
  (* -pl/2, exactly *)
  destruct (fmul_s c_mhalf pl Fmh Fpl) as [Fmpl Bmpl]; [apply Small; rewrite Bmh, Half; lra | ].
  rewrite Bmh in Bmpl. replace (- bpow radix2 (-1) * B pl) with ((- B pl) * bpow radix2 (-1)) in Bmpl by ring.
  rewrite (rnd_scale (- B pl) (-1) (-230) (generic_format_opp _ _ _ (B_fmt pl))) in Bmpl.
  2: { destruct (Req_dec (B pl) 0) as [Z0 | N0]; [left; rewrite Z0; ring | right; rewrite Rabs_Ropp; apply grid_nonzero; assumption]. }
  2: lia.
  set (mpl := fmul c_mhalf pl) in *.
  assert (Bmpl' : B mpl = - (B pl / 2)) by (rewrite Bmpl; change (bpow radix2 (-1)) with (/ 2); unfold Rdiv; ring).
  assert (Ampl : Rabs (B mpl) <= 1) by (rewrite Bmpl', Rabs_Ropp; unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra; lra).
  (* lo *)
  destruct (fadd_s mpl tail Fmpl Ft) as [Fr1 Br1]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  assert (Ar1 : Rabs (B (fadd mpl tail)) <= 2)
    by (rewrite Br1; apply rnd_bound; [apply (fmt_pow 1); lia | change (bpow radix2 1) with 2; apply Rle_trans with (1 := Rabs_triang _ _); lra]).
  set (r1 := fadd mpl tail) in *.
  assert (Aln0' : Rabs (B ln0) <= 1) by (apply Rle_trans with (1 := Aln0); change 1 with (bpow radix2 0); apply bpow_le; lia).
  destruct (fadd_s ln0 lrt Fln0 Flrt) as [Fr2 Br2]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  assert (Ar2 : Rabs (B (fadd ln0 lrt)) <= 16)
    by (rewrite Br2; apply rnd_bound; [apply (fmt_pow 4); lia | change (bpow radix2 4) with 16; apply Rle_trans with (1 := Rabs_triang _ _); lra]).
  set (r2 := fadd ln0 lrt) in *.
  destruct (fadd_s r2 r1 Fr2 Fr1) as [Fr3 Br3]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  assert (Ar3 : Rabs (B (fadd r2 r1)) <= 32)
    by (rewrite Br3; apply rnd_bound; [apply (fmt_pow 5); lia | change (bpow radix2 5) with 32; apply Rle_trans with (1 := Rabs_triang _ _); lra]).
  set (r3 := fadd r2 r1) in *.
  assert (He1' : Rabs (B e1) <= 1) by (apply Rle_trans with (1 := He1); change 1 with (bpow radix2 0); apply bpow_le; lia).
  assert (He2' : Rabs (B e2) <= 1) by (apply Rle_trans with (1 := He2); change 1 with (bpow radix2 0); apply bpow_le; lia).
  destruct (fadd_s e1 e2 Fe1 Fe2) as [Fr4 Br4]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  assert (Ar4 : Rabs (B (fadd e1 e2)) <= 2)
    by (rewrite Br4; apply rnd_bound; [apply (fmt_pow 1); lia | change (bpow radix2 1) with 2; apply Rle_trans with (1 := Rabs_triang _ _); lra]).
  set (r4 := fadd e1 e2) in *.
  destruct (fadd_s r4 r3 Fr4 Fr3) as [Flo Blo]; [apply Small; apply Rle_trans with (1 := Rabs_triang _ _); lra | ].
  set (lo := fadd r4 r3) in *.
  assert (Elo : B lo = b_lo (B e1) (B e2) (B ln0) L (B z)).
  { assert (Br1' : B r1 = rndF (B tail - B pl / 2)) by (rewrite Br1, Bmpl'; f_equal; ring).
    unfold b_lo. cbv zeta.
    change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
    rewrite Blo, Br4, Br3, Br2, Br1', Blrt, Bq2, Bq1, Bomz, Blr, Bt, Bzp, Bhz, Bpl', Bp. fold L. reflexivity. }
  (* the certificate for lo *)
  assert (HLr : IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62)).
  { apply rng_abs. apply Rle_trans with (1 := HL). bpow_num. lra. }
  assert (Hzr : IZR (-1) * bpow radix2 (-9) <= B z <= IZR 1 * bpow radix2 (-9)) by (bpow_num; lra).
  assert (He1r : IZR (-1) * bpow radix2 (-44) <= B e1 <= IZR 1 * bpow radix2 (-44)) by (apply rng_abs; bpow_num; bpow_num_in He1; lra).
  assert (He2r : IZR (-1) * bpow radix2 (-44) <= B e2 <= IZR 1 * bpow radix2 (-44)) by (apply rng_abs; bpow_num; bpow_num_in He2; lra).
  assert (Hln0r : IZR (-1) * bpow radix2 (-34) <= B ln0 <= IZR 1 * bpow radix2 (-34)) by (apply rng_abs; bpow_num; bpow_num_in Aln0; lra).
  destruct (stage_b_lo (B e1) (B e2) (B ln0) L (B z) Hzr HLr He1r He2r Hln0r
              (fix_of_fmt _ (B_fmt e1)) (fix_of_fmt _ (B_fmt e2)) (fix_of_fmt _ (B_fmt ln0))) as [G1 G2].
  rewrite <- Elo in G1, G2.
  (* ln(1 + x) = E ln 2 − ln R + ln(1 + z) + ln(1 + u), u = L/(1 + z) *)
  assert (Hzr1 : 0 < 1 + B z) by lra.
  set (u := L / (1 + B z)).
  assert (Huu : Rabs u <= / 2 ^ 52).
  { unfold u, Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (1 + B z)) by lra.
    apply Rmult_le_reg_r with (1 + B z); [lra | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    apply Rle_trans with (1 := HL). bpow_num. simpl. lra. }
  assert (Dec : ln (1 + B x) = IZR E * ln 2 - ln R + ln (1 + B z) + ln (1 + u)).
  { assert (Ex : 1 + B x = (1 + B z) * (1 + u) * bpow radix2 E * / R).
    { replace ((1 + B z) * (1 + u)) with (1 + B z + L) by (unfold u; field; lra).
      rewrite <- Sum, Bhy. unfold L. rewrite Brs. rewrite Bz.
      assert (Bm2 : bpow radix2 (- E) * bpow radix2 E = 1) by (rewrite <- bpow_plus, Z.add_opp_diag_l; reflexivity).
      replace (B l) with (B l * (bpow radix2 (- E) * bpow radix2 E)) at 1 by (rewrite Bm2; ring).
      field. lra. }
    pose proof (bpow_gt_0 radix2 E) as PE.
    assert (Pu1 : 0 < 1 + u) by (apply Rabs_le_inv in Huu; assert (/ 2 ^ 52 < 1) by (simpl; lra); lra).
    rewrite Ex, ln_mult, ln_mult, ln_mult, ln_Rinv, ln_bpow by (try apply Rinv_0_lt_compat; try apply Rmult_lt_0_compat; try apply Rmult_lt_0_compat; lra).
    ring. }
  set (W := b_W (B z)).
  set (ap := ln (1 + B z) - (B z - B z * B z / 2 + B z * B z * B z * W)).
  assert (Hap : IZR (-349) * bpow radix2 (-91) <= ap <= IZR 349 * bpow radix2 (-91)).
  { apply rng_abs. pose proof (b_approx (B z) ltac:(simpl; lra)) as BA. fold W in BA.
    replace ap with (ln (1 + B z) - B z + B z * B z / 2 - B z * B z * B z * W) by (unfold ap; ring).
    apply Rle_trans with (1 := BA). rewrite !Rabs_mult.
    assert (Z3 : Rabs (B z) * Rabs (B z) * Rabs (B z) <= / 512 * / 512 * / 512).
    { pose proof (Rabs_pos (B z)). apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | apply Rmult_le_compat; lra | lra]. }
    bpow_num. simpl. lra. }
  set (t6 := ln (1 + u) - u).
  assert (Ht6 : Rabs t6 <= IZR 267 * bpow radix2 (-114)).
  { unfold t6. apply Rle_trans with (u * u / (1 - Rabs u)).
    - apply ln1p_linear. apply Rle_trans with (1 := Huu). simpl. lra.
    - assert (Uu : Rabs u <= IZR 519 * bpow radix2 (-62) / (1 - / 512)).
      { unfold u, Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (1 + B z)) by lra.
        apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | apply abs_rng; exact HLr | ].
        apply Rinv_le_contravar; lra. }
      bpow_num_in Uu. bpow_num. pose proof (Rabs_pos u).
      assert (u * u <= Rabs u * Rabs u) by (rewrite <- Rabs_mult; apply Rle_abs).
      assert (Rabs u * Rabs u <= (519 * / 4611686018427387904 / (1 - / 512)) * (519 * / 4611686018427387904 / (1 - / 512)))
        by (apply Rmult_le_compat; lra).
      assert (A0 : 0 <= u * u) by apply Rle_0_sqr.
      assert (Huu' : Rabs u <= / 4503599627370496) by (apply Rle_trans with (1 := Huu); simpl; lra).
      unfold Rdiv at 1. apply Rle_trans with ((519 * / 4611686018427387904 / (1 - / 512)) * (519 * / 4611686018427387904 / (1 - / 512)) * / (1 - / 4503599627370496)).
      + apply Rmult_le_compat; [exact A0 | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
        apply Rinv_le_contravar; lra.
      + lra. }
  assert (Hlt : IZR (-263) * bpow radix2 (-97) <= u + t6 - L * (1 - B z + B z * B z - B z * B z * B z) <= IZR 263 * bpow radix2 (-97)).
  { replace (u + t6 - L * (1 - B z + B z * B z - B z * B z * B z)) with (L * (B z * B z * B z * B z) / (1 + B z) + t6)
      by (unfold u; field; lra).
    apply rng_abs. apply Rle_trans with (1 := Rabs_triang _ _).
    assert (Z4 : Rabs (B z * B z * B z * B z) <= / 512 * / 512 * / 512 * / 512).
    { rewrite !Rabs_mult. pose proof (Rabs_pos (B z)).
      apply Rmult_le_compat; [repeat apply Rmult_le_pos; lra | lra | | lra].
      apply Rmult_le_compat; [repeat apply Rmult_le_pos; lra | lra | | lra].
      apply Rmult_le_compat; lra. }
    assert (A : Rabs (L * (B z * B z * B z * B z) / (1 + B z)) <= IZR 519 * bpow radix2 (-62) * (/ 512 * / 512 * / 512 * / 512) * / (1 - / 512)).
    { unfold Rdiv. rewrite (Rabs_mult (L * _)), (Rabs_mult L), Rabs_Rinv, (Rabs_pos_eq (1 + B z)) by lra.
      apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | | apply Rinv_le_contravar; lra].
      apply Rmult_le_compat; try apply Rabs_pos; [apply abs_rng; exact HLr | exact Z4]. }
    bpow_num_in A. bpow_num_in Ht6. bpow_num. lra. }
  destruct c_eb_ok as [Feb Beb].
  destruct (b_table_compose (ln (1 + B x)) NN (B ln1) (B ln0) (B z) L (B s1) (B e1) (B m) (B s) (B e2) (B p) (B pl) (B lo) W ap u t6
              (B lo - b_ideal (B e1) (B e2) (B ln0) L (B z))) as [Ep [Lo1 Main]].
  - rewrite Dec. unfold ap, t6, NN. ring.
  - reflexivity.
  - exact Zb.
  - lra.
  - exact Bm'.
  - exact Se2.
  - exact Bppl.
  - unfold b_ideal. fold W.
    change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
    rewrite <- Bp, Bpl'. ring.
  - exact HT1.
  - exact Hap.
  - exact Hlt.
  - exact G1.
  - apply abs_rng in G2. bpow_num_in G2. bpow_num. lra.
  - exact As.
  - split; [exact Fs | ]. split; [exact Flo | ]. split; [exact Feb | ]. rewrite Beb. split; [exact Ep | ].
    split; [apply Rle_trans with 1024; [exact As | change 1024 with (bpow radix2 10); apply bpow_le; lia] | ].
    split; [exact Lo1 | exact Main].
Qed.

Theorem stage_b_table_eval x : finite x -> -1 < B x < bpow radix2 1020 ->
  let '(s, lo, eps) := stage_b_table_parts x in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fx Hr.
  pose proof (b_split x Fx Hr) as SP. cbv zeta in SP.
  destruct SP as [Fh [Fl [Sum [Hb [Lb _]]]]].
  unfold stage_b_table_parts. cbv zeta.
  exact (stage_b_core_eval x _ _ Fx Fh Fl Sum Hb Lb).
Qed.

Theorem stage_b_eval x : finite x -> bpow radix2 (-54) <= Rabs (B x) -> -1 < B x < bpow radix2 1020 ->
  let '(s, lo, eps) := stage_b_parts x in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fx Hx Hr. destruct c_two_m9_ok as [F9 B9].
  pose proof (is_finite_Babs 53 1024 unop_nan_pl64 x) as Fax. fold (b64_abs x) in Fax. rewrite Fx in Fax.
  assert (Bax : B (b64_abs x) = Rabs (B x)) by apply B_abs.
  unfold stage_b_parts. rewrite (Bcompare_correct 53 1024 (b64_abs x) c_two_m9 Fax F9), Bax, B9.
  destruct (Rcompare_spec (Rabs (B x)) (bpow radix2 (-9))) as [L | E | G]; cbv beta iota.
  - exact (stage_b_small_eval x Fx (conj Hx L)).
  - exact (stage_b_table_eval x Fx Hr).
  - exact (stage_b_table_eval x Fx Hr).
Qed.

(** Stage B, when its test passes, returns [RN(ln(1 + x))], and every real
    within [2^-123] of [ln(1 + x)] relatively rounds to the same value. *)
Theorem stage_b_ok x v : finite x -> bpow radix2 (-54) <= Rabs (B x) -> -1 < B x < bpow radix2 1020 ->
  stage_b x = Some v ->
  finite v /\ B v = rndF (ln (1 + B x)) /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) -> rndF w = B v.
Proof.
  intros Fx Hx Hr Hd. pose proof (stage_b_eval x Fx Hx Hr) as EV. unfold stage_b in Hd.
  destruct (stage_b_parts x) as [[s lo] eps].
  destruct EV as [Fs [Flo [Feps [E0 [Hs [Hl Main]]]]]].
  destruct (decide_ok s lo eps v Fs Flo Feps E0 Hs Hl Hd) as [Fv Dv].
  assert (All : forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) -> rndF w = B v)
    by (intros w Hw; apply Dv, Main, Hw).
  split; [exact Fv | split; [ | exact All]].
  symmetry. apply All. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
  apply Rmult_le_pos; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | apply Rabs_pos].
Qed.
