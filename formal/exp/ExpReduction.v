(** exp/mod.rs's argument reduction [Reduced::of] (docs/exp.md, section 3),
    transcribed on binary64 and proved: [n] is the integer nearest [x/L] up to
    the rounding of [x·INV_L], [r1 = x − n·L1] and [p2 + e2 = n·L2] exactly, and
    [(r_hi, r_lo)] is within [2^−113] of [x − n·L] ([reduce_ok]). The last bound
    is formal/exp/reduction.g's theorem, whose Coq proof Gappa writes as module
    [exp_reduction] (scripts/check_formal.sh); [reduction_bound] states it over
    Flocq's rounding. [L] is [L1 + L2 + L3 + L4 + dL] for any [|dL| <= 2^−206],
    the generator's claim about [ln 2 / 128]. *)

From Coq Require Import ZArith Reals Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Binary64Mul.
From Gappa Require Gappa_definitions Gappa_round_def.
Require exp_reduction.

Open Scope R_scope.

(** Rounding to nearest-even commutes with a shift by an even integer. *)
Lemma znearest_shift (c : Z) x : Z.even c = true ->
  Znearest ne (x + IZR c) = (Znearest ne x + c)%Z.
Proof.
  intros Hc.
  assert (Fl : Zfloor (x + IZR c) = (Zfloor x + c)%Z).
  { apply Zfloor_imp. rewrite !plus_IZR. pose proof (Zfloor_lb x). pose proof (Zfloor_ub x). lra. }
  assert (Ce : Zceil (x + IZR c) = (Zceil x + c)%Z).
  { apply Zceil_imp. rewrite minus_IZR, !plus_IZR. pose proof (Zceil_ub x). pose proof (Zceil_lb x). lra. }
  unfold Znearest. rewrite Fl, Ce, plus_IZR.
  replace (x + IZR c - (IZR (Zfloor x) + IZR c)) with (x - IZR (Zfloor x)) by ring.
  destruct (Rcompare (x - IZR (Zfloor x)) (/ 2)); try reflexivity.
  unfold ne. rewrite Z.even_add, Hc.
  destruct (Z.even (Zfloor x)); reflexivity.
Qed.

(** The shifter [1.5·2^52]. *)
Definition shifter : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE 3 51 false.

Lemma shifter_value : B shifter = IZR (3 * 2 ^ 51) /\ finite shifter.
Proof.
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE 3 51 false) as C.
  assert (V : F2R (Float radix2 3 51) = IZR (3 * 2 ^ 51)) by (unfold F2R; cbn [Fnum Fexp]; rewrite mult_IZR; reflexivity).
  rewrite V in C. rewrite round_generic in C.
  - rewrite Rlt_bool_true in C.
    + destruct C as [C1 [C2 _]]. split; assumption.
    + rewrite Rabs_pos_eq by (apply IZR_le; lia). apply Rlt_le_trans with (bpow radix2 53).
      * replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia.
      * apply bpow_le. lia.
  - auto with typeclass_instances.
  - rewrite <- V. apply generic_format_FLT. exists (Float radix2 3 51); simpl; [reflexivity | lia | lia].
Qed.

(** [(y + SHIFTER) − SHIFTER] is [y] rounded to the nearest integer, ties to
    even, for [|y| <= 2^50]. *)
Theorem shifter_round y : finite y -> Rabs (B y) <= bpow radix2 50 ->
  let n := fsub (fadd y shifter) shifter in
  finite n /\ B n = IZR (Znearest ne (B y)).
Proof.
  intros Fy Hy n. destruct shifter_value as [Bs Fs].
  set (k := Znearest ne (B y)).
  assert (Hk : Rabs (B y - IZR k) <= / 2) by (unfold k; apply Znearest_half).
  assert (Kb : (Z.abs k <= 2 ^ 50 + 1)%Z).
  { apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hy.
    replace (bpow radix2 50) with (IZR (2 ^ 50)) in Hy by reflexivity.
    assert (- IZR (2 ^ 50) - 1 < IZR k < IZR (2 ^ 50) + 1) by lra.
    rewrite <- !plus_IZR, <- opp_IZR, <- minus_IZR in H. destruct H as [H1 H2].
    apply lt_IZR in H1. apply lt_IZR in H2. lia. }
  (* the sum *)
  assert (Ha : bnd 1 53 (B y + B shifter)).
  { unfold bnd. rewrite Bs. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
    change (bpow radix2 50) with 1125899906842624%R in Hy. change (IZR 1 * bpow radix2 53) with (1 * 9007199254740992)%R.
    apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
  destruct (fadd_ok 1 53 y shifter Fy Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ha) as [Fa Ba].
  assert (Rs : rndF (B y + B shifter) = IZR (k + 3 * 2 ^ 51)).
  { rewrite Bs.
    assert (Mag : mag radix2 (B y + IZR (3 * 2 ^ 51)) = 53%Z :> BinNums.Z).
    { apply mag_unique. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
      change (bpow radix2 50) with 1125899906842624%R in Hy.
      change (bpow radix2 (53 - 1)) with 4503599627370496%R. change (bpow radix2 53) with 9007199254740992%R.
      apply Rabs_le_inv in Hy. rewrite Rabs_pos_eq by lra. lra. }
    unfold round, scaled_mantissa, cexp. rewrite Mag. unfold FLT_exp, emin, prec.
    change (Z.max (53 - 53) (-1074)) with 0%Z. change (bpow radix2 (- 0)) with 1%R. rewrite Rmult_1_r.
    rewrite znearest_shift by reflexivity. fold k. unfold F2R. cbn [Fnum Fexp]. change (bpow radix2 0) with 1%R. ring. }
  (* the difference *)
  assert (Hd : bnd 1 53 (B (fadd y shifter) - B shifter)).
  { unfold bnd. rewrite Ba, Rs, Bs, <- minus_IZR. replace (k + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with k by ring.
    rewrite <- abs_IZR. replace (IZR 1 * bpow radix2 53) with (IZR (2 ^ 53)) by (simpl; ring). apply IZR_le. lia. }
  destruct (fsub_ok 1 53 (fadd y shifter) shifter Fa Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fn Bn].
  split; [exact Fn | ]. unfold n. rewrite Bn, Ba, Rs, Bs, <- minus_IZR.
  replace (k + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with k by ring.
  apply round_generic; auto with typeclass_instances.
  apply generic_format_FLT. exists (Float radix2 k 0); simpl; [unfold F2R; simpl; ring | | ].
  - apply Z.le_lt_trans with (2 ^ 50 + 1)%Z; [exact Kb | reflexivity].
  - unfold emin. lia.
Qed.

(** exp/tables.rs's reduction constants, from their encodings. *)
Definition c_inv_l : f64 := b64_of_bits 4640701337412797182.   (* 0x40671547652b82fe *)
Definition c_l1 : f64 := b64_of_bits 4572893336921964544.      (* 0x3f762e42fefc0000 *)
Definition c_l2 : f64 := b64_of_bits 13635880478764185753.     (* 0xbd3c610ca86c3899 *)
Definition c_l3 : f64 := b64_of_bits 4163582197559673075.      (* 0x39c803f2f6af40f3 *)

Lemma c_inv_l_val : B c_inv_l = F2R (Float radix2 6497320848556798 (-45)).
Proof. unfold c_inv_l. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B.
  change (binary_float_of_bits_aux 52 11 4640701337412797182) with (F754_finite false 6497320848556798 (-45)). reflexivity. Qed.

Lemma c_l1_val : B c_l1 = F2R (Float radix2 6243314768281600 (-60)).
Proof. unfold c_l1. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B.
  change (binary_float_of_bits_aux 52 11 4572893336921964544) with (F754_finite false 6243314768281600 (-60)). reflexivity. Qed.
Lemma c_l2_val : B c_l2 = F2R (Float radix2 (-7988006341064857) (-96)).
Proof. unfold c_l2. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B.
  change (binary_float_of_bits_aux 52 11 13635880478764185753) with (F754_finite true 7988006341064857 (-96)). reflexivity. Qed.
Lemma c_l3_val : B c_l3 = F2R (Float radix2 6759741496705267 (-151)).
Proof. unfold c_l3. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B.
  change (binary_float_of_bits_aux 52 11 4163582197559673075) with (F754_finite false 6759741496705267 (-151)). reflexivity. Qed.
Lemma c_finite : finite c_inv_l /\ finite c_l1 /\ finite c_l2 /\ finite c_l3.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** [|RN(v) − v| <= 2^−53 |v| + 2^−1075]. *)
Lemma rnd_abs_err v : Rabs (rndF v - v) <= / 9007199254740992 * Rabs v + / 2 * bpow radix2 (-1074).
Proof.
  destruct (error_N_FLT radix2 (-1074) 53 ltac:(lia) ne v) as [eps [eta [He [Ht [_ Hr]]]]].
  change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Hr. rewrite Hr.
  replace (v * (1 + eps) + eta - v) with (v * eps + eta) by ring.
  assert (He' : Rabs eps <= / 9007199254740992).
  { change (- (53) + 1)%Z with (-52)%Z in He. change (bpow radix2 (-52)) with (/ 4503599627370496)%R in He. lra. }
  apply Rle_trans with (Rabs (v * eps) + Rabs eta); [apply Rabs_triang | ].
  rewrite Rabs_mult, (Rmult_comm (/ 9007199254740992)). apply Rplus_le_compat; [apply Rmult_le_compat_l; [apply Rabs_pos | exact He'] | exact Ht].
Qed.

Section Reduction.

(** The facts about [L] that steps 1–2 use, proved for the generated split in
    [L_range] and [inv_l_close]. *)
Variable L : R.
Hypothesis L_range : 0.0054152123 <= L <= 0.0054152124.
Hypothesis inv_l_close : Rabs (B c_inv_l - / L) <= bpow radix2 (-40).

(** Steps 1–2: [n = RN_int(RN(x·INV_L))], an integer with [|n| <= 137601], and
    [|x/L − n| <= 1/2 + 10^−9]. *)
Theorem reduce_n x : finite x -> -745.1333 <= B x <= 709.79 ->
  let n := fsub (fadd (fmul x c_inv_l) shifter) shifter in
  finite n /\ exists k : BinNums.Z, B n = IZR k /\ (Z.abs k <= 137601)%Z /\
    Rabs (B x / L - IZR k) <= / 2 + / 1000000000.
Proof.
  intros Fx Hx n. destruct c_finite as [Fi [F1 [F2 F3]]].
  assert (Iv : B c_inv_l = IZR 6497320848556798 * / 35184372088832) by (rewrite c_inv_l_val; reflexivity).
  assert (Ib : 184.66 <= B c_inv_l <= 184.67) by (rewrite Iv; lra).
  assert (Bp : bnd 1 18 (B x * B c_inv_l)).
  { unfold bnd. change (bpow radix2 18) with 262144%R; rewrite ?Rmult_1_l. rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (B c_inv_l)) by lra. apply Rabs_le_inv in Hx || idtac.
    assert (Rabs (B x) <= 745.1333) by (apply Rabs_le; lra). nra. }
  destruct (fmul_ok 1 18 x c_inv_l Fx Fi ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bp) as [Fy By].
  set (y := fmul x c_inv_l) in *.
  assert (Ey := rnd_abs_err (B x * B c_inv_l)). rewrite <- By in Ey.
  assert (Yb : Rabs (B y) <= bpow radix2 50).
  { rewrite By. apply Rle_trans with (IZR 1 * bpow radix2 18); [apply bnd_round; [lia | lia | exact Bp] | ].
    change (bpow radix2 18) with 262144%R; rewrite ?Rmult_1_l. change (bpow radix2 50) with 1125899906842624%R. lra. }
  destruct (shifter_round y Fy Yb) as [Fn Bn]. fold n in Fn, Bn.
  split; [exact Fn | ]. exists (Znearest ne (B y)). split; [exact Bn | ].
  set (k := Znearest ne (B y)).
  assert (Hk : Rabs (B y - IZR k) <= / 2) by (unfold k; apply Znearest_half).
  change (bpow radix2 (-1074)) with (/ 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)%R in Ey.
  assert (Xb : Rabs (B x) <= 745.1333) by (apply Rabs_le; lra).
  split.
  - (* |k| <= |y| + 1/2 <= 137601.1 *)
    assert (Rabs (B x * B c_inv_l) <= 137600.6) by (rewrite Rabs_mult, (Rabs_pos_eq (B c_inv_l)) by lra; nra).
    assert (Rabs (IZR k) <= 137601.2).
    { pose proof H as H'. apply Rabs_le_inv in H'. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Ey. apply Rabs_le. split; lra. }
    rewrite <- abs_IZR in H0. assert (IZR (Z.abs k) < IZR 137602) by lra. apply lt_IZR in H1. lia.
  - (* x/L − k = x (1/L − INV_L) + (x INV_L − y) + (y − k) *)
    destruct L_range as [L1' L2'].
    replace (B x / L - IZR k) with (B x * (/ L - B c_inv_l) + (B x * B c_inv_l - B y) + (B y - IZR k)) by (unfold Rdiv; ring).
    assert (A1 : Rabs (B x * (/ L - B c_inv_l)) <= 745.1333 * bpow radix2 (-40)).
    { rewrite Rabs_mult, (Rabs_minus_sym (/ L)).
      apply Rmult_le_compat; try apply Rabs_pos; assumption. }
    change (bpow radix2 (-40)) with (/ 1099511627776)%R in A1.
    assert (A2 : Rabs (B x * B c_inv_l - B y) <= / 9007199254740992 * 137600.6 + / 1000000000000).
    { rewrite <- Rabs_Ropp, Ropp_minus_distr.
      assert (Rabs (B x * B c_inv_l) <= 137600.6) by (rewrite Rabs_mult, (Rabs_pos_eq (B c_inv_l)) by lra; nra).
      apply Rle_trans with (1 := Ey). lra. }
    eapply Rle_trans; [apply Rabs_triang | ]. eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ]. lra.
Qed.

End Reduction.

Lemma fmt_int m e : (Z.abs m < 2 ^ 53)%Z -> (-1074 <= e)%Z -> fmtF (IZR m * bpow radix2 e).
Proof.
  intros Hm He. apply generic_format_FLT. exists (Float radix2 m e); [reflexivity | exact Hm | exact He].
Qed.

(** [r1 = x − k·L1] is representable when [|r1| < 2^−8], [L1 = l·2^−42], and
    [|x| >= 2^−9] unless [k = 0]: both terms are multiples of
    [2^min(cexp x, −42)], at least [2^−61]. *)
Lemma diff_exact x k l : fmtF x -> (k <> 0%Z -> bpow radix2 (-9) <= Rabs x) ->
  Rabs (x - IZR k * (IZR l * bpow radix2 (-42))) < bpow radix2 (-8) ->
  fmtF (x - IZR k * (IZR l * bpow radix2 (-42))).
Proof.
  intros Fx Hx Hd.
  destruct (Z.eq_dec k 0) as [K0 | K0].
  { subst k. rewrite Rmult_0_l, Rminus_0_r. exact Fx. }
  specialize (Hx K0).
  set (cx := cexp radix2 (FLT_exp emin prec) x).
  set (M := Ztrunc (scaled_mantissa radix2 (FLT_exp emin prec) x)).
  assert (Ex : x = IZR M * bpow radix2 cx) by exact Fx.
  assert (Mg : (-8 <= mag radix2 x)%Z).
  { apply mag_ge_bpow. replace (-8 - 1)%Z with (-9)%Z by lia. exact Hx. }
  assert (Cx : (-61 <= cx)%Z) by (unfold cx, cexp, FLT_exp, emin, prec; lia).
  set (e := Z.min cx (-42)).
  set (m := (M * Zpower radix2 (cx - e) - k * l * Zpower radix2 (-42 - e))%Z).
  assert (Em : x - IZR k * (IZR l * bpow radix2 (-42)) = IZR m * bpow radix2 e).
  { unfold m. rewrite minus_IZR, !mult_IZR, !IZR_Zpower by (unfold e; lia).
    rewrite Ex at 1. rewrite Rmult_minus_distr_r, !Rmult_assoc, <- !bpow_plus.
    replace (cx - e + e)%Z with cx by ring. replace (-42 - e + e)%Z with (-42)%Z by ring. ring. }
  rewrite Em in Hd |- *. apply fmt_int; [ | unfold e; lia].
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) in Hd by apply bpow_ge_0.
  assert (B : Rabs (IZR m) < bpow radix2 53).
  { apply Rmult_lt_reg_r with (bpow radix2 e); [apply bpow_gt_0 | ].
    rewrite <- bpow_plus. apply Rlt_le_trans with (1 := Hd). apply bpow_le. unfold e. lia. }
  rewrite <- abs_IZR in B. change (bpow radix2 53) with (IZR (2 ^ 53)) in B. apply lt_IZR in B. exact B.
Qed.

(** [L1]–[L4] as reals. *)
Definition l1v := IZR 23816355775 * bpow radix2 (-42).
Definition l2v := F2R (Float radix2 (-7988006341064857) (-96)).
Definition l3v := F2R (Float radix2 6759741496705267 (-151)).
Definition l4v := F2R (Float radix2 4725274267454307 (-205)).

Lemma c_l1_eq : B c_l1 = l1v.
Proof. rewrite c_l1_val. unfold l1v, F2R. simpl. lra. Qed.

(** formal/exp/reduction.g's theorem, over Flocq's rounding. *)
Theorem reduction_bound (R dL : R) (k : Z) r1 p2 s t e2 rr :
  (Z.abs k <= 137601)%Z -> Rabs R <= 0.0027077 -> Rabs dL <= bpow radix2 (-206) ->
  r1 = R + IZR k * (l2v + l3v + l4v + dL) -> p2 = rndF (IZR k * l2v) -> s = rndF (r1 - p2) ->
  t = r1 - p2 - s -> e2 = IZR k * l2v - p2 -> rr = rndF (rndF (t - e2) - rndF (IZR k * l3v)) ->
  Rabs (s + rr - R) <= bpow radix2 (-113).
Proof.
  intros Hk HR HdL Hr1 Hp2 Hs Ht He2 Hrr. subst rr e2 t s p2 r1.
  apply Rnot_lt_le. intros Hlt.
  apply (exp_reduction.l1 R (IZR k) dL).
  assert (Rn : round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) = IZR k).
  { apply round_generic.
    - unfold Gappa_round_def.rndNE. apply valid_rnd_N.
    - apply generic_format_FIX. exists (Float radix2 k 0); [unfold F2R; simpl; ring | reflexivity]. }
  assert (Kr : -137601 <= IZR k <= 137601) by (split; apply IZR_le; lia).
  apply Rabs_le_inv in HR. apply Rabs_le_inv in HdL.
  unfold exp_reduction.s1, exp_reduction.s2, exp_reduction.s3, exp_reduction.s4, Gappa_definitions.BND.
  rewrite Rn.
  split; [split; [split | ] | ].
  - cbv [Gappa_definitions.lower Gappa_definitions.upper exp_reduction.i1 exp_reduction.f1 exp_reduction.f2 Gappa_definitions.float2R F2R Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. simpl. lra.
  - cbv [Gappa_definitions.lower Gappa_definitions.upper exp_reduction.i2 exp_reduction.f3 exp_reduction.f4 Gappa_definitions.float2R F2R Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. simpl. lra.
  - cbv [Gappa_definitions.lower Gappa_definitions.upper exp_reduction.i3 exp_reduction.f5 exp_reduction.f6 Gappa_definitions.float2R F2R Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. simpl.
    simpl in HdL. lra.
  - intros Hb. unfold l2v, l3v, l4v in Hlt.
    set (v := _ + _ - R) in Hlt.
    assert (Hb' : IZR (-1) * bpow radix2 (-113) <= v <= IZR 1 * bpow radix2 (-113)) by exact Hb.
    apply (Rlt_irrefl (bpow radix2 (-113))). apply Rlt_le_trans with (1 := Hlt).
    apply Rabs_le. lra.
Qed.

Section Constants.

Variable dL : R.
Hypothesis HdL : Rabs dL <= bpow radix2 (-206).

Lemma L_range : 0.0054152123 <= l1v + l2v + l3v + l4v + dL <= 0.0054152124.
Proof. apply Rabs_le_inv in HdL. unfold l1v, l2v, l3v, l4v, F2R in *. simpl in *. lra. Qed.

Lemma inv_l_close : Rabs (B c_inv_l - / (l1v + l2v + l3v + l4v + dL)) <= bpow radix2 (-40).
Proof.
  pose proof L_range as [La Lb]. set (L := l1v + l2v + l3v + l4v + dL) in *.
  assert (E : Rabs (B c_inv_l * L - 1) <= bpow radix2 (-40) * 0.0054152123).
  { rewrite c_inv_l_val. apply Rabs_le_inv in HdL. apply Rabs_le. unfold L, l1v, l2v, l3v, l4v, F2R in *. simpl in *. split; lra. }
  replace (B c_inv_l - / L) with ((B c_inv_l * L - 1) * / L) by (field; lra).
  rewrite Rabs_mult, (Rabs_pos_eq (/ L)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  apply Rle_trans with (bpow radix2 (-40) * 0.0054152123 * / 0.0054152123).
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | exact E | apply Rinv_le_contravar; lra].
  - right. field. lra.
Qed.

End Constants.

(** Normalizes a [bnd 1 e] bound to a numeral. *)
Lemma one_mul v : IZR 1 * v = v.
Proof. ring. Qed.
Ltac pw := unfold bnd; rewrite ?one_mul;
  try change (bpow radix2 0) with 1%R; try change (bpow radix2 1) with 2%R;
  try change (bpow radix2 10) with 1024%R; try change (bpow radix2 11) with 2048%R.

(** [Reduced::of], steps 1–4: [(n, r1, p2, e2, r_hi, r_lo)]. *)
Definition reduce (x : f64) : f64 * f64 * f64 * f64 * f64 * f64 :=
  let n := fsub (fadd (fmul x c_inv_l) shifter) shifter in
  let r1 := fsub x (fmul n c_l1) in
  let '(p2, e2) := two_prod64 n c_l2 in
  let '(s, t) := two_sum64 r1 (fneg p2) in
  let rr := fsub (fsub t e2) (fmul n c_l3) in
  let '(rh, rl) := two_sum64 s rr in
  (n, r1, p2, e2, rh, rl).

(** For every [x] the kernel reduces, with [L = L1 + L2 + L3 + L4 + dL]: [n] is
    an integer [k], [|k| <= 137601]; [r1 = x − k·L1] and [p2 + e2 = k·L2]
    exactly; [|x − k·L| <= 0.0027077]; and [r_hi + r_lo] is within [2^−113] of
    [x − k·L]. *)
Theorem reduce_ok x dL : finite x -> -745.1333 <= B x <= 709.79 -> Rabs dL <= bpow radix2 (-206) ->
  let L := l1v + l2v + l3v + l4v + dL in
  let '(n, r1, p2, e2, rh, rl) := reduce x in
  exists k : Z, B n = IZR k /\ (Z.abs k <= 137601)%Z /\
    finite n /\ finite r1 /\ finite p2 /\ finite e2 /\ finite rh /\ finite rl /\
    B r1 = B x - IZR k * l1v /\ B p2 = rndF (IZR k * l2v) /\ B p2 + B e2 = IZR k * l2v /\
    Rabs (B x - IZR k * L) <= 0.0027077 /\
    Rabs (B rh + B rl - (B x - IZR k * L)) <= bpow radix2 (-113).
Proof.
  intros Fx Hx HdL L.
  destruct c_finite as [Fi [F1 [F2 F3]]].
  pose proof (L_range dL HdL) as Lr. pose proof (inv_l_close dL HdL) as Ic.
  change (l1v + l2v + l3v + l4v + dL) with L in Lr, Ic.
  pose proof (reduce_n L Lr Ic x Fx Hx) as Hn. cbv zeta in Hn.
  destruct Hn as [Fn [k [Bn [Kb Kx]]]].
  unfold reduce.
  set (n := fsub (fadd (fmul x c_inv_l) shifter) shifter) in *.
  assert (Kr : -137601 <= IZR k <= 137601) by (split; apply IZR_le; lia).
  assert (Rk : Rabs (IZR k) <= 137601) by (apply Rabs_le; lra).
  destruct Lr as [La Lb].
  (* the reduced argument *)
  set (R := B x - IZR k * L).
  assert (HR : Rabs R <= 0.0027077).
  { replace R with (L * (B x / L - IZR k)) by (unfold R; field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq L) by lra.
    apply Rle_trans with (0.0054152124 * (/ 2 + / 1000000000)); [ | lra].
    apply Rmult_le_compat; try lra. apply Rabs_pos. }
  assert (Big : k <> 0%Z -> bpow radix2 (-9) <= Rabs (B x)).
  { intros K0. assert (K1 : 1 <= Rabs (IZR k)).
    { rewrite <- abs_IZR. apply IZR_le. lia. }
    assert (Q : Rabs (B x / L) >= / 2 - / 1000000000).
    { pose proof (Rabs_triang_inv (IZR k) (IZR k - B x / L)) as T.
      replace (IZR k - (IZR k - B x / L)) with (B x / L) in T by ring.
      rewrite Rabs_minus_sym in T. lra. }
    replace (B x) with (L * (B x / L)) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq L) by lra.
    change (bpow radix2 (-9)) with (/ 512). nra. }
  (* x − n·L1 *)
  assert (L1d : Rabs (L - l1v) <= / 1000000000000).
  { apply Rabs_le_inv in HdL. unfold L, l1v, l2v, l3v, l4v, F2R in *. simpl in *.
    apply Rabs_le. split; lra. }
  assert (P1 : B n * B c_l1 = IZR (k * 23816355775) * bpow radix2 (-42)).
  { rewrite Bn, c_l1_eq. unfold l1v. rewrite mult_IZR. ring. }
  assert (P1b : Rabs (B n * B c_l1) <= 746).
  { rewrite Bn, c_l1_eq, Rabs_mult. unfold l1v.
    rewrite (Rabs_pos_eq (IZR 23816355775 * bpow radix2 (-42))) by (simpl; lra).
    apply Rle_trans with (137601 * (IZR 23816355775 * bpow radix2 (-42))).
    - apply Rmult_le_compat_r; [simpl; lra | exact Rk].
    - simpl. lra. }
  destruct (fmul_ok 1 10 n c_l1 Fn F1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(pw; lra)) as [Fm1 Bm1].
  assert (Em1 : B (fmul n c_l1) = IZR k * l1v).
  { rewrite Bm1, P1. rewrite round_generic; auto with typeclass_instances.
    - unfold l1v. rewrite mult_IZR. ring.
    - apply fmt_int; [ | lia]. rewrite Z.abs_mul. change (2 ^ 53)%Z with 9007199254740992%Z. lia. }
  assert (Dx : Rabs (B x - IZR k * l1v) < bpow radix2 (-8)).
  { replace (B x - IZR k * l1v) with (R + IZR k * (L - l1v)) by (unfold R; ring).
    apply Rle_lt_trans with (Rabs R + Rabs (IZR k) * Rabs (L - l1v)).
    - rewrite <- Rabs_mult. apply Rabs_triang.
    - change (bpow radix2 (-8)) with (/ 256).
      assert (Rabs (IZR k) * Rabs (L - l1v) <= 137601 * / 1000000000000)
        by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
      lra. }
  destruct (fsub_ok 1 11 x (fmul n c_l1) Fx Fm1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(pw; rewrite Em1; change (bpow radix2 (-8)) with (/ 256) in Dx; lra)) as [Fr1 Br1].
  set (r1 := fsub x (fmul n c_l1)) in *.
  assert (Er1 : B r1 = B x - IZR k * l1v).
  { rewrite Br1, Em1. apply round_generic; auto with typeclass_instances.
    unfold l1v. apply diff_exact; [apply B_fmt | | ].
    - exact Big.
    - exact Dx. }
  (* n·L2 *)
  assert (L2b : Rabs (B c_l2) <= bpow radix2 (-43)).
  { rewrite c_l2_val. unfold F2R. simpl. rewrite Rabs_left by lra. lra. }
  assert (Nb : Rabs (B n) <= bpow radix2 18) by (rewrite Bn; simpl; lra).
  assert (Dom : in_two_prod_domain (B n) (B c_l2)).
  { destruct (Z.eq_dec k 0) as [K0 | K0].
    - left. rewrite Bn, K0. ring.
    - right. rewrite Rabs_mult, Bn.
      assert (K1 : 1 <= Rabs (IZR k)) by (rewrite <- abs_IZR; apply IZR_le; lia).
      assert (L2l : bpow radix2 (-44) <= Rabs (B c_l2)) by (rewrite c_l2_val; unfold F2R; simpl; rewrite Rabs_left by lra; lra).
      apply Rle_trans with (Rabs (B c_l2)); [apply Rle_trans with (bpow radix2 (-44)); [apply bpow_le; lia | exact L2l] | ].
      pose proof (Rabs_pos (B c_l2)). nra. }
  pose proof (two_prod_ieee 18 (-43) n c_l2 Fn F2 Nb L2b ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  destruct (two_prod64 n c_l2) as [p2 e2]. destruct TP as [Fp [Fe [Bp Be]]].
  rewrite Bn, c_l2_val in Bp, Be. fold l2v in Bp, Be.
  assert (P2b : Rabs (IZR k * l2v) <= / 1000000).
  { rewrite Rabs_mult. apply Rle_trans with (137601 * / 1000000000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; [exact Rk | ].
    unfold l2v, F2R. simpl. rewrite Rabs_left by lra. lra. }
  assert (Bp2 : Rabs (B p2) <= 1).
  { rewrite Bp. replace 1 with (IZR 1 * bpow radix2 0) by (simpl; ring). apply bnd_round; [lia | lia | ].
    pw. lra. }
  (* two_sum(r1, −p2) *)
  assert (Fq : finite (fneg p2)) by (unfold fneg, b64_opp; now rewrite is_finite_Bopp).
  assert (Bq : B (fneg p2) = - B p2) by apply B2R_Bopp.
  assert (Rr1 : Rabs (B r1) <= bpow radix2 1020) by (rewrite Er1; apply Rlt_le, Rlt_le_trans with (1 := Dx); apply bpow_le; lia).
  assert (Rq : Rabs (B (fneg p2)) <= bpow radix2 1020) by (rewrite Bq, Rabs_Ropp; apply Rle_trans with 1; [exact Bp2 | simpl; lra]).
  pose proof (two_sum_ieee r1 (fneg p2) Fr1 Fq Rr1 Rq) as TS.
  destruct (two_sum64 r1 (fneg p2)) as [s t]. destruct TS as [Fs [Ft [Bs Bst]]].
  rewrite Bq in Bs, Bst.
  (* rr *)
  pose proof (rnd_abs_err (B r1 + - B p2)) as Es. rewrite <- Bs in Es.
  pose proof (rnd_abs_err (IZR k * l2v)) as Ee. rewrite <- Bp in Ee.
  assert (Tiny : 0 <= bpow radix2 (-1074) <= / 1024).
  { split; [apply bpow_ge_0 | ]. change (/ 1024) with (bpow radix2 (-10)). apply bpow_le. lia. }
  assert (Rx1 : Rabs (B r1) <= 1) by (rewrite Er1; change (bpow radix2 (-8)) with (/ 256) in Dx; lra).
  assert (Tb : Rabs (B t - B e2) <= 1).
  { replace (B t - B e2) with ((B r1 + - B p2 - B s) + - (IZR k * l2v - B p2)) by lra.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp, (Rabs_minus_sym (IZR k * l2v)).
    rewrite Rabs_minus_sym in Es.
    assert (Rabs (B r1 + - B p2) <= 2) by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra).
    lra. }
  destruct (fsub_ok 1 0 t e2 Ft Fe ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(pw; lra)) as [Fu1 Bu1].
  assert (U2b : Rabs (B n * B c_l3) <= 1).
  { rewrite Bn, c_l3_val, Rabs_mult. apply Rle_trans with (137601 * / 1000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; [exact Rk | ]. unfold F2R. simpl. rewrite Rabs_pos_eq by lra. lra. }
  destruct (fmul_ok 1 0 n c_l3 Fn F3 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(pw; lra)) as [Fu2 Bu2].
  assert (U1r : Rabs (B (fsub t e2)) <= 1)
    by (rewrite Bu1; replace 1 with (IZR 1 * bpow radix2 0) by (simpl; ring); apply bnd_round; [lia | lia | pw; lra]).
  assert (U2r : Rabs (B (fmul n c_l3)) <= 1)
    by (rewrite Bu2; replace 1 with (IZR 1 * bpow radix2 0) by (simpl; ring); apply bnd_round; [lia | lia | pw; lra]).
  assert (Db : Rabs (B (fsub t e2) - B (fmul n c_l3)) <= 2)
    by (unfold Rminus; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra).
  destruct (fsub_ok 1 1 (fsub t e2) (fmul n c_l3) Fu1 Fu2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(pw; lra)) as [Frr Brr].
  set (rr := fsub (fsub t e2) (fmul n c_l3)) in *.
  (* two_sum(s, rr) *)
  assert (Sb : Rabs (B s) <= bpow radix2 1020).
  { rewrite Bs. apply Rle_trans with (IZR 1 * bpow radix2 1); [ | simpl; lra].
    apply bnd_round; [lia | lia | pw]. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (RRb : Rabs (B rr) <= bpow radix2 1020).
  { rewrite Brr. apply Rle_trans with (IZR 1 * bpow radix2 1); [ | simpl; lra].
    apply bnd_round; [lia | lia | pw; lra]. }
  pose proof (two_sum_ieee s rr Fs Frr Sb RRb) as TS2.
  destruct (two_sum64 s rr) as [rh rl]. destruct TS2 as [Fh [Fl [_ Bhl]]].
  exists k. repeat split; try assumption.
  rewrite Bhl.
  apply (reduction_bound R dL k (B r1) (B p2) (B s) (B t) (B e2) (B rr) Kb HR HdL).
  - rewrite Er1. unfold R, L. ring.
  - exact Bp.
  - rewrite Bs. reflexivity.
  - lra.
  - lra.
  - rewrite Brr, Bu1, Bu2, Bn, c_l3_val. reflexivity.
Qed.
