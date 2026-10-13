(** erfcx::exp_dw: the shared exponential stage at a double-word input,
    followed by exact Fast2Sum normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingConstant.
Require Import ExpStageTables StageGappa ExpStageReduction ExpStageA ExpStageB.
Require Import ErfcxReflectionReduction ErfcxReflectionSquare.
Open Scope R_scope.

Definition reflection_exp64 x se : f64 * f64 * Z :=
  let '(j,k,rh,rt) := reflection_reduce64 x se in
  let '(y,l) := stage_b_at rh rt (Z.to_nat j) in
  let '(yh,yl) := fast_two_sum64 y l in
  (yh,yl,k).

Theorem reflection_exp_ieee x se :
  finite x -> Rabs (B x) < 710 -> finite se -> Rabs (B se) <= bpow radix2 (-44) ->
  let '(yh,yl,k) := reflection_exp64 x se in
  finite yh /\ finite yl /\ (-1025 <= k <= 1025)%Z /\
  0.999 <= B yh <= 2.001 /\ Rabs (B yl) <= bpow radix2 (-52) /\
  B yh = rndF (B yh + B yl) /\
  Rabs (exp (B x + B se) / bpow radix2 k - (B yh + B yl)) <= IZR 209 * bpow radix2 (-78).
Proof.
  intros Fx Hx Fse Hse. unfold reflection_exp64.
  pose proof (reflection_reduce_ieee x se Fx Hx Fse Hse) as Red.
  revert Red. generalize (reflection_reduce64 x se). intros [[[j k] rh] rt] Red.
  destruct Red as [ni [Nk [J [K [Frh [Frt [Grh [Rh [Rt [HR Err]]]]]]]]]].
  pose proof (stage_b_at_extended_ok rh rt (Z.to_nat j)
    (B x - IZR ni * L + B se) Frh Frt Grh Rh Rt Err HR ltac:(lia)) as Stage.
  revert Stage. generalize (stage_b_at rh rt (Z.to_nat j)). intros [y l] Stage.
  destruct Stage as [Fy [Fl [Y [Low E]]]].
  assert (Yabs : Rabs (B y) <= bpow radix2 1021).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 2);
      [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  assert (Labs : Rabs (B l) <= bpow radix2 1021)
    by (apply Rle_trans with (1 := Low); apply bpow_le; lia).
  assert (Dom : Rabs (B l) <= Rabs (B y)).
  { change (bpow radix2 (-20)) with (/1048576) in Low.
    rewrite (Rabs_pos_eq (B y)) by lra. lra. }
  pose proof (fast_two_sum_ieee y l Fy Fl Yabs Labs (or_intror (or_introl Dom))) as FS.
  revert FS. generalize (fast_two_sum64 y l). intros [yh yl] FS.
  destruct FS as [Fyh [Fyl [High Exact]]].
  assert (Jr : 0 <= INR (Z.to_nat j) <= 511).
  { split; [apply pos_INR | ].
    replace 511 with (INR 511) by (rewrite INR_IZR_INZ; reflexivity).
    apply le_INR. lia. }
  assert (Ideal : 0.9993 <=
    exp (INR (Z.to_nat j) * ln 2 / 512) * exp (B x - IZR ni * L + B se) <= 2).
  { rewrite <- exp_plus. pose proof L_range as Lr. unfold L in Lr.
    pose proof (Rabs_le_inv _ _ HR) as Rr.
    assert (Zr : -0.000677 <= INR (Z.to_nat j) * ln 2 / 512 +
      (B x - IZR ni * L + B se) <= ln 2) by nra.
    split.
    - pose proof (exp_ineq1_le (INR (Z.to_nat j) * ln 2 / 512 +
        (B x - IZR ni * L + B se))). lra.
    - apply Rle_trans with (exp (ln 2));
        [apply exp_le; exact (proj2 Zr) | rewrite exp_ln; lra]. }
  assert (Sum : 0.9992 <= B y + B l <= 2.0001).
  { pose proof (Rabs_le_inv _ _ E) as Er.
    change (IZR 209) with 209 in Er.
    change (bpow radix2 (-78)) with (/302231454903657293676544) in Er.
    split; lra. }
  pose proof (rnd_err_below (B y + B l) 2 ltac:(lia)
    ltac:(change (bpow radix2 2) with 4; apply Rabs_le; lra)) as Round.
  rewrite <- High in Round.
  assert (Yh : 0.999 <= B yh <= 2.001).
  { pose proof (Rabs_le_inv _ _ Round) as Rr.
    change (bpow radix2 (2 - 54)) with (/4503599627370496) in Rr. split; lra. }
  assert (Yl : Rabs (B yl) <= bpow radix2 (-52)).
  { replace (B yl) with (- (B yh - (B y + B l))) by lra.
    rewrite Rabs_Ropp. exact Round. }
  assert (Scale : exp (B x + B se) =
    (exp (INR (Z.to_nat j) * ln 2 / 512) * exp (B x - IZR ni * L + B se)) * bpow radix2 k).
  { rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia. rewrite Nk. ring. }
  assert (Value : exp (B x + B se) / bpow radix2 k =
    exp (INR (Z.to_nat j) * ln 2 / 512) * exp (B x - IZR ni * L + B se)).
  { rewrite Scale. field. apply Rgt_not_eq, bpow_gt_0. }
  split; [exact Fyh | split; [exact Fyl | split; [exact K | split; [exact Yh | split; [exact Yl | split]]]]].
  - rewrite Exact. exact High.
  - rewrite Value, Exact. exact E.
Qed.

Theorem reflection_square_exp_ieee x : finite x -> B reflection_limit < B x < - /2 ->
  let '(s,se) := two_prod64 x x in
  let '(yh,yl,k) := reflection_exp64 s se in
  finite yh /\ finite yl /\ (-1025 <= k <= 1025)%Z /\
  0.999 <= B yh <= 2.001 /\ Rabs (B yl) <= bpow radix2 (-52) /\
  B yh = rndF (B yh + B yl) /\
  Rabs (exp (B x * B x) / bpow radix2 k - (B yh + B yl)) <= IZR 209 * bpow radix2 (-78).
Proof.
  intros Fx Hx. pose proof (reflection_square_ieee x Fx Hx) as Sq.
  destruct (two_prod64 x x) as [s se].
  destruct Sq as [Fs [Fse [Exact [S Low]]]].
  pose proof (reflection_exp_ieee s se Fs ltac:(rewrite Rabs_pos_eq; lra) Fse Low) as H.
  rewrite Exact in H. exact H.
Qed.

(** The reflection dispatch's exponent cases. In the subtraction case the
    positive argument lies wholly within the table kernel's domain. *)
Theorem reflection_dispatch_range x : finite x -> B reflection_limit < B x < - /2 ->
  let '(s,se) := two_prod64 x x in
  let '(j,k,rh,rt) := reflection_reduce64 s se in
  (0 <= k <= 1023)%Z /\ ((k <= 104)%Z -> /2 < - B x < 9).
Proof.
  intros Fx Hx. pose proof (reflection_square_ieee x Fx Hx) as Sq.
  destruct (two_prod64 x x) as [s se]. destruct Sq as [Fs [Fse [Exact [S Low]]]].
  pose proof (reflection_reduce_ieee s se Fs ltac:(rewrite Rabs_pos_eq; lra) Fse Low) as Red.
  destruct (reflection_reduce64 s se) as [[[j k] rh] rt].
  destruct Red as (ni & Nk & J & K & Frh & Frt & Grh & Rh & Rt & HR & Err).
  assert (Rem : Rabs (B x * B x - IZR ni * L) <= 0.000677).
  { replace (B x * B x - IZR ni * L) with (B s - IZR ni * L + B se) by lra. exact HR. }
  pose proof (Rabs_le_inv _ _ Rem) as Rr. pose proof L_range as Lr.
  pose proof reflection_limit_value as Limit.
  assert (X : -26.63 < B x < - /2) by lra.
  assert (Ni : (0 <= ni <= 524287)%Z).
  { split.
    - destruct (Z_le_gt_dec 0 ni); [assumption | ].
      assert (IZR ni <= -1) by (apply IZR_le; lia). nra.
    - destruct (Z_le_gt_dec ni 524287); [assumption | ].
      assert (524288 <= IZR ni) by (apply IZR_le; lia). nra. }
  split; [lia | ]. intros Kh.
  assert (IZR ni <= 53759) by (apply IZR_le; lia).
  assert (0 <= IZR ni) by (apply IZR_le; lia).
  split; nra.
Qed.
