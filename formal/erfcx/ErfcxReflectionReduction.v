(** The negative erfcx branch reduces the double-word square before the
    shared exponential evaluation. The low square word is added after the
    three-word ln(2)/512 reduction, with one additional IEEE rounding. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings RoundingConstant.
From Gappa Require Import Gappa_library.
Require Import ExpStageTables StageGappa ExpStageReduction.
Require erfcx_reflection_reduction.
Open Scope R_scope.

Lemma reflection_reduction_bound (R dL dh se : R) (k : Z) :
  (Z.abs k <= 565000)%Z -> Rabs R <= 0.000677 -> Rabs dL <= bpow radix2 (-129) ->
  Rabs dh <= bpow radix2 (-41) -> Rabs se <= bpow radix2 (-44) ->
  let r1 := R + IZR k * (l2_g + l3_g + dL) in
  let rh := rn (r1 - IZR k * l2_g) + dh in
  let rt := rn (rn (r1 - rh - IZR k * l2_g - rn (IZR k * l3_g)) + se) in
  Rabs (rh + rt - (R + se)) <= bpow radix2 (-92) /\
  Rabs rt <= bpow radix2 (-40) /\ Rabs rh <= 0.000678.
Proof.
  intros Hk HR HdL Hdh Hse. cbv zeta.
  assert (Hn : -565000 <= round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) <= 565000)
    by (rewrite rnd_int; split; apply IZR_le; lia).
  apply Rabs_le_inv in HR. apply Rabs_le_inv in HdL.
  apply Rabs_le_inv in Hdh. apply Rabs_le_inv in Hse.
  rewrite <- (rnd_int k). unfold l2_g, l3_g.
  split; [ | split]; apply Rabs_le;
    gappa_goal (erfcx_reflection_reduction.l1 R (IZR k) dL dh se).
Qed.

Definition reflection_reduced64 n r1 se : f64 * f64 :=
  let p2 := fmul n st_l2 in
  let rh := fsub (fadd (fsub r1 p2) c_split) c_split in
  let rt0 := fsub (fsub (fsub r1 rh) p2) (fmul n st_l3) in
  (rh, fadd rt0 se).

Theorem reflection_reduced_ieee x n r1 se (ni : Z) :
  finite x -> finite n -> B n = IZR ni -> (Z.abs ni <= 565000)%Z -> finite r1 ->
  B r1 = B x - IZR ni * B st_l1 -> Rabs (B x - IZR ni * L) <= 0.000677 ->
  Rabs (B r1) < bpow radix2 (-10) ->
  (ni <> 0%Z -> on_grid (-63) (B r1)) -> (ni = 0%Z -> B r1 = B x) ->
  finite se -> Rabs (B se) <= bpow radix2 (-44) ->
  let '(rh,rt) := reflection_reduced64 n r1 se in
  finite rh /\ finite rt /\ on_grid (-40) (B rh) /\
  Rabs (B rh) <= 0.000678 /\ Rabs (B rt) <= bpow radix2 (-40) /\
  Rabs (B rh + B rt - (B x - IZR ni * L + B se)) <= bpow radix2 (-92).
Proof.
  intros Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1 Fse Hse.
  unfold reflection_reduced64. cbv zeta.
  set (p2 := fmul n st_l2).
  set (rh := fsub (fadd (fsub r1 p2) c_split) c_split).
  set (rt0 := fsub (fsub (fsub r1 rh) p2) (fmul n st_l3)).
  destruct (stage_b_r_model x n r1 ni Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1)
    as [Frh [Frt0 [Grh [Dh Brt0]]]].
  fold p2 rh rt0 in Frh, Frt0, Grh, Dh, Brt0.
  assert (Model : forall lo, Rabs lo <= bpow radix2 (-44) ->
    Rabs (B rh + rn (B rt0 + lo) - (B x - IZR ni * L + lo)) <= bpow radix2 (-92) /\
    Rabs (rn (B rt0 + lo)) <= bpow radix2 (-40) /\ Rabs (B rh) <= 0.000678).
  { intros lo Hlo.
    pose proof (reflection_reduction_bound (B x - IZR ni * L)
      (L - B st_l1 - B st_l2 - B st_l3)
      (B rh - rn (B r1 - IZR ni * B st_l2)) lo ni Hn HR split_3 Dh Hlo) as SB.
    cbv zeta in SB. rewrite <- l2_g_eq, <- l3_g_eq in SB.
    replace (B x - IZR ni * L + IZR ni * (B st_l2 + B st_l3 +
      (L - B st_l1 - B st_l2 - B st_l3))) with (B r1) in SB by (rewrite Br1; ring).
    replace (rn (B r1 - IZR ni * B st_l2) +
      (B rh - rn (B r1 - IZR ni * B st_l2))) with (B rh) in SB by ring.
    rewrite <- Brt0 in SB. exact SB. }
  assert (Rt0b : Rabs (B rt0) <= bpow radix2 (-40)).
  { destruct (Model 0 ltac:(rewrite Rabs_R0; apply bpow_ge_0)) as [_ [H _]].
    rewrite Rplus_0_r, round_generic in H by (exact _ || apply B_fmt). exact H. }
  destruct (fadd16 rt0 se Frt0 Fse) as [Frt Brt].
  { apply Rle_trans with (1 := Rabs_triang _ _).
    change (bpow radix2 (-40)) with (/1099511627776) in Rt0b.
    change (bpow radix2 (-44)) with (/17592186044416) in Hse. lra. }
  rewrite rndF_rn in Brt.
  destruct (Model (B se) Hse) as [Err [Rt Rh]]. rewrite <- Brt in Err, Rt.
  repeat split; assumption.
Qed.

Definition reflection_reduce64 x se : Z * Z * f64 * f64 :=
  let '(n,j,k,r1) := stage_of x in
  let '(rh,rt) := reflection_reduced64 n r1 se in
  (j,k,rh,rt).

Theorem reflection_reduce_ieee x se :
  finite x -> Rabs (B x) < 710 -> finite se -> Rabs (B se) <= bpow radix2 (-44) ->
  let '(j,k,rh,rt) := reflection_reduce64 x se in
  exists ni : Z, ni = (512*k+j)%Z /\ (0 <= j < 512)%Z /\ (-1025 <= k <= 1025)%Z /\
    finite rh /\ finite rt /\ on_grid (-40) (B rh) /\
    Rabs (B rh) <= 0.000678 /\ Rabs (B rt) <= bpow radix2 (-40) /\
    Rabs (B x - IZR ni * L + B se) <= 0.000677 /\
    Rabs (B rh + B rt - (B x - IZR ni * L + B se)) <= bpow radix2 (-92).
Proof.
  intros Fx Hx Fse Hse. unfold reflection_reduce64.
  pose proof (stage_of_extended_ok x Fx Hx) as H.
  destruct (stage_of x) as [[[n j] k] r1].
  destruct H as [ni [Bn [Fn [Ni [Nk [J [K [Fr [Br [Hr [Rb [Gr Zr]]]]]]]]]]]].
  pose proof (reflection_reduced_ieee x n r1 se ni Fx Fn Bn ltac:(lia)
    Fr Br ltac:(lra) Rb Gr Zr Fse Hse) as Red.
  destruct (reflection_reduced64 n r1 se) as [rh rt].
  assert (HR : Rabs (B x - IZR ni * L + B se) <= 0.000677).
  { apply Rle_trans with (1 := Rabs_triang _ _).
    change (bpow radix2 (-44)) with (/17592186044416) in Hse. lra. }
  destruct Red as [Frh [Frt [Grh [Rh [Rt Err]]]]].
  exists ni. repeat split; try assumption; lia.
Qed.

Theorem reflection_reduce_wide_ieee x se :
  finite x -> Rabs (B x) < 762 -> finite se -> Rabs (B se) <= bpow radix2 (-44) ->
  let '(j,k,rh,rt) := reflection_reduce64 x se in
  exists ni : Z, ni = (512*k+j)%Z /\ (0 <= j < 512)%Z /\ (-1100 <= k <= 1100)%Z /\
    finite rh /\ finite rt /\ on_grid (-40) (B rh) /\
    Rabs (B rh) <= 0.000678 /\ Rabs (B rt) <= bpow radix2 (-40) /\
    Rabs (B x - IZR ni * L + B se) <= 0.000677 /\
    Rabs (B rh + B rt - (B x - IZR ni * L + B se)) <= bpow radix2 (-92).
Proof.
  intros Fx Hx Fse Hse. unfold reflection_reduce64.
  pose proof (stage_of_wide_ok x Fx Hx) as H.
  destruct (stage_of x) as [[[n j] k] r1].
  destruct H as [ni [Bn [Fn [Ni [Nk [J [K [Fr [Br [Hr [Rb [Gr Zr]]]]]]]]]]]].
  pose proof (reflection_reduced_ieee x n r1 se ni Fx Fn Bn ltac:(lia)
    Fr Br ltac:(lra) Rb Gr Zr Fse Hse) as Red.
  destruct (reflection_reduced64 n r1 se) as [rh rt].
  assert (HR : Rabs (B x - IZR ni * L + B se) <= 0.000677).
  { apply Rle_trans with (1 := Rabs_triang _ _).
    change (bpow radix2 (-44)) with (/17592186044416) in Hse. lra. }
  destruct Red as [Frh [Frt [Grh [Rh [Rt Err]]]]].
  exists ni. repeat split; try assumption; lia.
Qed.
