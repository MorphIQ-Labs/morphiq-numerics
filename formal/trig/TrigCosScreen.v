(** The small cosine screen: discrete threshold gaps and the five rounded
    return values. Threshold endpoint bounds are certified independently. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingGaps RoundingTest.
From Interval Require Import Tactic.
Require Import TrigScreenConstants.
Open Scope R_scope.

Lemma trig_cos_decreasing x y : 0<=x<=y -> y<=1 -> cos y<=cos x.
Proof.
 intros [X XY] Y. destruct (Req_dec x y) as [Eq|Ne];[subst;lra|].
 pose proof PI_RGT_0 as P. assert (One:1<PI) by interval.
 pose proof (cos_decreasing_1 x y ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra));lra.
Qed.

Lemma trig_cos_above_step k x : B(trig_cos_step k)<B x ->
 B(trig_cos_step_next k)<=B x.
Proof.
 intro X. pose proof (trig_cos_step_bounds k) as [[Lower Adjacent] Upper].
 assert (Range:bpow radix2 (-1022)<=B(trig_cos_step k)<bpow radix2 1023).
 { split.
   - apply Rle_trans with (bpow radix2 (-27));[apply bpow_le;lia|lra].
   - apply Rlt_le_trans with (bpow radix2 (-25));[lra|apply bpow_le;lia]. }
 destruct (bits_up (trig_cos_step k) (trig_cos_step_finite k) Range) as [_ Up].
 assert (Bits:bits_of_b64 (trig_cos_step k)=trig_cos_step_bits k).
 { destruct k as [|[|[|k]]];vm_compute;reflexivity. }
 rewrite Bits in Up. change (B(trig_cos_step_next k)=succ radix2 (FLT_exp (-1074) 53) (B(trig_cos_step k))) in Up.
 rewrite Up. apply succ_le_lt;try apply B_fmt;try exact X.
 exact (@FLT_exp_valid (-1074) 53 ltac:(unfold Prec_gt_0;lia)).
Qed.

Definition trig_cos_result (k:nat) := b64_of_bits (4607182418800017408-Z.of_nat k).
Lemma trig_cos_result_value k : (k<=4)%nat ->
 B(trig_cos_result k)=1-INR k*bpow radix2 (-53).
Proof.
 intro K. destruct k as [|[|[|[|[|k]]]]];try lia;unfold trig_cos_result;cbn [INR].
 - change (4607182418800017408-Z.of_nat 0)%Z with 4607182418800017408%Z. rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-53)) with (/9007199254740992);field.
 - change (4607182418800017408-Z.of_nat 1)%Z with 4607182418800017407%Z. rewrite (bits_val 4607182418800017407 false 9007199254740991 53 eq_refl). cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-53)) with (/9007199254740992);field.
 - change (4607182418800017408-Z.of_nat 2)%Z with 4607182418800017406%Z. rewrite (bits_val 4607182418800017406 false 9007199254740990 53 eq_refl). cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-53)) with (/9007199254740992);field.
 - change (4607182418800017408-Z.of_nat 3)%Z with 4607182418800017405%Z. rewrite (bits_val 4607182418800017405 false 9007199254740989 53 eq_refl). cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-53)) with (/9007199254740992);field.
 - change (4607182418800017408-Z.of_nat 4)%Z with 4607182418800017404%Z. rewrite (bits_val 4607182418800017404 false 9007199254740988 53 eq_refl). cbn [SpecFloat.cond_Zopp]. change (bpow radix2 (-53)) with (/9007199254740992);field.
Qed.
Lemma trig_cos_result_finite k : (k<=4)%nat -> finite(trig_cos_result k).
Proof. intro K;destruct k as [|[|[|[|[|k]]]]];try lia;vm_compute;reflexivity. Qed.
Lemma trig_cos_result_range k : (k<=4)%nat -> /2<B(trig_cos_result k)<=1.
Proof.
 intro K;rewrite trig_cos_result_value by exact K.
 destruct k as [|[|[|[|[|k]]]]];try lia;cbn [INR];split;interval with (i_prec 100).
Qed.

Lemma trig_cos_result_gaps k : (k<=4)%nat ->
 bpow radix2 (-53)<=ulp radix2 (FLT_exp emin prec) (B(trig_cos_result k)) /\
 bpow radix2 (-53)<=B(trig_cos_result k)-pred radix2 (FLT_exp emin prec) (B(trig_cos_result k)).
Proof.
 intro K. pose proof (B_fmt (trig_cos_result k)) as F.
 pose proof (trig_cos_result_range k K) as Range.
 destruct k as [|k].
 - pose proof (relative_gaps (B(trig_cos_result O)) F ltac:(lra)) as [A C].
   rewrite (trig_cos_result_value O ltac:(lia)) in A,C |- *;cbn [INR] in *;split;lra.
 - assert (Strict:B(trig_cos_result (S k))<1).
   { rewrite trig_cos_result_value by exact K.
     assert (N:0<INR(S k)) by (apply lt_0_INR;lia).
     pose proof (bpow_gt_0 radix2 (-53));nra. }
   assert (Mag:(mag radix2 (B(trig_cos_result (S k))):Z)=0%Z).
   { apply mag_unique;rewrite Rabs_pos_eq by lra;change (/2<=B(trig_cos_result(S k))<1);lra. }
   assert (Ulp:ulp radix2 (FLT_exp emin prec) (B(trig_cos_result(S k)))=bpow radix2 (-53)).
   { rewrite ulp_neq_0 by lra;unfold cexp;rewrite Mag;reflexivity. }
   rewrite Ulp;split;[lra|].
   destruct (gap_below (B(trig_cos_result(S k))) F ltac:(lra)) as [_ Gap].
   assert (NotPower:B(trig_cos_result(S k))<>bpow radix2 (mag radix2 (B(trig_cos_result(S k)))-1)).
   { rewrite Mag;change (B(trig_cos_result(S k))<>/2);lra. }
   specialize (Gap NotPower).
   change (B(trig_cos_result(S k))-pred radix2 (FLT_exp emin prec) (B(trig_cos_result(S k)))=ulp radix2 (FLT_exp emin prec) (B(trig_cos_result(S k)))) in Gap.
   rewrite Gap,Ulp;lra.
Qed.

Lemma trig_cos_result_round k z : (k<=4)%nat ->
 Rabs(z-B(trig_cos_result k))<bpow radix2 (-54) -> rndF z=B(trig_cos_result k).
Proof.
 intros K Error. destruct (trig_cos_result_gaps k K) as [Above Below].
 pose proof (trig_cos_result_range k K) as Range.
 apply (round_within (B(trig_cos_result k)) z (bpow radix2 (-53)) (B_fmt _) ltac:(lra) Above Below).
 assert (Half:bpow radix2 (-53)/2=bpow radix2 (-54)) by (change (/9007199254740992/2=/18014398509481984);field).
 rewrite Half;exact Error.
Qed.

Definition trig_cos_cell k x :=
 (k<=4)%nat /\ 0<=B x<bpow radix2 (-25) /\
 (k=O \/ B(trig_cos_step (k-1))<B x) /\
 (k=4%nat \/ B x<=B(trig_cos_step k)).

Theorem trig_cos_cell_round k x : trig_cos_cell k x ->
 rndF(cos(B x))=B(trig_cos_result k).
Proof.
 intros [K [Range [Lower Upper]]].
 assert (Small:bpow radix2 (-25)<1) by interval.
 assert (Half:0<bpow radix2 (-54)) by apply bpow_gt_0.
 assert (Scale:bpow radix2 (-53)=2*bpow radix2 (-54)) by (change (/9007199254740992=2*/18014398509481984);field).
 apply trig_cos_result_round;[exact K|]. rewrite trig_cos_result_value by exact K.
 assert (Lo:1-(2*INR k+1)*bpow radix2 (-54)<cos(B x)).
 { destruct (Nat.eq_dec k 4) as [Four|NotFour].
   - subst k. pose proof (trig_cos_decreasing (B x) (bpow radix2 (-25)) ltac:(lra) ltac:(lra)) as Monotone.
     pose proof trig_cos_small_lower as Endpoint. cbn [INR];lra.
   - assert (Less:(k<4)%nat) by lia.
     destruct Upper as [Impossible|Below];[contradiction|].
     pose proof (trig_cos_step_lower k Less) as Endpoint.
     pose proof (trig_cos_step_bounds k) as [[_ T] U].
     pose proof (trig_cos_decreasing (B x) (B(trig_cos_step k)) ltac:(lra) ltac:(lra)) as Monotone;lra. }
 assert (Hi:cos(B x)<1-(2*INR k-1)*bpow radix2 (-54)).
 { destruct k as [|k].
   - cbn [INR]. pose proof (COS_bound (B x));lra.
   - destruct Lower as [Impossible|Above];[discriminate|].
     replace (S k-1)%nat with k in Above by lia.
     pose proof (trig_cos_above_step k x Above) as Next.
     pose proof (trig_cos_step_next_upper k ltac:(lia)) as Endpoint.
     pose proof (trig_cos_step_bounds k) as [[StepLower T] U].
     assert (Pos:0<B(trig_cos_step_next k)) by (pose proof (bpow_gt_0 radix2 (-27));lra).
     pose proof (trig_cos_decreasing (B(trig_cos_step_next k)) (B x) ltac:(lra) ltac:(lra)) as Monotone.
     rewrite S_INR;nra. }
 rewrite Scale. apply Rabs_lt;split;nra.
Qed.

Definition trig_cos_pass k x :=
 match Bcompare 53 1024 (trig_cos_step k) x with Some Lt=>true | _=>false end.
Lemma trig_cos_pass_correct k x : finite x ->
 (trig_cos_pass k x=true <-> B(trig_cos_step k)<B x) /\
 (trig_cos_pass k x=false <-> B x<=B(trig_cos_step k)).
Proof.
 intro F;unfold trig_cos_pass.
 rewrite (Bcompare_correct 53 1024 _ x (trig_cos_step_finite k) F).
 destruct (Rcompare_spec (B(trig_cos_step k)) (B x));split;split;intros;try reflexivity;try discriminate;lra.
Qed.
Definition trig_cos_count x : nat :=
 if trig_cos_pass 0 x then
  if trig_cos_pass 1 x then
   if trig_cos_pass 2 x then
    if trig_cos_pass 3 x then 4 else 3
   else 2
  else 1
 else 0.
Theorem trig_cos_count_cell x : finite x -> 0<=B x<bpow radix2 (-25) ->
 trig_cos_cell (trig_cos_count x) x.
Proof.
 intros F Range.
 destruct (trig_cos_pass_correct 0 x F) as [T0 F0].
 destruct (trig_cos_pass_correct 1 x F) as [T1 F1].
 destruct (trig_cos_pass_correct 2 x F) as [T2 F2].
 destruct (trig_cos_pass_correct 3 x F) as [T3 F3].
 unfold trig_cos_count,trig_cos_cell.
 repeat match goal with
 | |- context [if trig_cos_pass ?k x then _ else _] => destruct (trig_cos_pass k x) eqn:?
 end.
 all: split;[lia|];split;[exact Range|];split;
   first [left;reflexivity | right;cbn [Nat.sub];tauto].
Qed.
Definition trig_cos_eval k :=
 fsub (b64_of_bits 4607182418800017408)
  (fmul (binary_normalize 53 1024 eq_refl eq_refl mode_NE (Z.of_nat k) 0 false)
        (b64_of_bits 4368491638549381120)).
Lemma trig_cos_eval_result k : (k<=4)%nat -> trig_cos_eval k=trig_cos_result k.
Proof.
 intro K.
 assert (Bits:bits_of_b64(trig_cos_eval k)=bits_of_b64(trig_cos_result k)).
 { destruct k as [|[|[|[|[|k]]]]];try lia;vm_compute;reflexivity. }
 apply (f_equal b64_of_bits) in Bits.
 unfold bits_of_b64,b64_of_bits in Bits.
 repeat rewrite binary_float_of_bits_of_binary_float in Bits;exact Bits.
Qed.
Definition trig_cos_small x := trig_cos_eval (trig_cos_count x).
Theorem trig_cos_small_correct x : finite x -> 0<=B x<bpow radix2 (-25) ->
 finite(trig_cos_small x) /\ B(trig_cos_small x)=rndF(cos(B x)).
Proof.
 intros F Range. pose proof (trig_cos_count_cell x F Range) as Cell.
 pose proof (proj1 Cell) as K. unfold trig_cos_small;rewrite trig_cos_eval_result by exact K.
 split;[apply trig_cos_result_finite;exact K|symmetry;apply trig_cos_cell_round;exact Cell].
Qed.

Theorem trig_cos_abs_small_correct x : finite x -> Rabs(B x)<bpow radix2 (-25) ->
 finite(trig_cos_small (b64_abs x)) /\
 B(trig_cos_small (b64_abs x))=rndF(cos(B x)).
Proof.
 intros F Range.
 pose proof (is_finite_Babs 53 1024 unop_nan_pl64 x) as AbsFinite.
 fold (b64_abs x) in AbsFinite;rewrite F in AbsFinite.
 assert (AbsValue:B(b64_abs x)=Rabs(B x)) by apply B_abs.
 destruct (trig_cos_small_correct (b64_abs x) AbsFinite) as [Y Value].
 - rewrite AbsValue;split;[apply Rabs_pos|exact Range].
 - split;[exact Y|]. rewrite AbsValue in Value.
   destruct (Rle_lt_dec 0 (B x)) as [Pos|Neg].
   + rewrite Rabs_pos_eq in Value by exact Pos;exact Value.
   + rewrite Rabs_left,cos_neg in Value by exact Neg;exact Value.
Qed.
