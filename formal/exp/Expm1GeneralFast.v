(** The general fallback's subtraction, exact scaling and renormalization,
    composed from the input's actual reduction. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid RoundingTest Encodings.
Require Import ExpFast Expm1GeneralBounds Expm1GeneralScale Expm1GeneralSum
 Expm1GeneralSubtract Expm1GeneralReduction Expm1Scale Ln1pLemmas StageGappa.
Open Scope R_scope.
Lemma em_rnd_lower e v : (-1074 <= e)%Z -> bpow radix2 e <= Rabs v ->
 bpow radix2 e <= Rabs (rndF v).
Proof.
 intros E V. rewrite <- round_NE_abs by auto with typeclass_instances.
 rewrite <- (round_generic radix2 (FLT_exp emin prec) (Znearest ne) (bpow radix2 e)) at 1
   by (auto with typeclass_instances; apply fmt_pow; exact E).
 apply round_le; auto with typeclass_instances.
Qed.
Definition em_rescale h l k := two_sum64 (scale h k) (scale l k).
Theorem em_rescale_ok h l k x z : finite x -> B x < B c_x_overflow -> /32 <= Rabs (B x) ->
 finite h -> finite l -> B h = rndF (B h+B l) ->
 on_grid (Z.min (-1020) (-k)) (B h) -> on_grid (Z.min (-1020) (-k)) (B l) ->
 (-54 <= k <= 1024)%Z -> 9/10 <= z <= 21/10 -> exp (B x) = z*bpow radix2 k ->
 Rabs ((B h+B l)*bpow radix2 k-(exp (B x)-1)) <= /2^62*Rabs (exp (B x)-1) ->
 let '(v,t) := em_rescale h l k in
 finite v /\ finite t /\ B v = rndF (B v+B t) /\
 bpow radix2 (-900) <= Rabs (B v) < bpow radix2 1024 /\
 Rabs (B v+B t-(exp (B x)-1)) <= /2^62*Rabs (exp (B x)-1).
Proof.
 intros Fx Ov X Fh Fl DW Gh Gl K Z Ex Err.
 set (m := B h+B l) in *. set (w := exp (B x)-1) in *.
 set (s := bpow radix2 k) in *. pose proof (bpow_gt_0 radix2 k) as S. fold s in S.
 assert (Id : w = (z-bpow radix2 (-k))*s).
 { unfold w. rewrite Ex. unfold s. rewrite Rmult_minus_distr_r, <-bpow_plus,Z.add_opp_diag_l. change (bpow radix2 0) with 1. ring. }
 assert (Un : Rabs (m-(z-bpow radix2 (-k))) <= /2^62*Rabs (z-bpow radix2 (-k))).
 { rewrite Id in Err. replace (m*s-(z-bpow radix2 (-k))*s) with ((m-(z-bpow radix2 (-k)))*s) in Err by ring.
   rewrite !Rabs_mult,(Rabs_pos_eq s) in Err by lra. nra. }
 destruct (em_unscaled_range (B x) z k K X Z Ex) as [Ul [Uh Up]].
 assert (Ml : bpow radix2 (-9) <= Rabs m).
 { pose proof (Rabs_triang_inv (z-bpow radix2 (-k)) m) as T. rewrite (Rabs_minus_sym (z-bpow radix2 (-k)) m) in T.
   assert (C : /2^62 <= /2) by interval with (i_prec 64).
   bpow_num_in Ul. bpow_num. pose proof (Rabs_pos (z-bpow radix2 (-k))). nra. }
 pose proof (em_nonzero (B x) X) as Wl. fold w in Wl.
 assert (Sl : bpow radix2 (-7) <= Rabs (m*s)).
 { pose proof (Rabs_triang_inv w (m*s)) as T. rewrite Rabs_minus_sym in T.
   assert (C : /2^62 <= /2) by interval with (i_prec 64). bpow_num. pose proof (Rabs_pos w). nra. }
 assert (M0 : m <> 0) by (intros E; rewrite E,Rabs_R0 in Ml; pose proof (bpow_gt_0 radix2 (-9)); lra).
 assert (Mag : (-8 <= mag radix2 m)%Z) by (apply mag_ge_bpow; exact Ml).
 assert (Round : B h*s = rndF (m*s)).
 { unfold s. rewrite round_scale by (try exact M0; lia). rewrite <-DW. reflexivity. }
 assert (Hl : bpow radix2 (-900) <= Rabs (B h*s)).
 { rewrite Round. apply Rle_trans with (bpow radix2 (-7)); [apply bpow_le; lia | apply em_rnd_lower; [lia | exact Sl]]. }
 assert (RawHl : bpow radix2 (-900) <= Rabs (B h)).
 { rewrite DW. apply Rle_trans with (bpow radix2 (-9)); [apply bpow_le; lia | apply em_rnd_lower; [lia | exact Ml]]. }
 pose proof (lo_bound (B h) (B l) RawHl DW) as Low.
 pose proof (exp_below_overflow x Fx Ov) as Eb.
 pose proof (exp_pos (B x)) as Ep.
 set (big := bpow radix2 1024).
 assert (Big : 1 <= big*(1-/2^46)) by (unfold big; interval with (i_prec 64)).
 assert (Wb : Rabs w <= big*(1-/2^46)).
 { apply Rabs_le. unfold w,big in *. replace (bpow radix2 1024) with (2^1024) in * by (rewrite bpow_powerRZ; reflexivity). lra. }
 assert (Mb : Rabs (m*s) <= (1+/2^62)*big*(1-/2^46)).
 { pose proof (Rabs_triang_inv (m*s) w). pose proof (Rabs_pos w). nra. }
 assert (Bnd : bnd (2^53-64) 971 (m*s)).
 { unfold bnd. apply Rle_trans with (1:=Mb). unfold big. interval with (i_prec 128). }
 assert (Hb : bnd (2^53-64) 971 (B h*s)).
 { rewrite Round. apply bnd_round; [lia | lia | exact Bnd]. }
 assert (Hov : Rabs (B h*s) < bpow radix2 1024) by (apply Rle_lt_trans with (1:=Hb); apply bnd_lt; lia).
 assert (Lb : bnd 2 971 (B l*s)).
 { unfold bnd in *. rewrite !Rabs_mult,(Rabs_pos_eq s) by lra.
   rewrite Rabs_mult,(Rabs_pos_eq s) in Hb by lra.
   apply Rle_trans with (bpow radix2 (-52)*(Rabs (B h)*s)); [nra | ].
   apply Rle_trans with (bpow radix2 (-52)*(IZR (2^53-64)*bpow radix2 971)); [apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Hb] | ].
   rewrite <-Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | interval with (i_prec 128)]. }
 assert (Lov : Rabs (B l*s) < bpow radix2 1024) by (apply Rle_lt_trans with (1:=Lb); apply bnd_lt; lia).
 destruct (em_scale_exact h (Z.min (-1020) (-k)) k Fh Gh ltac:(lia) ltac:(lia) K Hov) as [Fv V].
 destruct (em_scale_exact l (Z.min (-1020) (-k)) k Fl Gl ltac:(lia) ltac:(lia) K Lov) as [Ft T].
 fold s in V,T.
 assert (D : B (scale h k) = rndF (B (scale h k)+B (scale l k))).
 { rewrite V,T, <-Rmult_plus_distr_r. exact Round. }
 pose proof (em_two_sum_large (scale h k) (scale l k) Fv Ft D) as Sum.
 rewrite V,T in Sum. specialize (Sum (bnd_weaken _ (2^53-4) _ _ Hb ltac:(lia)) Lb).
 unfold em_rescale. destruct (two_sum64 (scale h k) (scale l k)) as [v t].
 destruct Sum as [Fv' [Ft' [V' S']]].
 repeat split; try assumption.
 - rewrite S', <-Rmult_plus_distr_r, V'. exact Round.
 - rewrite V'; exact Hl.
 - rewrite V'; exact Hov.
 - rewrite S', <-Rmult_plus_distr_r. exact Err.
Qed.

Lemma em_z_range j R : (j < 128)%nat -> Rabs R <= 0.0027076063 ->
 9/10 <= exp (INR j*ln 2/128)*exp R <= 21/10.
Proof.
 intros J H. apply Rabs_le_inv in H.
 assert (Jr : 0 <= INR j <= 127).
 { split; [apply pos_INR | ]. assert (j <= 127)%nat by lia. apply le_INR in H0.
   rewrite (INR_IZR_INZ 127) in H0. exact H0. }
 generalize (INR j) Jr; intros v V.
 assert (T : 0.999 <= exp (v*ln 2/128) <= 2) by (split; interval with (i_prec 64)).
 assert (E : 0.99 <= exp R <= 1.01) by (split; interval with (i_prec 64)).
 split; nra.
Qed.
Definition em_general_fast_value x :=
 let '(j,k,_,_,_,_,rh,rl) := em_reduce x in
 let '(yh,yl) := fast_at rh rl (Z.to_nat j) in
 let '(h,l) := em_subtract_fast yh yl k in em_rescale h l k.
Theorem em_general_fast_bound x : finite x -> -37.43 <= B x ->
 B x < B c_x_overflow -> /32 <= Rabs (B x) ->
 let '(v,t) := em_general_fast_value x in
 finite v /\ finite t /\ B v = rndF (B v+B t) /\
 bpow radix2 (-900) <= Rabs (B v) < bpow radix2 1024 /\
 Rabs (B v+B t-(exp (B x)-1)) <= /2^62*Rabs (exp (B x)-1).
Proof.
 intros Fx Lo Hi X. pose proof (em_reduce_ok x Fx Lo Hi X) as RD.
 unfold em_general_fast_value. revert RD. generalize (em_reduce x).
 intros [[[[[[[j k] n] r1] p2] e2] rh] rl]
   [J [K [Bn [Fh [Fl [Dw [Gh [Gl [Err [HR [Nr Er]]]]]]]]]]].
 set (r := B x-IZR (128*k+j)*(ln 2/128)) in *.
 assert (Split : exp (B x) = exp (INR (Z.to_nat j)*ln 2/128)*exp r*bpow radix2 k).
 { rewrite <-ExpFast.exp_split. f_equal. unfold r. rewrite Z2Nat.id by lia. ring. }
 pose proof (fast_reduced_grid_ok rh rl (Z.to_nat j) r Fh Fl Dw Err HR Gh
   (grid_le (-151) (-967) _ ltac:(lia) Gl) ltac:(lia)) as FP.
 cbv zeta in FP. destruct (fast_at rh rl (Z.to_nat j)) as [yh yl].
 destruct FP as [Fyh [Fyl [Dy [Hy [Ey [Gyh Gyl]]]]]].
 pose proof (em_subtract_fast_ok yh yl k (B x) (exp (INR (Z.to_nat j)*ln 2/128)*exp r)
   Fyh Fyl Dy Hy Gyh Gyl Ey K X Split) as Sub.
 destruct (em_subtract_fast yh yl k) as [h l]. destruct Sub as [Fm [Fn [Dm [Gm [Gn Em]]]]].
 apply (em_rescale_ok h l k x (exp (INR (Z.to_nat j)*ln 2/128)*exp r)); try assumption.
 apply em_z_range; [lia | exact HR].
Qed.
Definition em_eps := b64_of_bits 4327959241903046660.
Lemma em_eps_ok : finite em_eps /\ B em_eps = /2^62*(1+bpow radix2 (-50)).
Proof.
 split; [exact (bits_finite 4327959241903046660 _ _ _ eq_refl) | ].
 unfold em_eps. rewrite (bits_val 4327959241903046660 false 4503599627370500 114 eq_refl).
 cbn [SpecFloat.cond_Zopp]. apply Rle_antisym; interval with (i_prec 128).
Qed.
Definition em_general_fast x := let '(h,l) := em_general_fast_value x in decide_with h l em_eps.
Theorem em_general_fast_ok x v : finite x -> -37.43 <= B x ->
 B x < B c_x_overflow -> /32 <= Rabs (B x) ->
 em_general_fast x = Some v -> finite v /\ B v = rndF (exp (B x)-1).
Proof.
 intros Fx Lo Hi X. pose proof (em_general_fast_bound x Fx Lo Hi X) as F.
 unfold em_general_fast. destruct (em_general_fast_value x) as [h l].
 destruct F as [Fh [Fl [Dw [H E]]]]; intros D.
 destruct em_eps_ok as [Fe Be].
 assert (Prod : B em_eps*Rabs (B h) <= bpow radix2 1020).
 { rewrite Be. apply Rle_trans with ((/2^62*(1+bpow radix2 (-50)))*bpow radix2 1024).
   - apply Rmult_le_compat_l; [interval with (i_prec 64) | lra].
   - interval with (i_prec 128). }
 destruct (decide_with_bounded_ok h l em_eps (exp (B x)-1) (/2^62) v Fh Fl Fe H Prod Dw)
   as [V R].
 - split; interval with (i_prec 64).
 - rewrite Be. split; [lra | interval with (i_prec 128)].
 - rewrite Rabs_minus_sym. exact E.
 - exact D.
 - subst v. split; [exact Fh | symmetry; exact R].
Qed.
