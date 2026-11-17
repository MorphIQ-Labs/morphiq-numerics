(** The bounded normal CDF beyond [|x| = 8]: the actual binary64 sequence of
    the far-tail row of [fast/cdf.rs] (exact exponent split, the full bounded
    exponential, a fixed-coefficient tail polynomial), and the composed entry contract on
    [2^-33 <= |x| <= 45/2]: absolute error at most [2^-49], and relative error
    at most [2^-48] for [x < 0]. [FastCdf] proves the region [|x| <= 8]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool Classical.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings
  RoundingCore RoundingConstant RoundingGaps RoundingTest.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxDecision ErfcxPublicModel ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget
  ErfcxTableEvaluation ErfcxReciprocal NormalConstants NormalComparisons NormalCentered
  NormalTailAnalytic NormalErfcxSensitivity NormalErfcxFastScaled NormalPublicEntry NormalPublicModel
  NormalAccurateCentralCdf NormalFastDispatch NormalTailThresholdConstants FastExp FastErfcx FastNormalArgument FastCdfConstants
  FastCdfOde FastCdfApprox FastCdfBody FastCdf FastCdfFarArithmetic FastCdfFarRatio.
Open Scope R_scope.

Definition cdf_far_limit : f64 := b64_of_bits 4627026404658118656.

Lemma cdf_far_limit_ok : finite cdf_far_limit /\ B cdf_far_limit=45/2.
Proof.
  split;[exact (bits_finite 4627026404658118656 false 6333186975989760 (-48) eq_refl)|].
  unfold cdf_far_limit. rewrite (bits_val 4627026404658118656 false 6333186975989760 48 eq_refl).
  simpl. field.
Qed.

(** {1 The row} *)

Definition fast_cdf_far_lower64 a :=
  let '(p,e):=two_prod64 (fmul erfcx_negative_half a) a in
  let r:=fast_cdf_far_ratio64 a in
  fmul (fmul cdf_half (fast_exp_entry64 p)) (fadd r (fmul r e)).

Definition fast_cdf_far_outer64 x :=
  let lower:=fast_cdf_far_lower64 (b64_abs x) in
  if normal_lt x normal_zero then lower else fsub (erfcx_pow2 0) lower.
Definition fast_cdf_far64 x :=
  if normal_lt (erfcx_pow2 3) (b64_abs x) then fast_cdf_far_outer64 x else fast_cdf64 x.
(** Positive arguments beyond 8 stay with the strong owner: [Phi(a)] rounds to 1
    from [a ~ 8.4] and the strong entry returns it without evaluating a tail,
    so no accelerated row can beat it there. *)
Definition fast_cdf_far_screen64 x :=
  normal_le(erfcx_pow2(-33))(b64_abs x) &&
  (normal_le(b64_abs x)(erfcx_pow2 3) ||
   (normal_lt x normal_zero && normal_le(b64_abs x) cdf_far_limit)).

Definition cdf_far_domain (x:R) : Prop :=
  bpow radix2(-33)<=Rabs x /\ (Rabs x<=8 \/ (x<0 /\ Rabs x<=45/2)).
Definition fast_cdf_far_entry64 x :=
  if fast_cdf_far_screen64 x then fast_cdf_far64 x else normal_entry64 NormalCdf x.

(** {1 Algebra} *)

Lemma cdf_far_exp_first_order e : Rabs e<=bpow radix2 (-45) -> Rabs((1+e)-exp e)<=bpow radix2 (-89).
Proof. intros E. apply Rabs_le_inv in E. bpow_num_all. apply Rabs_le. split;interval with (i_taylor e, i_prec 200). Qed.

Lemma cdf_far_damped w x c : 0<w -> /2<=x -> Rabs c<=bpow radix2 (-89) ->
  Rabs(w*c)<=bpow radix2 (-88)*(w*x).
Proof.
  intros W X C. rewrite Rabs_mult,(Rabs_pos_eq w) by lra.
  assert (H89 : bpow radix2 (-89)=/2*bpow radix2 (-88)) by (bpow_num;lra).
  assert (H1 : w*Rabs c<=w*bpow radix2 (-89)) by (apply Rmult_le_compat_l;lra).
  rewrite H89 in H1.
  assert (w*(/2*bpow radix2 (-88))<=w*(x*bpow radix2 (-88))).
  { apply Rmult_le_compat_l;[lra|]. apply Rmult_le_compat_r;[apply bpow_ge_0|lra]. }
  lra.
Qed.

Lemma cdf_far_exp_correction P EY be : 0<P*EY/2 -> /2<=exp be ->
  Rabs((1+be)-exp be)<=bpow radix2 (-89) ->
  Rabs(P/2*(EY*(1+be))-P*exp be*EY/2)<=bpow radix2(-88)*(P*exp be*EY/2).
Proof.
  intros W X C.
  replace (P/2*(EY*(1+be))-P*exp be*EY/2) with ((P*EY/2)*((1+be)-exp be)) by field.
  replace (P*exp be*EY/2) with ((P*EY/2)*exp be) by field.
  apply cdf_far_damped;assumption.
Qed.

Lemma cdf_far_tail_correction br bre be EY d : Rabs(br-EY)<=d*EY -> Rabs(bre-br*be)<=bpow radix2(-98) ->
  0<=d -> 0<1+be -> 1/63<=EY*(1+be) ->
  Rabs(br+bre-EY*(1+be))<=(d+bpow radix2(-88))*(EY*(1+be)).
Proof.
  intros A Bv D E X.
  replace (br+bre-EY*(1+be)) with ((br-EY)*(1+be)+(bre-br*be)) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult,(Rabs_pos_eq (1+be)) by lra.
  assert (Rabs(br-EY)*(1+be)<=d*(EY*(1+be))).
  { replace (d*(EY*(1+be))) with ((d*EY)*(1+be)) by ring. apply Rmult_le_compat_r;lra. }
  assert (bpow radix2(-98)<=bpow radix2(-88)*(EY*(1+be))) by (bpow_num_all;lra).
  lra.
Qed.

Lemma cdf_far_erfcx_floor Y : 5<=Y<=16 -> 1/62<=gaussian_erfcx Y.
Proof.
  intros Y'. pose proof inv_sqrt_pi_positive as P.
  assert (Pl : 5641/10000<=inv_sqrt_pi) by (unfold inv_sqrt_pi;interval).
  pose proof (normal_erfcx_large_lower Y ltac:(lra)) as Lo.
  assert (1/62<=inv_sqrt_pi/(2*Y)).
  { apply (Rmult_le_reg_r (2*Y));[lra|]. replace (inv_sqrt_pi/(2*Y)*(2*Y)) with inv_sqrt_pi by (field;lra). nra. }
  lra.
Qed.

(** {1 The lower tail [Phi(-a)] for [8 < a <= 45/2]} *)

Theorem fast_cdf_far_lower_ok a : finite a -> 8<B a<=45/2 ->
  finite(fast_cdf_far_lower64 a) /\
  bpow radix2(-400)<=B(fast_cdf_far_lower64 a)<=bpow radix2(-45) /\
  normal_tail(B a)<=bpow radix2(-46) /\ bpow radix2(-399)<=normal_tail(B a) /\
  Rabs(B(fast_cdf_far_lower64 a)-normal_tail(B a))<=bpow radix2(-48)*normal_tail(B a).
Proof.
  intros Fa A. unfold fast_cdf_far_lower64. cbv zeta.
  assert (Apos : 0<B a) by lra.
  pose proof (bpow_gt_0 radix2 (-53)) as U.
  set (Y:=B a/sqrt 2) in *.
  assert (Ylo : 5.6<=Y).
  { unfold Y;apply (Rmult_le_reg_r (sqrt 2));[interval|];rewrite cdf_sqrt2_cancel;interval. }
  assert (Yhi : Y<=15.92).
  { unfold Y;apply (Rmult_le_reg_r (sqrt 2));[interval|];rewrite cdf_sqrt2_cancel;interval. }
  assert (Ypos : 0<Y) by lra.
  assert (U53 : bpow radix2 (-53)<=/2^50) by (bpow_num;lra).
  destruct (fast_cdf_far_ratio_ok a Fa ltac:(split;lra)) as [Fr CB].
  fold Y in CB.
  set (r:=fast_cdf_far_ratio64 a) in *. clearbody r.
  set (EY:=gaussian_erfcx Y) in *.
  assert (EYr : 1/62<=EY<=1).
  { split;[apply cdf_far_erfcx_floor;lra|apply normal_erfcx_unit_upper;lra]. }
  pose proof (Rabs_le_inv _ _ CB) as CBr.
  assert (Rr : 1/70<=B r<=2).
  { clear - CBr EYr. bpow_num_all. split; lra. }
  (* The exponent, exactly: p + e = -a^2/2. *)
  destruct erfcx_negative_half_ok as [Fnh Half].
  assert (Mag : (-32<=mag radix2(B a))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-33)<=Rabs(B a));rewrite Rabs_pos_eq by lra.
    assert (bpow radix2(-33)<=1) by (bpow_num;lra). lra. }
  assert (Fmt : F64(B erfcx_negative_half*B a)).
  { rewrite Half;replace(-/2*B a)with(-(B a*bpow radix2(-1)))by(bpow_num;ring).
    apply generic_format_opp,mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct (fmul_exact erfcx_negative_half a Fnh Fa Fmt) as [Fm Hm].
  { rewrite Half,Rabs_mult,(Rabs_pos_eq(B a))by lra.
    eapply Rle_lt_trans with 12;[rewrite Rabs_Ropp;rewrite Rabs_pos_eq by lra;nra|].
    change 12 with 12;apply (Rlt_le_trans _ (bpow radix2 4));[change(bpow radix2 4)with 16;lra|apply bpow_le;lia]. }
  rewrite Half in Hm. set (m:=fmul erfcx_negative_half a) in *. clearbody m.
  assert (Dom : in_two_prod_domain (B m) (B a)).
  { right. rewrite Hm. rewrite Rabs_mult,Rabs_mult,Rabs_Ropp,!(Rabs_pos_eq (B a)),(Rabs_pos_eq (/2)) by lra.
    assert (bpow radix2(-969)<=1) by (change 1 with (bpow radix2 0);apply bpow_le;lia).
    nra. }
  pose proof (two_prod_ieee 4 5 m a Fm Fa
    ltac:(rewrite Hm,Rabs_mult,Rabs_Ropp,Rabs_pos_eq,Rabs_pos_eq by lra;change(bpow radix2 4)with 16;lra)
    ltac:(rewrite Rabs_pos_eq by lra;change(bpow radix2 5)with 32;lra)
    ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  revert TP. destruct (two_prod64 m a) as [p e]. intros [Fp [Fe [Vp Sum]]].
  rewrite Hm in Sum, Vp.
  assert (Qv : bpow radix2(-5)<=B a*B a/2).
  { assert (bpow radix2(-5)<=1) by (change 1 with (bpow radix2 0);apply bpow_le;lia). nra. }
  assert (Qr : 32<=B a*B a/2<=253.2) by (split;nra).
  assert (Pv : B p=rndF(-(B a*B a/2))) by (rewrite Vp;f_equal;field).
  assert (Prange : -256<=B p<=-32).
  { rewrite Pv. split.
    - change(-256)with(-bpow radix2 8);apply round_ge_generic;[exact _|exact _| |change(-256<= -(B a*B a/2));lra].
      apply generic_format_opp,generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change(-32)with(-bpow radix2 5);apply round_le_generic;[exact _|exact _| |change(-(B a*B a/2)<= -32);lra].
      apply generic_format_opp,generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (Terror : Rabs(B p+B a*B a/2)<=bpow radix2(-53)*(B a*B a/2)).
  { assert (Normal : bpow radix2(-1022)<=Rabs(-(B a*B a/2))).
    { rewrite Rabs_Ropp,Rabs_pos_eq by lra. eapply Rle_trans with 1;[|lra].
      change 1 with (bpow radix2 0);apply bpow_le;lia. }
    pose proof (rnd_rel _ Normal) as K.
    change (Rabs(rndF(-(B a*B a/2))-(-(B a*B a/2)))<=bpow radix2(-53)*Rabs(-(B a*B a/2))) in K.
    rewrite <-Pv,Rabs_Ropp,(Rabs_pos_eq(B a*B a/2)) in K by lra.
    replace (B p+B a*B a/2) with (B p-(-(B a*B a/2))) by ring. exact K. }
  assert (Ee : Rabs(B e)<=bpow radix2(-45)).
  { replace (B e) with (-(B p+B a*B a/2)) by lra. rewrite Rabs_Ropp.
    eapply Rle_trans;[exact Terror|]. bpow_num_all. nra. }
  pose proof (Rabs_le_inv _ _ Ee) as Ee'.
  destruct (fast_exp_entry_ok p Fp ltac:(apply Rabs_lt;lra)) as [FE Eerr].
  set (E:=fast_exp_entry64 p) in *. clearbody E.
  assert (Ep : exp(B p)<=exp(-32)) by (apply exp_le;lra).
  assert (Epl : bpow radix2(-370)<=exp(B p)).
  { assert (exp(-256)<=exp(B p)) by (apply exp_le;lra).
    assert (bpow radix2(-370)<=exp(-256)) by (bpow_num;interval with (i_prec 200)).
    lra. }
  assert (Epu : exp(-32)<=bpow radix2(-46)) by (bpow_num;interval).
  pose proof (Rabs_le_inv _ _ Eerr) as Eerr'.
  assert (Erng : bpow radix2(-371)<=B E<=bpow radix2(-46)*2).
  { assert (bpow radix2(-370)*(1-bpow radix2(-51))<=exp(B p)*(1-bpow radix2(-51))) by (apply Rmult_le_compat_r;[bpow_num_all;lra|lra]).
    split;bpow_num_all;nra. }
  (* h = E/2 exactly. *)
  destruct cdf_half_ok as [Fhalf Hhalf].
  assert (MagE : (-372<=mag radix2(B E))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-373)<=Rabs(B E));rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-371));lra).
    eapply Rle_trans;[|exact (proj1 Erng)]. apply bpow_le;lia. }
  assert (FmtH : F64(B cdf_half*B E)).
  { rewrite Hhalf,Rmult_comm. change (/2) with (bpow radix2 (-1)). apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct (fmul_exact cdf_half E Fhalf FE FmtH) as [Fh Vh].
  { rewrite Hhalf,Rabs_mult,(Rabs_pos_eq(B E)) by(pose proof(bpow_gt_0 radix2(-371));lra).
    rewrite Rabs_pos_eq by lra.
    eapply Rle_lt_trans with (bpow radix2(-46));[nra|apply bpow_lt;lia]. }
  rewrite Hhalf in Vh. set (h:=fmul cdf_half E) in *. clearbody h.
  (* r e, r + r e, h (r + r e). *)
  assert (BRE : bnd 1 (-44) (B r*B e)).
  { unfold bnd. rewrite Rmult_1_l,Rabs_mult,(Rabs_pos_eq (B r)) by lra.
    assert (B r*Rabs(B e)<=2*bpow radix2(-45)) by (apply Rmult_le_compat;try lra;apply Rabs_pos).
    bpow_num_all. lra. }
  destruct (fmul_bnd 1 (-44) r e Fr Fe ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BRE) as [Fre [Vre _]].
  assert (Rre : Rabs(B(fmul r e)-B r*B e)<=bpow radix2(-98)).
  { rewrite Vre. apply (rnd_err_below _ (-44));[lia|]. unfold bnd in BRE. rewrite Rmult_1_l in BRE. exact BRE. }
  set (re:=fmul r e) in *. clearbody re.
  pose proof (Rabs_le_inv _ _ Rre) as Rre'.
  assert (BRE' : B r*B e<=bpow radix2 (-44) /\ -bpow radix2 (-44)<=B r*B e).
  { unfold bnd in BRE. rewrite Rmult_1_l in BRE. apply Rabs_le_inv in BRE. lra. }
  assert (Wr : 1/100<=B r+B re<=3).
  { assert (bpow radix2 (-98)<=bpow radix2 (-44)) by (apply bpow_le;lia). bpow_num_all. split;lra. }
  assert (BT : bnd 1 2 (B r+B re)) by (unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;change (bpow radix2 2) with 4;lra).
  destruct (fadd_bnd 1 2 r re Fr Fre ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BT) as [Ft [Vt _]].
  assert (Rt : Rabs(B(fadd r re)-(B r+B re))<=bpow radix2(-53)*(B r+B re)).
  { rewrite Vt. assert (N : bpow radix2 (-1022)<=Rabs(B r+B re)).
    { rewrite Rabs_pos_eq by lra. assert (bpow radix2 (-1022)<=1/100) by (bpow_num;lra). lra. }
    pose proof (rnd_rel _ N) as K. rewrite (Rabs_pos_eq (B r+B re)) in K by lra. exact K. }
  set (t:=fadd r re) in *. clearbody t.
  pose proof (Rabs_le_inv _ _ Rt) as Rt'.
  assert (Trng : 1/200<=B t<=4) by (clear - Wr Rt'; bpow_num_all;split;nra).
  assert (Hrng : bpow radix2(-372)<=B h<=1).
  { rewrite Vh. assert (H46 : bpow radix2(-46)<=1/1000) by (bpow_num;lra).
    assert (bpow radix2 (-372)=/2*bpow radix2 (-371)) by (bpow_num;lra).
    destruct Erng as [E1 E2]. split;lra. }
  pose proof (bpow_gt_0 radix2 (-372)) as P372.
  assert (BL : bnd 1 2 (B h*B t)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by nra;change (bpow radix2 2) with 4;nra. }
  destruct (fmul_bnd 1 2 h t Fh Ft ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BL) as [Fl [Vl _]].
  assert (Rl : Rabs(B(fmul h t)-B h*B t)<=bpow radix2(-53)*(B h*B t)).
  { rewrite Vl. assert (N : bpow radix2 (-1022)<=Rabs(B h*B t)).
    { rewrite Rabs_pos_eq by nra. assert (bpow radix2 (-1022)<=bpow radix2 (-372)*(1/200)) by (bpow_num;lra).
      assert (bpow radix2 (-372)*(1/200)<=B h*B t) by (apply Rmult_le_compat;try lra;apply bpow_ge_0). lra. }
    pose proof (rnd_rel _ N) as K. rewrite (Rabs_pos_eq (B h*B t)) in K by nra. exact K. }
  (* The real chain; every binary64 word above is opaque. *)
  clear Vre BRE BRE' Vt BT BL Vl MagE FmtH Fmt Mag Dom Hm Half Hhalf Vp Pv
    Fnh Fm Fhalf Fh Fre Ft Fr Fe FE Fp Fa Wr Trng Hrng.
  set (X2:=EY*(1+B e)).
  assert (Ebig : 999/1000<=1+B e<=1001/1000) by (bpow_num_all;lra).
  assert (X2r : 1/63<=X2<=2) by (unfold X2;split;nra).
  assert (T2 : Rabs(B r+B re-X2)<=(10*bpow radix2(-53)+bpow radix2(-88))*X2).
  { unfold X2. apply cdf_far_tail_correction;[exact CB|exact Rre|bpow_num_all;lra|bpow_num_all;lra|exact (proj1 X2r)]. }
  pose proof (cdf_rel_chain (B t) (B r+B re) X2 _ _ Rt T2 ltac:(lra) ltac:(lra) ltac:(bpow_num_all;lra)) as T3.
  apply (cdf_rel_weaken _ _ _ (12*bpow radix2(-53))) in T3;[|lra|bpow_num;interval].
  set (X1:=exp(B p)/2).
  assert (X1p : 0<X1) by (unfold X1;pose proof (exp_pos (B p));lra).
  assert (H1 : Rabs(B h-X1)<=bpow radix2(-51)*X1).
  { rewrite Vh. unfold X1. exact (cdf_half_rel _ _ _ Eerr). }
  pose proof (cdf_rel_mul (B h) X1 (B t) X2 _ _ H1 T3 ltac:(lra) ltac:(lra) ltac:(apply bpow_ge_0) ltac:(bpow_num_all;lra)) as T4.
  apply (cdf_rel_weaken _ _ _ (17*bpow radix2(-53))) in T4;[|nra|bpow_num;interval].
  pose proof (cdf_rel_chain (B(fmul h t)) (B h*B t) (X1*X2) _ _ Rl T4 ltac:(nra) ltac:(lra) ltac:(lra)) as T5.
  apply (cdf_rel_weaken _ _ _ (19*bpow radix2(-53))) in T5;[|nra|bpow_num;interval].
  set (T:=normal_tail(B a)).
  assert (Tid : T=exp(B p)*exp(B e)*EY/2).
  { unfold T,normal_tail. fold Y EY. rewrite <-exp_plus. f_equal. f_equal. f_equal. lra. }
  assert (Ee2 : /2<=exp(B e)<=2) by (bpow_num_all;split;interval).
  assert (Wp : 0<exp(B p)*EY/2) by (pose proof (exp_pos (B p));apply Rdiv_lt_0_compat;[apply Rmult_lt_0_compat|];lra).
  assert (T6 : Rabs(X1*X2-T)<=bpow radix2(-88)*T).
  { rewrite Tid. unfold X1,X2. apply cdf_far_exp_correction;[exact Wp|lra|exact (cdf_far_exp_first_order (B e) Ee)]. }
  assert (Tp : 0<T).
  { rewrite Tid. apply Rdiv_lt_0_compat;[|lra]. apply Rmult_lt_0_compat;[apply Rmult_lt_0_compat;apply exp_pos|lra]. }
  pose proof (cdf_rel_chain (B(fmul h t)) (X1*X2) T _ _ T5 T6 ltac:(lra) ltac:(lra) ltac:(apply bpow_ge_0)) as T7.
  apply (cdf_rel_weaken _ _ _ (bpow radix2(-48))) in T7;[|lra|bpow_num;interval].
  (* Ranges. *)
  pose proof (exp_pos (B p)) as Pp. pose proof (exp_pos (B e)) as Pe.
  assert (Tup : T<=bpow radix2(-46)).
  { rewrite Tid.
    assert (S1 : exp(B p)*exp(B e)<=exp(-32)*2) by (apply Rmult_le_compat;lra).
    assert (S2 : exp(B p)*exp(B e)*EY<=exp(-32)*2*1) by (apply Rmult_le_compat;try lra;nra).
    lra. }
  assert (Tlo : bpow radix2(-399)<=T).
  { rewrite Tid.
    assert (S1 : bpow radix2(-370)*(/2)<=exp(B p)*exp(B e)) by (apply Rmult_le_compat;try lra;apply bpow_ge_0).
    assert (S2 : bpow radix2(-370)*(/2)*(1/62)<=exp(B p)*exp(B e)*EY) by (apply Rmult_le_compat;try lra;[apply Rmult_le_pos;[apply bpow_ge_0|lra]]).
    assert (bpow radix2(-399)<=bpow radix2(-370)*(/2)*(1/62)/2) by (bpow_num;lra).
    lra. }
  pose proof (Rabs_le_inv _ _ T7) as T7'.
  assert (Blow : bpow radix2(-400)<=B(fmul h t)).
  { assert (bpow radix2(-48)*T<=T) by (bpow_num_all;nra). bpow_num_all. nra. }
  assert (Bup : B(fmul h t)<=bpow radix2(-45)).
  { assert (bpow radix2(-48)*T<=bpow radix2(-48)*bpow radix2(-46)) by (apply Rmult_le_compat_l;[apply bpow_ge_0|exact Tup]).
    bpow_num_all. lra. }
  split;[exact Fl|]. split;[split;assumption|]. split;[exact Tup|]. split;[exact Tlo|exact T7].
Qed.

(** {1 The outer region and the entry} *)

Lemma cdf_far_complement_ok lower T : finite lower -> bpow radix2(-400)<=B lower<=bpow radix2(-45) ->
  T<=bpow radix2(-46) -> Rabs(B lower-T)<=bpow radix2(-48)*T ->
  finite (fsub (erfcx_pow2 0) lower) /\ /2<=B(fsub (erfcx_pow2 0) lower)<=1 /\
  Rabs(B(fsub (erfcx_pow2 0) lower)-(1-T))<=bpow radix2(-49).
Proof.
  intros Fl L Tu Error.
  destruct (erfcx_pow2_ok 0 ltac:(lia)) as [Fone One]. change (bpow radix2 0) with 1 in One.
  assert (Sm : bpow radix2(-45)<=1/1000) by (bpow_num;lra).
  assert (Bound : bnd 1 0 (B (erfcx_pow2 0)-B lower)).
  { rewrite One. unfold bnd. rewrite Rmult_1_l. change (bpow radix2 0) with 1.
    rewrite Rabs_pos_eq by lra. pose proof (bpow_gt_0 radix2 (-400)). lra. }
  destruct (fsub_bnd 1 0 (erfcx_pow2 0) lower Fone Fl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bound)
    as [Fo [Out _]]. rewrite One in Out.
  assert (Round : Rabs(B(fsub (erfcx_pow2 0) lower)-(1-B lower))<=bpow radix2(-54)).
  { rewrite Out. apply (rnd_err_below _ 0);[lia|]. rewrite Rabs_pos_eq by lra.
    change (bpow radix2 0) with 1. pose proof (bpow_gt_0 radix2 (-400)). lra. }
  split;[exact Fo|]. split.
  - rewrite Out. split.
    + change (/2) with (bpow radix2 (-1)). apply round_ge_generic;[exact _|exact _| |bpow_num_all;lra].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    + change 1 with (bpow radix2 0). apply round_le_generic;[exact _|exact _| |pose proof (bpow_gt_0 radix2 (-400));lra].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
  - replace (B(fsub (erfcx_pow2 0) lower)-(1-T)) with
      ((B(fsub (erfcx_pow2 0) lower)-(1-B lower))-(B lower-T)) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
    assert (bpow radix2(-48)*T<=bpow radix2(-48)*bpow radix2(-46)) by (apply Rmult_le_compat_l;[apply bpow_ge_0|exact Tu]).
    bpow_num_all. lra.
Qed.

Theorem fast_cdf_far_outer_ok x : finite x -> 8<Rabs(B x)<=45/2 ->
  finite(fast_cdf_far_outer64 x) /\ bpow radix2(-400)<=B(fast_cdf_far_outer64 x)<=1 /\
  Rabs(B(fast_cdf_far_outer64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf_far_outer64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X.
  assert (Fa : finite(b64_abs x)) by (unfold b64_abs;destruct x;exact Fx).
  destruct (fast_cdf_far_lower_ok (b64_abs x) Fa ltac:(rewrite B_abs;exact X)) as [Fl [L [Tu [_ Error]]]].
  rewrite B_abs in Tu,Error.
  assert (Fzero : finite normal_zero) by reflexivity.
  assert (Zero : B normal_zero=0) by reflexivity.
  assert (Tp : 0<normal_tail (Rabs (B x))).
  { destruct (normal_tail_range (Rabs (B x))) as [P _];[lra|exact P]. }
  unfold fast_cdf_far_outer64. cbv zeta. destruct (normal_lt x normal_zero) eqn:Sign.
  - apply normal_lt_true in Sign;try assumption. rewrite Zero in Sign.
    assert (Target : normal_cdf(B x)=normal_tail (Rabs (B x))).
    { rewrite Rabs_left by lra. rewrite normal_tail_negative_cdf,Ropp_involutive. reflexivity. }
    rewrite Target. split;[exact Fl|]. split;[split;[exact (proj1 L)|]|].
    + eapply Rle_trans;[exact (proj2 L)|]. bpow_num_all. lra.
    + split;[|intros;exact Error].
      eapply Rle_trans;[exact Error|]. assert (bpow radix2(-48)*normal_tail (Rabs (B x))<=bpow radix2(-48)*bpow radix2(-46))
        by (apply Rmult_le_compat_l;[apply bpow_ge_0|exact Tu]). bpow_num_all. lra.
  - apply normal_lt_false in Sign;try assumption. rewrite Zero in Sign.
    assert (Target : normal_cdf(B x)=1-normal_tail (Rabs (B x))).
    { rewrite Rabs_pos_eq by lra. rewrite normal_tail_complement. unfold normal_cdf. field. }
    rewrite Target.
    destruct (cdf_far_complement_ok _ _ Fl L Tu Error) as [Fo [Range E]].
    split;[exact Fo|]. split;[split;[|exact (proj2 Range)]|].
    + eapply Rle_trans;[|exact (proj1 Range)]. bpow_num_all. lra.
    + split;[exact E|lra].
Qed.

Theorem fast_cdf_far_ok x : finite x -> bpow radix2(-33)<=Rabs(B x)<=45/2 ->
  finite(fast_cdf_far64 x) /\ bpow radix2(-400)<=B(fast_cdf_far64 x)<=1 /\
  Rabs(B(fast_cdf_far64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf_far64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X. unfold fast_cdf_far64.
  assert (Fa : finite(b64_abs x)) by (unfold b64_abs;destruct x;exact Fx).
  destruct (erfcx_pow2_ok 3 ltac:(lia)) as [F8 V8]. change (bpow radix2 3) with 8 in V8.
  destruct (normal_lt (erfcx_pow2 3) (b64_abs x)) eqn:Far.
  - apply (normal_lt_true _ _ F8 Fa) in Far. rewrite V8,B_abs in Far.
    apply fast_cdf_far_outer_ok;[exact Fx|lra].
  - apply (normal_lt_false _ _ F8 Fa) in Far. rewrite V8,B_abs in Far.
    destruct (fast_cdf_ok x Fx ltac:(lra)) as [Fv [Range [E1 E2]]].
    split;[exact Fv|]. split;[split;[|exact (proj2 Range)]|];[eapply Rle_trans;[|exact (proj1 Range)];bpow_num_all;lra|].
    split;assumption.
Qed.

Theorem fast_cdf_far_screen_finite x : finite x ->
  (fast_cdf_far_screen64 x=true <-> cdf_far_domain(B x)).
Proof.
  intros Fx;assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fmin Min].
  destruct(erfcx_pow2_ok 3 ltac:(lia))as[F8 V8]. change (bpow radix2 3) with 8 in V8.
  destruct cdf_far_limit_ok as[Fmax Max].
  assert(Z : B normal_zero=0)by reflexivity.
  assert(Fz : finite normal_zero)by reflexivity.
  unfold fast_cdf_far_screen64,cdf_far_domain;rewrite andb_true_iff,orb_true_iff,andb_true_iff,
    (normal_le_true _ _ Fmin Fa),(normal_le_true _ _ Fa F8),(normal_le_true _ _ Fa Fmax),
    (normal_lt_true _ _ Fx Fz),Min,V8,Max,Z,B_abs.
  tauto.
Qed.

Theorem fast_cdf_far_entry_ok x : finite x -> cdf_far_domain(B x) ->
  finite(fast_cdf_far_entry64 x) /\ bpow radix2(-400)<=B(fast_cdf_far_entry64 x)<=1 /\
  Rabs(B(fast_cdf_far_entry64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf_far_entry64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X;unfold fast_cdf_far_entry64.
  rewrite(proj2(fast_cdf_far_screen_finite x Fx)X);apply fast_cdf_far_ok;[assumption|].
  destruct X as[X1[X2|[X3 X4]]];[split;[exact X1|lra]|split;[exact X1|exact X4]].
Qed.

Theorem fast_cdf_far_fallback x : fast_cdf_far_screen64 x=false ->
  fast_cdf_far_entry64 x=normal_entry64 NormalCdf x.
Proof. intros Screen;unfold fast_cdf_far_entry64;rewrite Screen;reflexivity. Qed.

Theorem fast_cdf_far_fallback_contract x : fast_cdf_far_screen64 x=false ->
  normal_contract NormalCdf x (fast_cdf_far_entry64 x).
Proof. intros Screen;rewrite fast_cdf_far_fallback by exact Screen;apply normal_public_contract. Qed.

Theorem fast_cdf_far_nonfinite x : is_finite 53 1024 x=false ->
  fast_cdf_far_entry64 x=normal_entry64 NormalCdf x.
Proof.
  intros Nonfinite;destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;reflexivity.
  - reflexivity.
Qed.

Theorem fast_cdf_far_zeros :
  fast_cdf_far_entry64(B754_zero 53 1024 false)=erfcx_pow2(-1) /\
  fast_cdf_far_entry64(B754_zero 53 1024 true)=erfcx_pow2(-1).
Proof. split;reflexivity. Qed.

(** The source keeps the old near-domain entry in its common frame.  The
    negative far-tail screen is evaluated only when that screen rejects.
    This is a dispatch refactoring, not a change to the numerical entry. *)
Definition fast_cdf_far_only_screen64 x :=
  normal_le (fneg cdf_far_limit) x && normal_lt x (fneg (erfcx_pow2 3)).
Definition fast_cdf_far_split64 x :=
  if fast_cdf_screen64 x then fast_cdf64 x
  else if fast_cdf_far_only_screen64 x then fast_cdf_far_lower64 (b64_abs x)
  else normal_entry64 NormalCdf x.

Lemma fast_cdf_far_split_finite x : finite x ->
  fast_cdf_far_split64 x = fast_cdf_far_entry64 x.
Proof.
  intros Fx.
  assert (Fa : finite (b64_abs x)) by (unfold b64_abs; destruct x; exact Fx).
  destruct (erfcx_pow2_ok 3 ltac:(lia)) as [F8 V8].
  change (bpow radix2 3) with 8 in V8.
  destruct cdf_far_limit_ok as [Fmax Vmax].
  assert (Nf : forall w, finite w -> finite (fneg w)) by
    (intros w Fw; unfold fneg,b64_opp; rewrite is_finite_Bopp; exact Fw).
  assert (Nb : forall w, B (fneg w) = - B w) by (intros; apply B2R_Bopp).
  assert (Far : fast_cdf_far_only_screen64 x = true <-> -(45/2) <= B x < -8).
  { unfold fast_cdf_far_only_screen64. rewrite andb_true_iff,
      (normal_le_true _ _ (Nf _ Fmax) Fx), (normal_lt_true _ _ Fx (Nf _ F8)),
      !Nb, Vmax, V8. reflexivity. }
  assert (Min8 : bpow radix2 (-33) <= 8) by (bpow_num; lra).
  unfold fast_cdf_far_split64, fast_cdf_far_entry64.
  destruct (fast_cdf_screen64 x) eqn:Near.
  - pose proof (proj1 (fast_cdf_screen_finite x Fx) Near) as X.
    assert (Screen : fast_cdf_far_screen64 x = true).
    { apply (proj2 (fast_cdf_far_screen_finite x Fx)).
      unfold cdf_far_domain. split; [lra|left; lra]. }
    rewrite Screen. unfold fast_cdf_far64.
    assert (Tail : normal_lt (erfcx_pow2 3) (b64_abs x) = false).
    { apply (proj2 (normal_lt_false _ _ F8 Fa)). rewrite V8, B_abs. lra. }
    now rewrite Tail.
  - assert (NotNear : ~ bpow radix2 (-33) <= Rabs (B x) <= 8).
    { intros X. apply (proj2 (fast_cdf_screen_finite x Fx)) in X.
      rewrite Near in X; discriminate. }
    destruct (fast_cdf_far_only_screen64 x) eqn:Only.
    + pose proof (proj1 Far eq_refl) as X.
      assert (Abs : Rabs (B x) = - B x) by (apply Rabs_left1; lra).
      assert (Screen : fast_cdf_far_screen64 x = true).
      { apply (proj2 (fast_cdf_far_screen_finite x Fx)).
        unfold cdf_far_domain. rewrite Abs. split; [lra|right; split; lra]. }
      rewrite Screen. unfold fast_cdf_far64, fast_cdf_far_outer64.
      assert (Tail : normal_lt (erfcx_pow2 3) (b64_abs x) = true).
      { apply (proj2 (normal_lt_true _ _ F8 Fa)). rewrite V8, B_abs, Abs. lra. }
      assert (Neg : normal_lt x normal_zero = true).
      { apply (proj2 (normal_lt_true x normal_zero Fx ltac:(reflexivity))).
        change (B normal_zero) with 0. lra. }
      now rewrite Tail, Neg.
    + destruct (fast_cdf_far_screen64 x) eqn:Screen; [|reflexivity].
      exfalso. pose proof (proj1 (fast_cdf_far_screen_finite x Fx) Screen) as X.
      unfold cdf_far_domain in X. destruct X as [Min [Small|[Neg Max]]].
      * apply NotNear; split; assumption.
      * assert (Abs : Rabs (B x) = - B x) by (apply Rabs_left1; lra).
        assert (Large : 8 < Rabs (B x)) by (apply Rnot_le_lt; intros H; apply NotNear; split; assumption).
        assert (Yes : false = true).
        { apply (proj2 Far). rewrite Abs in Max, Large. split; lra. }
        discriminate.
Qed.

Theorem fast_cdf_far_split_eq x : fast_cdf_far_split64 x = fast_cdf_far_entry64 x.
Proof.
  destruct (is_finite 53 1024 x) eqn:Fx.
  - apply fast_cdf_far_split_finite; exact Fx.
  - destruct x as [s|s|s p Hp|s m e Hm]; try discriminate.
    + destruct s; reflexivity.
    + reflexivity.
Qed.

(** Exact endpoint completion shares the strong owner's generated threshold.
    The scalar split and SIMD masks retain the existing result bits. *)
Definition fast_cdf_saturated_split64 x :=
  if fast_cdf_screen64 x then fast_cdf64 x
  else if normal_lt x (fneg (erfcx_pow2 3)) then
    if normal_le (fneg cdf_far_limit) x then fast_cdf_far_lower64 (b64_abs x)
    else normal_entry64 NormalCdf x
  else if normal_le normal_cdf_one x then erfcx_pow2 0
  else normal_entry64 NormalCdf x.

Lemma cdf_saturation_owner_finite x : finite x ->
  normal_le normal_cdf_one x = true ->
  normal_entry64 NormalCdf x = erfcx_pow2 0.
Proof.
  intros Fx High.
  destruct normal_cdf_one_ok as [Fc Vc].
  pose proof (proj1 (normal_le_true _ _ Fc Fx) High) as X.
  assert (Nan : is_nan 53 1024 x = false) by
    (destruct x; try discriminate; reflexivity).
  assert (Zero : normal_eq x normal_zero = false).
  { destruct (normal_eq x normal_zero) eqn:E; [|reflexivity].
    apply (proj1 (normal_eq_true x normal_zero Fx ltac:(reflexivity))) in E.
    change (B normal_zero) with 0 in E. rewrite Vc in X. exfalso; lra. }
  unfold normal_entry64, normal_special64.
  rewrite Nan, Zero, High. reflexivity.
Qed.

Theorem fast_cdf_saturated_split_eq x :
  fast_cdf_saturated_split64 x = fast_cdf_far_split64 x.
Proof.
  destruct (is_finite 53 1024 x) eqn:Fx.
  - unfold fast_cdf_saturated_split64, fast_cdf_far_split64.
    destruct (fast_cdf_screen64 x); [reflexivity|].
    unfold fast_cdf_far_only_screen64.
    destruct (normal_lt x (fneg (erfcx_pow2 3))).
    + rewrite andb_true_r. destruct (normal_le (fneg cdf_far_limit) x); reflexivity.
    + rewrite andb_false_r.
      destruct (normal_le normal_cdf_one x) eqn:High; [|reflexivity].
      symmetry. apply cdf_saturation_owner_finite; assumption.
  - destruct x as [s|s|s p Hp|s m e Hm]; try discriminate.
    + destruct s; reflexivity.
    + reflexivity.
Qed.
