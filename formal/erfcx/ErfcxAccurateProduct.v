(** Final accurate positive-tail product; CS is the generated Rust constant.
    Its mathematical error is independently checked by CoqInterval. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import QSpec Q256 Q256Real.
From Q Require Limbs.
Require Import StageGappa ErfcxConstants ErfcxScaledAnalytic ErfcxTailIntegral
  ErfcxAccurateInputs ErfcxAccurateSetup.
Import ListNotations.
Open Scope R_scope.

Definition q_cs := new false [4152697298031616177%Z;1443862089616487703%Z;8202333101225853764%Z;10407460856758233229%Z] (-256).
Definition cs_significand : Z := 65328690604926057193764014675007098287082143062425007121036959538132401135793.

Lemma q_cs_ok : valid q_cs /\
  qval q_cs=IZR cs_significand*bpow radix2 (-256).
Proof.
  assert (O : ok4 [4152697298031616177%Z;1443862089616487703%Z;8202333101225853764%Z;10407460856758233229%Z]).
  { split; [repeat constructor; unfold Limbs.B; lia | reflexivity]. }
  split; [apply new_valid; exact O | ].
  unfold q_cs. rewrite new_val by exact O.
  unfold val,F2R. cbn [Fnum Fexp]. reflexivity.
Qed.

Lemma q_cs_error : exists e, Rabs e<=bpow radix2 (-255) /\
  qval q_cs=inv_sqrt_pi*(1+e).
Proof.
  destruct q_cs_ok as [Q Value].
  exists (qval q_cs/inv_sqrt_pi-1). split.
  - rewrite Value. unfold cs_significand,inv_sqrt_pi.
    bpow_num. apply Rabs_le; split; interval with (i_prec 400).
  - field. pose proof inv_sqrt_pi_positive; lra.
Qed.

Definition q_asym x := mul (mul (q_tail_series x) (q_recip (q_float x))) q_cs.

Lemma accurate_product_error s y c a b :
  Rabs s<=bpow radix2 (-225) -> Rabs y<=bpow radix2 (-252) ->
  Rabs c<=bpow radix2 (-255) -> Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs ((1+s)*(1+y)*(1+c)*(1+a)*(1+b)-1)<=bpow radix2 (-224).
Proof.
  intros S Y C A B. apply Rabs_le_inv in S,Y,C,A,B.
  replace ((1+s)*(1+y)*(1+c)*(1+a)*(1+b)-1) with
    (s+(1+s)*(y+(1+y)*(c+(1+c)*(a+(1+a)*b)))) by ring.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 400).
Qed.

Lemma accurate_series_relative sum j : /2<=j ->
  Rabs (sum-j)<=bpow radix2 (-226) ->
  exists e, Rabs e<=bpow radix2 (-225) /\ sum=j*(1+e).
Proof.
  intros J Error. exists ((sum-j)/j). split.
  - unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by lra. rewrite (Rabs_pos_eq j) by lra.
    apply (Rmult_le_reg_r j); [lra | ].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    eapply Rle_trans; [exact Error | ].
    replace (bpow radix2 (-226)) with (bpow radix2 (-225)*(/2)) by (bpow_num; field).
    apply Rmult_le_compat_l; [apply bpow_ge_0 | exact J].
  - field; lra.
Qed.

Theorem q_asym_error x : finite x -> 16<=B x ->
  valid (q_asym x) /\ exists e, Rabs e<=bpow radix2 (-224) /\
    qval (q_asym x)=positive_erfcx (B x)*(1+e).
Proof.
  intros F X. destruct (q_tail_series_integral x F X) as [S Serror].
  destruct (q_recip_float_error x F X) as [Y [ey [Ey Yvalue]]].
  destruct q_cs_ok as [C Cvalue]. destruct q_cs_error as [ec [Ec Cvalue']].
  assert (Reciprocal : 0</B x<=/16).
  { split; [apply Rinv_0_lt_compat | apply Rinv_le_contravar]; lra. }
  assert (T : 0<=(/B x)*(/B x)<=/2^8).
  { split; [nra | ]. eapply Rle_trans with ((/16)*(/16));
      [apply Rmult_le_compat; lra | right; field]. }
  pose proof (tail_integral_correction _ (proj1 T)) as Correction.
  assert (J : /2<=tail_integral ((/B x)*(/B x))) by (cbn [pow] in T; lra).
  destruct (accurate_series_relative _ _ J Serror) as [es [Es Svalue]].
  destruct (mul_relative _ _ S Y) as [P [a [A Pvalue]]].
  destruct (mul_relative _ _ P C) as [Result [b [Berr ResultValue]]].
  split; [exact Result | ].
  exists ((1+es)*(1+ey)*(1+ec)*(1+a)*(1+b)-1). split.
  - apply accurate_product_error; assumption.
  - unfold q_asym. rewrite ResultValue,Pvalue,Svalue,Yvalue,Cvalue'.
    unfold positive_erfcx,Rdiv. ring.
Qed.
