(** The bounded log-CDF's lower tail [Phi(-a) = exp(-a^2/2) erfcx(a/sqrt 2)/2]
    through the erfcx table: the actual binary64 sequence, its range and
    absolute error. The bounded CDF itself is [FastCdf]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxGaussianTarget NormalConstants
  NormalComparisons NormalFastDispatch NormalErfcxSensitivity
  NormalTailAnalytic NormalPublicEntry NormalPublicModel
  NormalAccurateCentralCdf FastExp FastErfcx FastNormalArgument FastNormalAnalytic.
Open Scope R_scope.

(** CI diagnostics for the previously silent FastNormal compile.
    Named checkpoints locate a stalled stage; tactic budgets fail closed and
    retain every proof obligation. *)

Definition fast_normal_lower64 a :=
  let t:=fast_normal_exponent64 a in
  let e:=fast_exp_entry64 t in
  let z:=fast_normal_argument64 a in
  let f:=fast_erfcx_table64 z in
  fmul(fmul(erfcx_pow2(-1))e)f.

(** Keep real algebra abstract: ring/field must never normalize a local
    alias for a computed binary64 Gaussian value. *)
Lemma fast_normal_half_product x y : (/2*x)*y=x*y/2.
Proof. timeout 30 (unfold Rdiv;ring). Time Qed.

Lemma fast_normal_three_errors w p q r :
  Rabs(w-r)<=Rabs(w-p)+Rabs(p-q)+Rabs(q-r).
Proof.
  replace(w-r)with((w-p)+(p-q)+(q-r))by timeout 30 ring.
  eapply Rle_trans;[apply Rabs_triang|].
  apply Rplus_le_compat_r;apply Rabs_triang.
Time Qed.

Lemma fast_normal_half_complement x : /2+x=1-(/2-x).
Proof. timeout 30 field. Time Qed.

Lemma fast_normal_three_quarters_format : fmtF(3/4).
Proof.
  replace(3/4)with(IZR 3*bpow radix2(-2))by(timeout 30 (bpow_num;simpl;field)).
  apply bnd_fmt;lia.
Time Qed.

Lemma fast_normal_product_error e f eh fh : 0<e -> 0<f -> e*f/2<=51/100 ->
  Rabs(eh-e)<=bpow radix2(-51)*e ->
  Rabs(fh-f)<=bpow radix2(-51)*f ->
  Rabs(eh*fh/2-e*f/2)<=5*bpow radix2(-53).
Proof.
  idtac "FastNormal.product_error.begin".
  intros E F P Ee Fe.
  set(de:=(eh-e)/e);set(df:=(fh-f)/f).
  assert(Eid : eh=e*(1+de))by(unfold de;field;timeout 30 lra).
  assert(Fid : fh=f*(1+df))by(unfold df;field;timeout 30 lra).
  assert(De : Rabs de<=bpow radix2(-51)).
  { unfold de,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq e)by timeout 30 lra.
    apply(Rmult_le_reg_r e);[timeout 30 lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by timeout 30 lra;exact Ee. }
  assert(Df : Rabs df<=bpow radix2(-51)).
  { unfold df,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f)by timeout 30 lra.
    apply(Rmult_le_reg_r f);[timeout 30 lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by timeout 30 lra;exact Fe. }
  assert(Factor : Rabs((1+de)*(1+df)-1)<=9*bpow radix2(-53)).
  { apply Rabs_le_inv in De,Df;apply Rabs_le;bpow_num_all;split;interval with(i_prec 160). }
  rewrite Eid,Fid.
  replace(e*(1+de)*(f*(1+df))/2-e*f/2)with((e*f/2)*((1+de)*(1+df)-1))by (unfold Rdiv;ring).
  rewrite Rabs_mult,(Rabs_pos_eq(e*f/2))by timeout 30 nra.
  assert(Scaled : (e*f/2)*Rabs((1+de)*(1+df)-1)<=(e*f/2)*(9*bpow radix2(-53))).
  { apply Rmult_le_compat_l;[timeout 30 nra|exact Factor]. }
  bpow_num_all;timeout 30 nra.
Time Qed.

Theorem fast_normal_lower_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_normal_lower64 a) /\
  bpow radix2(-58)<=B(fast_normal_lower64 a)<=3/4 /\
  Rabs(B(fast_normal_lower64 a)-normal_tail(B a))<=9*bpow radix2(-53).
Proof.
  idtac "FastNormal.lower.begin".
  intros Fa A.
  destruct(fast_normal_exponent_ok a Fa A)as[Ft [T [Tvalue Terror]]].
  destruct(fast_normal_argument_ok a Fa A)as[Fz [Z Zerror]].
  set(t:=fast_normal_exponent64 a)in *;set(z:=fast_normal_argument64 a)in *.
  assert(Zpos : 0<B z)by(pose proof(bpow_gt_0 radix2(-34));timeout 30 lra).
  assert(Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));timeout 30 lra).
  destruct(fast_exp_entry_ok t Ft ltac:(apply Rabs_lt;timeout 30 lra))as[Fe Eerror].
  pose proof(fast_exp_nonpositive_range t Ft T)as E.
  destruct(fast_erfcx_table_ok z Fz ltac:(split;timeout 30 lra))as[Ff [F Ferror]].
  set(e:=fast_exp_entry64 t)in *;set(f:=fast_erfcx_table64 z)in *.
  pose proof(fast_normal_perturbed_range (B a)(B z)(B t)ltac:(split;timeout 30 lra)Zpos Terror)as P.
  pose proof(fast_normal_product_error (exp(B t))(gaussian_erfcx(B z))(B e)(B f)
    (exp_pos _)(normal_erfcx_positive _ Zpos)(proj2 P)Eerror Ferror)as ProductError.
  idtac "FastNormal.lower.product_range".
  assert(ProductRange : bpow radix2(-57)<=B e*B f/2<=3/4).
  { pose proof(Rabs_le_inv _ _ ProductError)as Close.
    assert(LowerProduct : bpow radix2(-47)*bpow radix2(-9)<=B e*B f).
    { apply Rmult_le_compat;try apply bpow_ge_0;timeout 30 tauto. }
    assert(Lower : bpow radix2(-57)<=B e*B f/2)by(bpow_num_all;timeout 30 nra).
    split;[exact Lower|bpow_num_all;timeout 30 lra]. }
  idtac "FastNormal.lower.half_exact".
  destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fhalf Half].
  assert(Mag : (-46<=mag radix2(B e))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-47)<=Rabs(B e));rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-47));timeout 30 lra);exact(proj1 E). }
  assert(Format : fmtF(B(erfcx_pow2(-1))*B e)).
  { rewrite Half,Rmult_comm;apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct(fmul_exact(erfcx_pow2(-1))e Fhalf Fe Format)as[Fhe He].
  - rewrite Half,Rabs_mult,(Rabs_pos_eq(B e))by(pose proof(bpow_gt_0 radix2(-47));timeout 30 lra).
    rewrite Rabs_pos_eq by apply bpow_ge_0.
    eapply Rle_lt_trans with 1;[bpow_num_all;timeout 30 nra|change 1 with(bpow radix2 0);apply bpow_lt;lia].
  - rewrite Half in He;change(bpow radix2(-1))with(/2)in He.
    idtac "FastNormal.lower.multiply_bound".
    assert(Mbound : bnd 1 0 (B(fmul(erfcx_pow2(-1))e)*B f)).
    { rewrite He;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1.
      rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-57));timeout 30 nra);timeout 30 nra. }
    idtac "FastNormal.lower.multiply_ieee".
    destruct(fmul_bnd 1 0 (fmul(erfcx_pow2(-1))e)f Fhe Ff
      ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Mbound)as[Fl [L _]].
    (* Construct the value equality directly, avoiding the measured stall
       in the previous inverse-entry rewrite / real-product replacement block. *)
    idtac "FastNormal.lower.product_equality".
    assert(ProductValue : B(fmul(erfcx_pow2(-1))e)*B f=B e*B f/2).
    { transitivity ((/2*B e)*B f).
      - exact(f_equal(fun h:R=>h*B f)He).
      - exact(fast_normal_half_product(B e)(B f)). }
    idtac "FastNormal.lower.value_equality".
    assert(LowerValue : B(fast_normal_lower64 a)=rndF(B e*B f/2)).
    { exact(eq_trans L (f_equal rndF ProductValue)). }
    clear L;rename LowerValue into L.
    idtac "FastNormal.lower.output_range".
    assert(Range : bpow radix2(-58)<=B(fast_normal_lower64 a)<=3/4).
    { rewrite L;split.
      - apply round_ge_generic;[exact _|exact _| |bpow_num_all;timeout 30 lra].
        apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
      - apply round_le_generic;[exact _|exact _| |exact(proj2 ProductRange)].
        exact fast_normal_three_quarters_format. }
    idtac "FastNormal.lower.rounding".
    assert(Round : Rabs(B(fast_normal_lower64 a)-B e*B f/2)<=bpow radix2(-54)).
    { rewrite L;apply(rnd_err_below _ 0);[lia|].
      rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-57));timeout 30 lra).
      change(bpow radix2 0)with 1;timeout 30 lra. }
    idtac "FastNormal.lower.analytic_composition".
    pose proof(fast_normal_perturbation (B a)(B z)(B t)ltac:(split;timeout 30 lra)Zpos Zerror Terror)as Perturbation.
    idtac "FastNormal.lower.error_sum".
    assert(Error : Rabs(B(fast_normal_lower64 a)-normal_tail(B a))<=9*bpow radix2(-53)).
    { eapply Rle_trans.
      - exact(fast_normal_three_errors (B(fast_normal_lower64 a))
          (B e*B f/2)(exp(B t)*gaussian_erfcx(B z)/2)(normal_tail(B a))).
      - bpow_num_all;timeout 30 lra. }
    idtac "FastNormal.lower.finish".
    split;[exact Fl|];split;[exact Range|exact Error].
Time Qed.
