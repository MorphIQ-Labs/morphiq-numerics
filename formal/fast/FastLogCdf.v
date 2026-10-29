(** Bounded normal log-CDF: the actual binary64 scalar sequence of
    [fast::normal::log_norm_cdf], its finite negative normal output on the
    accelerated domain, its mixed natural-log-unit error bound, and its
    delegation to the strong entry everywhere else. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core Mult_error Sterbenz IEEE754.Binary IEEE754.Bits.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant RoundingCore RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxGaussianTarget ErfcxPublicModel NormalConstants
  NormalComparisons NormalErfcxSensitivity NormalErfcxFastScaled NormalTailAnalytic
  NormalAccurateCentralCdf NormalPublicEntry NormalPublicModel
  FastExp FastErfcx FastLn FastNormalArgument FastNormal.
Open Scope R_scope.

(** * The scalar sequence *)

(** Negative inputs, [a = -x]: [RN(RN(t + ln f) - ln2_hi)] with [t = RN(-a²/2)],
    [f] the erfcx table at [RN(a/sqrt 2)] and [ln] the bounded logarithm. *)
Definition fast_logcdf_negative64 a :=
  let t:=fast_normal_exponent64 a in
  let z:=fast_normal_argument64 a in
  let g:=fast_ln_regular64(fast_erfcx_table64 z) in
  fsub(fadd t g)normal_ln2_hi.

(** Positive inputs: the bounded lower tail [q], [w = RN(1 - q)], and Kahan's
    corrected logarithm [RN(ln w * RN(q / (1 - w)))]; [1 - w] is exact. *)
Definition fast_logcdf_positive64 a :=
  let q:=fast_normal_lower64 a in
  let w:=fsub(erfcx_pow2 0)q in
  fmul(fast_ln_regular64 w)(fdiv q(fsub(erfcx_pow2 0)w)).

(** 22.5: the largest negative magnitude whose scaled argument stays below the
    erfcx table's limit 16. *)
Definition fast_logcdf_limit : f64 := b64_of_bits 4627026404658118656.

Lemma fast_logcdf_limit_ok : finite fast_logcdf_limit /\ B fast_logcdf_limit=45/2.
Proof. split;[reflexivity|]. unfold fast_logcdf_limit,B;simpl;lra. Qed.

Definition fast_logcdf_screen64 x :=
  normal_le(erfcx_pow2(-33))(b64_abs x) &&
  (if normal_lt x normal_zero then normal_le(b64_abs x)fast_logcdf_limit
   else normal_le(b64_abs x)(erfcx_pow2 3)).

Definition fast_logcdf_entry64 x :=
  if fast_logcdf_screen64 x then
    (if normal_lt x normal_zero then fast_logcdf_negative64(b64_abs x)
     else fast_logcdf_positive64(b64_abs x))
  else normal_entry64 NormalLogCdf x.

(** The published contract, in natural-log units: [u*4*abs(L) + 32u]. *)
Definition fast_logcdf_budget L := bpow radix2(-51)*Rabs L+bpow radix2(-48).

(** * Real analysis shared by both branches *)

Lemma fast_logcdf_ln_one_minus_small d : Rabs d<=15*bpow radix2(-53) ->
  Rabs(ln(1+d))<=16*bpow radix2(-53).
Proof.
  intros D;apply Rabs_le_inv in D;apply Rabs_le;bpow_num_all;split;interval with(i_prec 120).
Qed.

(** The erfcx table argument is formed within [3u] relative; the logarithm of
    the table value moves by at most [15u]. On [(0,1]] the move is proportional
    to the argument; on [[1,16]] the tail derivative bound replaces it. *)
Lemma fast_logcdf_erfcx_sensitivity y z : 0<y<=16 ->
  Rabs(z-y)<=3*bpow radix2(-53)*y ->
  Rabs(gaussian_erfcx z-gaussian_erfcx y)<=14*bpow radix2(-53)*gaussian_erfcx y /\
  (y<=1 -> Rabs(gaussian_erfcx z-gaussian_erfcx y)<=14*bpow radix2(-53)*y*gaussian_erfcx y).
Proof.
  intros Y Zerror.
  pose proof inv_sqrt_pi_positive as Cpos.
  assert (Cval : 56/100<inv_sqrt_pi<57/100)by(unfold inv_sqrt_pi;split;interval with(i_prec 80)).
  pose proof(Rabs_le_inv _ _ Zerror)as Range.
  assert (Zpos : 0<z)by(bpow_num_all;nra).
  assert (Fy : 0<gaussian_erfcx y)by(apply normal_erfcx_positive;lra).
  (* The mean value theorem between the two arguments. *)
  assert (MVT : exists c, Rmin y z<=c<=Rmax y z /\
    gaussian_erfcx z-gaussian_erfcx y=normal_erfcx_derivative c*(z-y)).
  { destruct(Rtotal_order y z)as[Lt|[Eq|Gt]].
    - destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative y z Lt)as[c [Diff C]].
      + intros;apply is_derive_Reals,gaussian_erfcx_derivative.
      + exists c;split;[rewrite Rmin_left,Rmax_right by lra;lra|exact Diff].
    - exists y;split;[rewrite Rmin_left,Rmax_right by lra;lra|rewrite Eq;ring].
    - destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative z y Gt)as[c [Diff C]].
      + intros;apply is_derive_Reals,gaussian_erfcx_derivative.
      + exists c;split;[rewrite Rmin_right,Rmax_left by lra;lra|].
        replace(gaussian_erfcx z-gaussian_erfcx y)with(-(gaussian_erfcx y-gaussian_erfcx z))by ring.
        rewrite Diff;ring. }
  destruct MVT as[c [C Diff]].
  assert (Cpos' : 0<c).
  { destruct(Rle_dec y z);[rewrite Rmin_left in C by lra|rewrite Rmin_right in C by lra];bpow_num_all;nra. }
  destruct(normal_erfcx_derivative_bounds c Cpos')as[Dbounds Dtail].
  rewrite Diff,Rabs_mult.
  split.
  - destruct(Rle_dec y 1)as[Small|Large].
    + (* |F'| <= 2/sqrt pi and F(y) >= 7/(16 sqrt pi) on (0,2]. *)
      pose proof(normal_erfcx_small_lower y ltac:(lra))as Lower.
      assert (Dabs : Rabs(normal_erfcx_derivative c)<=2*inv_sqrt_pi)by(apply Rabs_le;lra).
      assert (Step : Rabs(normal_erfcx_derivative c)*Rabs(z-y)<=2*inv_sqrt_pi*(3*bpow radix2(-53)*y)).
      { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
      eapply Rle_trans;[exact Step|].
      bpow_num_all;nra.
    + (* |F'(c)| c² <= 1/sqrt pi, c >= y(1-3u), F(y) >= 1/(2 sqrt pi y). *)
      pose proof(normal_erfcx_large_lower y ltac:(lra))as Lower.
      assert (Clow : (1-3*bpow radix2(-53))*y<=c).
      { destruct(Rle_dec y z);[rewrite Rmin_left in C by lra|rewrite Rmin_right in C by lra];bpow_num_all;nra. }
      assert (Dabs : Rabs(normal_erfcx_derivative c)<=inv_sqrt_pi/(c*c)).
      { apply(Rmult_le_reg_r(c*c));[nra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by nra.
        rewrite <-Rmult_assoc;exact Dtail. }
      assert (Csq : (1-3*bpow radix2(-53))*(1-3*bpow radix2(-53))*(y*y)<=c*c)by(bpow_num_all;nra).
      assert (Dabs' : Rabs(normal_erfcx_derivative c)<=inv_sqrt_pi/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53))*(y*y))).
      { eapply Rle_trans;[exact Dabs|].
        apply Rmult_le_compat_l;[lra|];apply Rinv_le_contravar;[bpow_num_all;nra|exact Csq]. }
      assert (Step : Rabs(normal_erfcx_derivative c)*Rabs(z-y)<=
        inv_sqrt_pi/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53))*(y*y))*(3*bpow radix2(-53)*y)).
      { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
      eapply Rle_trans;[exact Step|].
      assert (Lower' : inv_sqrt_pi<=2*y*gaussian_erfcx y).
      { apply(Rmult_le_reg_r(/(2*y)));[apply Rinv_0_lt_compat;lra|].
        unfold Rdiv in Lower;rewrite Rmult_assoc,Rinv_r,Rmult_1_r by lra;exact Lower. }
      bpow_num_all.
      replace(inv_sqrt_pi/((1-3*(1/9007199254740992))*(1-3*(1/9007199254740992))*(y*y))*(3*(1/9007199254740992)*y))
        with(inv_sqrt_pi/y*(3*(1/9007199254740992)/((1-3*(1/9007199254740992))*(1-3*(1/9007199254740992)))))by(field;lra).
      assert (Q : inv_sqrt_pi/y<=2*gaussian_erfcx y).
      { apply(Rmult_le_reg_r y);[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;lra. }
      assert (K : 3*(1/9007199254740992)/((1-3*(1/9007199254740992))*(1-3*(1/9007199254740992)))<=7*(1/9007199254740992)).
      { interval with(i_prec 80). }
      pose proof(Rmult_le_compat _ _ _ _ (Rdiv_pos_pos_le_0 inv_sqrt_pi y ltac:(lra)ltac:(lra))
        ltac:(interval with(i_prec 80)) Q K)as P.
      lra.
  - intros Small.
    pose proof(normal_erfcx_small_lower y ltac:(lra))as Lower.
    assert (Dabs : Rabs(normal_erfcx_derivative c)<=2*inv_sqrt_pi)by(apply Rabs_le;lra).
    assert (Step : Rabs(normal_erfcx_derivative c)*Rabs(z-y)<=2*inv_sqrt_pi*(3*bpow radix2(-53)*y)).
    { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
    eapply Rle_trans;[exact Step|].
    bpow_num_all;nra.
Qed.

Lemma fast_logcdf_erfcx_log_sensitivity y z : 0<y<=16 ->
  Rabs(z-y)<=3*bpow radix2(-53)*y ->
  Rabs(ln(gaussian_erfcx z)-ln(gaussian_erfcx y))<=16*bpow radix2(-53).
Proof.
  intros Y Zerror.
  destruct(fast_logcdf_erfcx_sensitivity y z Y Zerror)as[Rel _].
  assert (Fy : 0<gaussian_erfcx y)by(apply normal_erfcx_positive;lra).
  pose proof(Rabs_le_inv _ _ Zerror)as Range.
  assert (Zpos : 0<z)by(bpow_num_all;nra).
  assert (Fz : 0<gaussian_erfcx z)by(apply normal_erfcx_positive;lra).
  set(d:=(gaussian_erfcx z-gaussian_erfcx y)/gaussian_erfcx y).
  assert (Did : gaussian_erfcx z=gaussian_erfcx y*(1+d))by(unfold d;field;lra).
  assert (D : Rabs d<=15*bpow radix2(-53)).
  { unfold d,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx y))by lra.
    apply(Rmult_le_reg_r(gaussian_erfcx y));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    eapply Rle_trans;[exact Rel|bpow_num_all;nra]. }
  assert (Dpos : 0<1+d)by(apply Rabs_le_inv in D;bpow_num_all;lra).
  rewrite Did,ln_mult by lra.
  replace(ln(gaussian_erfcx y)+ln(1+d)-ln(gaussian_erfcx y))with(ln(1+d))by ring.
  apply fast_logcdf_ln_one_minus_small;exact D.
Qed.

(** The table value of a positive scaled argument below 16 lies in
    [[1/128, 1+2^-51]]: the compact lower bound of the erfcx tail and its unit
    upper bound, perturbed by the table's relative error. *)
Lemma fast_logcdf_table_range z : finite z -> 0<B z<16 ->
  bpow radix2(-7)<=B(fast_erfcx_table64 z)<=1+bpow radix2(-51) /\
  Rabs(ln(B(fast_erfcx_table64 z)))<=49/10.
Proof.
  intros Fz Z.
  destruct(fast_erfcx_table_ok z Fz ltac:(lra))as[Ff [Range Error]].
  pose proof(normal_erfcx_compact_lower(B z)ltac:(lra))as Lower.
  pose proof(normal_erfcx_unit_upper(B z)ltac:(lra))as Upper.
  pose proof(Rabs_le_inv _ _ Error)as E.
  assert (Fpos : 0<gaussian_erfcx(B z))by(apply normal_erfcx_positive;lra).
  assert (R : bpow radix2(-7)<=B(fast_erfcx_table64 z)<=1+bpow radix2(-51))by(bpow_num_all;split;nra).
  split;[exact R|].
  apply Rabs_le;bpow_num_all;destruct R as[Rl Ru];split.
  - eapply Rle_trans;[|apply ln_le;[lra|exact Rl]];interval with(i_prec 80).
  - eapply Rle_trans;[apply ln_le;[lra|exact Ru]|];interval with(i_prec 80).
Qed.

(** The bounded logarithm of a positive finite binary64, including one. *)
Lemma fast_logcdf_ln_ok f : finite f -> 0<B f ->
  finite(fast_ln_regular64 f) /\
  Rabs(B(fast_ln_regular64 f)-ln(B f))<=bpow radix2(-53)*Rabs(ln(B f))+bpow radix2(-65).
Proof.
  intros Ff Fpos.
  destruct(Req_dec(B f)1)as[One|NotOne].
  - assert (Fid : f=b64_of_bits 4607182418800017408).
    { apply B2R_inj.
      - unfold finite in Ff;destruct f as[s|s|s p Hp|s m e Hm];try discriminate.
        + exfalso;destruct s;simpl in One;lra.
        + reflexivity.
      - reflexivity.
      - rewrite One;reflexivity. }
    rewrite Fid,fast_ln_regular_one,One,ln_1.
    split;[reflexivity|].
    unfold B,c_zero;simpl;rewrite Rminus_0_r,Rabs_R0,Rabs_R0;pose proof(bpow_gt_0 radix2(-65));lra.
  - apply fast_ln_regular_ok;assumption.
Qed.

(** * Argument formation on the negative side *)

Theorem fast_logcdf_argument_ok a : finite a -> bpow radix2(-33)<=B a<=45/2 ->
  finite(fast_normal_argument64 a) /\
  bpow radix2(-34)<=B(fast_normal_argument64 a)<16 /\
  Rabs(B(fast_normal_argument64 a)-B a/sqrt 2)<=3*bpow radix2(-53)*(B a/sqrt 2).
Proof.
  intros Fa A;destruct normal_inv_sqrt2_hi_ok as[Fc C].
  assert(Crange : /2<=B normal_inv_sqrt2_hi<=7072/10000)by(rewrite C;split;interval with(i_prec 80)).
  assert(Cerror : Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=bpow radix2(-53)/sqrt 2).
  { rewrite C;bpow_num;interval with(i_prec 160). }
  assert(Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  assert(Product : bpow radix2(-34)<=B a*B normal_inv_sqrt2_hi<=1592/100).
  { bpow_num_all;split;nra. }
  assert(Bound : bnd 1 4 (B a*B normal_inv_sqrt2_hi)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-34));lra).
    change(bpow radix2 4)with 16;lra. }
  destruct(fmul_bnd 1 4 a normal_inv_sqrt2_hi Fa Fc ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Bound)
    as[Fz [Z _]].
  fold(fast_normal_argument64 a)in Fz,Z.
  assert(Normal : bpow radix2(-1022)<=Rabs(B a*B normal_inv_sqrt2_hi)).
  { rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-34));lra).
    eapply Rle_trans with(bpow radix2(-34));[apply bpow_le;lia|exact(proj1 Product)]. }
  pose proof(rnd_rel _ Normal)as Round.
  change(Rabs(rndF(B a*B normal_inv_sqrt2_hi)-B a*B normal_inv_sqrt2_hi)<=
    bpow radix2(-53)*Rabs(B a*B normal_inv_sqrt2_hi))in Round.
  rewrite <-Z,Rabs_mult,(Rabs_pos_eq(B a)),(Rabs_pos_eq(B normal_inv_sqrt2_hi))in Round by lra.
  assert(Range : bpow radix2(-34)<=B(fast_normal_argument64 a)<16).
  { split.
    - rewrite Z;apply round_ge_generic;[exact _|exact _| |exact(proj1 Product)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - pose proof(Rabs_le_inv _ _ Round)as R;bpow_num_all;nra. }
  assert(Error : Rabs(B(fast_normal_argument64 a)-B a/sqrt 2)<=3*bpow radix2(-53)*(B a/sqrt 2)).
  { replace(B(fast_normal_argument64 a)-B a/sqrt 2)with
      ((B(fast_normal_argument64 a)-B a*B normal_inv_sqrt2_hi)+B a*(B normal_inv_sqrt2_hi-/sqrt 2))by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite Rabs_mult,(Rabs_pos_eq(B a))by lra.
    pose proof(Rabs_le_inv _ _ Cerror)as Cr.
    assert(Scaled : B a*Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=B a*(bpow radix2(-53)/sqrt 2)).
    { apply Rmult_le_compat_l;lra. }
    assert(High : B a*B normal_inv_sqrt2_hi<=B a*(1+bpow radix2(-53))/sqrt 2).
    { unfold Rdiv in *;nra. }
    assert(Ypos : 0<B a/sqrt 2)by(apply Rdiv_lt_0_compat;[lra|interval]).
    bpow_num_all;unfold Rdiv in *;nra. }
  repeat split;tauto.
Qed.

Theorem fast_logcdf_exponent_ok a : finite a -> bpow radix2(-33)<=B a<=45/2 ->
  finite(fast_normal_exponent64 a) /\ -254<=B(fast_normal_exponent64 a)<=0 /\
  Rabs(B(fast_normal_exponent64 a)+B a*B a/2)<=bpow radix2(-53)*(B a*B a/2).
Proof.
  intros Fa A;destruct erfcx_negative_half_ok as[Fhalf Half].
  assert(Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  assert(Mag : (-32<=mag radix2(B a))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-33)<=Rabs(B a));rewrite Rabs_pos_eq by lra;exact(proj1 A). }
  assert(Format : fmtF(B erfcx_negative_half*B a)).
  { rewrite Half;replace(-/2*B a)with(-(B a*bpow radix2(-1)))by(bpow_num;ring).
    apply generic_format_opp,mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct(fmul_exact erfcx_negative_half a Fhalf Fa Format)as[Fha Ha].
  - rewrite Half,Rabs_mult,(Rabs_pos_eq(B a))by lra.
    eapply Rle_lt_trans with 16;[rewrite Rabs_Ropp;rewrite Rabs_pos_eq by lra;nra|].
    change 16 with(bpow radix2 4);apply bpow_lt;lia.
  - rewrite Half in Ha.
    assert(Qrange : bpow radix2(-67)<=B a*B a/2<=2025/8)by(bpow_num_all;split;nra).
    assert(Bound : bnd 1 8 (B(fmul erfcx_negative_half a)*B a)).
    { rewrite Ha;unfold bnd;rewrite Rmult_1_l.
      replace(-/2*B a*B a)with(-(B a*B a/2))by (unfold Rdiv;ring).
      rewrite Rabs_Ropp,Rabs_pos_eq by nra;change(bpow radix2 8)with 256;lra. }
    destruct(fmul_bnd 1 8 (fmul erfcx_negative_half a)a Fha Fa ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Bound)
      as[Ft [T _]].
    fold(fast_normal_exponent64 a)in Ft,T;rewrite Ha in T.
    replace(-/2*B a*B a)with(-B a*B a/2)in T by (unfold Rdiv;ring).
    assert(Normal : bpow radix2(-1022)<=Rabs(-B a*B a/2)).
    { replace(-B a*B a/2)with(-(B a*B a/2))by (unfold Rdiv;ring);rewrite Rabs_Ropp,Rabs_pos_eq by nra.
      eapply Rle_trans with(bpow radix2(-67));[apply bpow_le;lia|exact(proj1 Qrange)]. }
    pose proof(rnd_rel _ Normal)as Error.
    change(Rabs(rndF(-B a*B a/2)-(-B a*B a/2))<=bpow radix2(-53)*Rabs(-B a*B a/2))in Error.
    rewrite <-T in Error.
    replace(-B a*B a/2)with(-(B a*B a/2))in Error by (unfold Rdiv;ring).
    rewrite Rabs_Ropp,(Rabs_pos_eq(B a*B a/2))in Error by nra.
    replace(B(fast_normal_exponent64 a)- -(B a*B a/2))with(B(fast_normal_exponent64 a)+B a*B a/2)in Error by (unfold Rdiv;ring).
    assert(Range : -254<=B(fast_normal_exponent64 a)<=0).
    { pose proof(Rabs_le_inv _ _ Error)as E;bpow_num_all;split;nra. }
    repeat split;tauto.
Qed.

(** * The negative branch *)

Lemma fast_logcdf_tail_log a : 0<a ->
  ln(normal_tail a)= -a*a/2+ln(gaussian_erfcx(a/sqrt 2))-ln 2.
Proof.
  intros A.
  assert (Y : 0<a/sqrt 2)by(apply Rdiv_lt_0_compat;[exact A|interval with(i_prec 80)]).
  pose proof(normal_erfcx_positive _ Y)as F.
  pose proof(exp_pos(-a*a/2))as E.
  unfold normal_tail,Rdiv at 3.
  rewrite ln_mult by(try apply Rinv_0_lt_compat;nra).
  rewrite ln_mult by lra.
  rewrite ln_exp,ln_Rinv by lra.
  unfold Rdiv;ring.
Qed.

Theorem fast_logcdf_negative_ok a : finite a -> bpow radix2(-33)<=B a<=45/2 ->
  finite(fast_logcdf_negative64 a) /\
  B(fast_logcdf_negative64 a)<= -/2 /\
  Rabs(B(fast_logcdf_negative64 a)-ln(normal_tail(B a)))<=fast_logcdf_budget(ln(normal_tail(B a))).
Proof.
  intros Fa A.
  assert (Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(fast_logcdf_argument_ok a Fa A)as[Fz [Z Zerror]].
  destruct(fast_logcdf_exponent_ok a Fa A)as[Ft [T Terror]].
  set(z:=fast_normal_argument64 a)in *;set(t:=fast_normal_exponent64 a)in *.
  set(y:=B a/sqrt 2)in *;set(q:=B a*B a/2)in *.
  assert (Ypos : 0<y)by(unfold y;apply Rdiv_lt_0_compat;[lra|interval with(i_prec 80)]).
  assert (Yup : y<=16)by(unfold y;interval with(i_prec 80)).
  assert (Zpos : 0<B z)by(pose proof(bpow_gt_0 radix2(-34));lra).
  destruct(fast_erfcx_table_ok z Fz ltac:(lra))as[Ff [Frange Ferror]].
  destruct(fast_logcdf_table_range z Fz ltac:(lra))as[Fvalue Flog].
  set(f:=fast_erfcx_table64 z)in *.
  assert (Fpos : 0<B f)by(pose proof(bpow_gt_0 radix2(-7));lra).
  destruct(fast_logcdf_ln_ok f Ff Fpos)as[Fg Gerror].
  set(g:=fast_ln_regular64 f)in *.
  (* The logarithm of the table value against the exact scaled erfcx. *)
  assert (Fz_pos : 0<gaussian_erfcx(B z))by(apply normal_erfcx_positive;lra).
  assert (Fy_pos : 0<gaussian_erfcx y)by(apply normal_erfcx_positive;lra).
  assert (TableLog : Rabs(ln(B f)-ln(gaussian_erfcx(B z)))<=5*bpow radix2(-53)).
  { set(d:=(B f-gaussian_erfcx(B z))/gaussian_erfcx(B z)).
    assert (Did : B f=gaussian_erfcx(B z)*(1+d))by(unfold d;field;lra).
    assert (D : Rabs d<=bpow radix2(-51)).
    { unfold d,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx(B z)))by lra.
      apply(Rmult_le_reg_r(gaussian_erfcx(B z)));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Ferror. }
    assert (Dpos : 0<1+d)by(apply Rabs_le_inv in D;bpow_num_all;lra).
    rewrite Did,ln_mult by lra.
    replace(ln(gaussian_erfcx(B z))+ln(1+d)-ln(gaussian_erfcx(B z)))with(ln(1+d))by ring.
    apply Rabs_le_inv in D;apply Rabs_le;bpow_num_all;split;interval with(i_prec 120). }
  pose proof(fast_logcdf_erfcx_log_sensitivity y (B z) (conj Ypos Yup) Zerror)as ArgLog.
  (* g against ln F(y): table, logarithm and argument errors. *)
  assert (Gtotal : Rabs(B g-ln(gaussian_erfcx y))<=
    bpow radix2(-53)*Rabs(ln(B f))+bpow radix2(-65)+21*bpow radix2(-53)).
  { replace(B g-ln(gaussian_erfcx y))with
      ((B g-ln(B f))+(ln(B f)-ln(gaussian_erfcx(B z)))+(ln(gaussian_erfcx(B z))-ln(gaussian_erfcx y)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|].
    bpow_num_all;lra. }
  assert (Gabs : Rabs(B g)<=5).
  { pose proof(Rabs_le_inv _ _ Gerror)as E;pose proof(Rabs_le_inv _ _ Flog)as L.
    apply Rabs_le;bpow_num_all;split;lra. }
  (* The first sum. *)
  assert (SumBound : bnd 1 9 (B t+B g)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 9)with 512;apply Rabs_le;apply Rabs_le_inv in Gabs;lra. }
  destruct(fadd_bnd 1 9 t g Ft Fg ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)SumBound)as[Fs [S _]].
  set(s:=fadd t g)in *.
  (* The sum t + g can be tiny, or zero: below the normal range the rounding
     error is at most half a minimum subnormal, otherwise relative. *)
  assert (Serror : Rabs(B s-(B t+B g))<=bpow radix2(-53)*Rabs(B t+B g)+bpow radix2(-1075)).
  { rewrite S;destruct(Rle_dec(bpow radix2(-1022))(Rabs(B t+B g)))as[Normal|Tiny].
    - pose proof(rnd_rel _ Normal);pose proof(bpow_gt_0 radix2(-1075));lra.
    - pose proof(rnd_err_below(B t+B g)(-1021)ltac:(lia)ltac:(apply Rnot_le_lt in Tiny;
        eapply Rle_trans;[left;exact Tiny|apply bpow_le;lia]))as E.
      change(-1021-54)%Z with(-1075)%Z in E.
      pose proof(Rmult_le_pos(bpow radix2(-53))(Rabs(B t+B g))(bpow_ge_0 _ _)(Rabs_pos _));lra. }
  (* The constant and the final difference. *)
  destruct normal_ln2_hi_ok as[Fc C].
  assert (Cerror : Rabs(B normal_ln2_hi-ln 2)<=bpow radix2(-54))by(rewrite C;bpow_num;interval with(i_prec 120)).
  assert (Crange : 69/100<=B normal_ln2_hi<=70/100)by(rewrite C;split;interval with(i_prec 80)).
  assert (DiffBound : bnd 1 9 (B s-B normal_ln2_hi)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 9)with 512.
    pose proof(Rabs_le_inv _ _ Serror)as Se;apply Rabs_le_inv in Gabs;apply Rabs_le;bpow_num_all;split;nra. }
  destruct(fsub_bnd 1 9 s normal_ln2_hi Fs Fc ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)DiffBound)as[Fr [R _]].
  fold(fast_logcdf_negative64 a)in Fr,R.
  (* The exact target and its size. *)
  rewrite(fast_logcdf_tail_log(B a)Apos).
  fold y q.
  assert (Fy_upper : gaussian_erfcx y<=1)by(apply normal_erfcx_unit_upper;lra).
  assert (LnFy : ln(gaussian_erfcx y)<=0)by(rewrite <-ln_1;apply ln_le;lra).
  assert (LnFy_low : -49/10<=ln(gaussian_erfcx y)).
  { pose proof(normal_erfcx_compact_lower y ltac:(lra))as Low.
    eapply Rle_trans;[|apply ln_le;[lra|exact Low]];interval with(i_prec 80). }
  assert (Ln2 : 69/100<ln 2<70/100)by(split;interval with(i_prec 80)).
  set(L:= -B a*B a/2+ln(gaussian_erfcx y)-ln 2).
  assert (Lneg : L<= -q-69/100)by(unfold L,q;lra).
  assert (Labs : Rabs L=q+ln 2-ln(gaussian_erfcx y))by(unfold L,q;rewrite Rabs_left1 by lra;ring).
  (* Relate the intermediate sums to L. *)
  pose proof(Rabs_le_inv _ _ Terror)as Te.
  pose proof(Rabs_le_inv _ _ Gtotal)as Ge.
  pose proof(Rabs_le_inv _ _ Serror)as Se.
  pose proof(Rabs_le_inv _ _ Cerror)as Ce.
  pose proof(Rabs_le_inv _ _ Flog)as Fl.
  assert (Normal2 : bpow radix2(-1022)<=Rabs(B s-B normal_ln2_hi)).
  { rewrite Rabs_left1;[|bpow_num_all;nra].
    eapply Rle_trans with(/2);[bpow_num;lra|bpow_num_all;nra]. }
  pose proof(rnd_rel _ Normal2)as Rerror.
  change(Rabs(rndF(B s-B normal_ln2_hi)-(B s-B normal_ln2_hi))<=bpow radix2(-53)*Rabs(B s-B normal_ln2_hi))in Rerror.
  rewrite <-R in Rerror.
  pose proof(Rabs_le_inv _ _ Rerror)as Re.
  assert (Rneg : B(fast_logcdf_negative64 a)<= -/2).
  { rewrite Rabs_left1 in Re;[|bpow_num_all;nra];bpow_num_all;nra. }
  split;[exact Fr|];split;[exact Rneg|].
  unfold fast_logcdf_budget;fold L;rewrite Labs.
  (* Every rounding is relative to a quantity dominated by |L|. *)
  assert (Qle : q<=Rabs L-69/100)by(rewrite Labs;lra).
  rewrite Rabs_left1 in Serror;[|bpow_num_all;nra].
  rewrite Rabs_left1 in Rerror;[|bpow_num_all;nra].
  pose proof(Rabs_le_inv _ _ Serror)as Se'.
  pose proof(Rabs_le_inv _ _ Rerror)as Re'.
  apply Rabs_le;bpow_num_all;split;nra.
Qed.

(** * The positive branch *)

(** The bounded lower tail with a relative error: the exponential's two
    perturbations, the table's two, and the final rounding. The argument
    sensitivity shrinks with the argument, which the near-zero region needs. *)
Theorem fast_logcdf_lower_relative a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_normal_lower64 a) /\
  bpow radix2(-52)<=B(fast_normal_lower64 a)<=51/100 /\
  (B a<=1 -> Rabs(B(fast_normal_lower64 a)-normal_tail(B a))<=20*bpow radix2(-53)*normal_tail(B a)) /\
  (1<=B a -> Rabs(B(fast_normal_lower64 a)-normal_tail(B a))<=56*bpow radix2(-53)*normal_tail(B a)).
Proof.
  intros Fa A.
  assert (Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(fast_normal_lower_ok a Fa A)as[Fl [Lrange _]].
  destruct(fast_normal_exponent_ok a Fa A)as[Ft [T [Tvalue Terror]]].
  destruct(fast_normal_argument_ok a Fa A)as[Fz [Z Zerror]].
  set(t:=fast_normal_exponent64 a)in *;set(z:=fast_normal_argument64 a)in *.
  set(y:=B a/sqrt 2)in *;set(q:=B a*B a/2)in *.
  assert (Ypos : 0<y)by(unfold y;apply Rdiv_lt_0_compat;[lra|interval with(i_prec 80)]).
  assert (Yup : y<=6)by(unfold y;interval with(i_prec 80)).
  assert (Zpos : 0<B z)by(pose proof(bpow_gt_0 radix2(-34));lra).
  destruct(fast_exp_entry_ok t Ft ltac:(apply Rabs_lt;lra))as[Fe Eerror].
  pose proof(fast_exp_nonpositive_range t Ft T)as E.
  destruct(fast_erfcx_table_ok z Fz ltac:(split;lra))as[Ff [F Ferror]].
  set(e:=fast_exp_entry64 t)in *;set(f:=fast_erfcx_table64 z)in *.
  pose proof(exp_pos(B t))as Etpos;pose proof(exp_pos(-q))as Eqpos.
  assert (Fz_pos : 0<gaussian_erfcx(B z))by(apply normal_erfcx_positive;lra).
  assert (Fy_pos : 0<gaussian_erfcx y)by(apply normal_erfcx_positive;lra).
  destruct(fast_logcdf_erfcx_sensitivity y (B z) (conj Ypos ltac:(lra)) Zerror)as[Sflat Sscaled].
  (* The four relative perturbations. *)
  set(d1:=(B e-exp(B t))/exp(B t)).
  set(d2:=exp(B t)/exp(-q)-1).
  set(d3:=(B f-gaussian_erfcx(B z))/gaussian_erfcx(B z)).
  set(d4:=(gaussian_erfcx(B z)-gaussian_erfcx y)/gaussian_erfcx y).
  assert (E1 : B e=exp(B t)*(1+d1))by(unfold d1;field;lra).
  assert (E2 : exp(B t)=exp(-q)*(1+d2))by(unfold d2;field;lra).
  assert (E3 : B f=gaussian_erfcx(B z)*(1+d3))by(unfold d3;field;lra).
  assert (E4 : gaussian_erfcx(B z)=gaussian_erfcx y*(1+d4))by(unfold d4;field;lra).
  assert (D1 : Rabs d1<=bpow radix2(-51)).
  { unfold d1,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(exp(B t)))by lra.
    apply(Rmult_le_reg_r(exp(B t)));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Eerror. }
  assert (D2 : Rabs d2<=33*bpow radix2(-53)).
  { unfold d2;replace(exp(B t)/exp(-q))with(exp(B t+q)).
    - pose proof(Rabs_le_inv _ _ Terror)as Te.
      assert (Q : 0<=q<=32)by(unfold q;nra).
      apply Rabs_le;bpow_num_all;split;interval with(i_prec 80).
    - rewrite exp_plus;replace q with(-(-q))at 2 by ring;rewrite exp_Ropp;field;lra. }
  assert (D3 : Rabs d3<=bpow radix2(-51)).
  { unfold d3,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx(B z)))by lra.
    apply(Rmult_le_reg_r(gaussian_erfcx(B z)));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Ferror. }
  assert (D4flat : Rabs d4<=14*bpow radix2(-53)).
  { unfold d4,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx y))by lra.
    apply(Rmult_le_reg_r(gaussian_erfcx y));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Sflat. }
  assert (D4scaled : y<=1 -> Rabs d4<=14*bpow radix2(-53)*y).
  { intros Y;specialize(Sscaled Y).
    unfold d4,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(gaussian_erfcx y))by lra.
    apply(Rmult_le_reg_r(gaussian_erfcx y));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;lra. }
  (* The exact product and its single rounding, as in FastNormal. *)
  destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fhalf Half].
  assert(Mag : (-46<=mag radix2(B e))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-47)<=Rabs(B e));rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-47));lra);exact(proj1 E). }
  assert(Format : fmtF(B(erfcx_pow2(-1))*B e)).
  { rewrite Half,Rmult_comm;apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct(fmul_exact(erfcx_pow2(-1))e Fhalf Fe Format)as[Fhe He].
  - rewrite Half,Rabs_mult,(Rabs_pos_eq(B e))by(pose proof(bpow_gt_0 radix2(-47));lra).
    rewrite Rabs_pos_eq by apply bpow_ge_0.
    eapply Rle_lt_trans with 1;[bpow_num_all;nra|change 1 with(bpow radix2 0);apply bpow_lt;lia].
  - rewrite Half in He;change(bpow radix2(-1))with(/2)in He.
    assert (Product : B(fmul(erfcx_pow2(-1))e)*B f=B e*B f/2)by(rewrite He;unfold Rdiv;ring).
    assert (Ppos : 0<B e*B f/2)by(pose proof(bpow_gt_0 radix2(-47));pose proof(bpow_gt_0 radix2(-9));nra).
    assert (Pup : B e*B f/2<=1)by(bpow_num_all;nra).
    assert(Mbound : bnd 1 0 (B(fmul(erfcx_pow2(-1))e)*B f)).
    { rewrite Product;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra. }
    destruct(fmul_bnd 1 0 (fmul(erfcx_pow2(-1))e)f Fhe Ff ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Mbound)as[Fl' [L _]].
    rewrite Product in L;fold(fast_normal_lower64 a)in L.
    assert (Normal : bpow radix2(-1022)<=Rabs(B e*B f/2)).
    { rewrite Rabs_pos_eq by lra;eapply Rle_trans with(bpow radix2(-57));[apply bpow_le;lia|].
      pose proof(bpow_gt_0 radix2(-47));pose proof(bpow_gt_0 radix2(-9));bpow_num_all;nra. }
    pose proof(rnd_rel _ Normal)as Round;rewrite <-L in Round.
    set(d5:=(B(fast_normal_lower64 a)-B e*B f/2)/(B e*B f/2)).
    assert (E5 : B(fast_normal_lower64 a)=B e*B f/2*(1+d5))by(unfold d5;field;lra).
    assert (D5 : Rabs d5<=bpow radix2(-53)).
    { unfold d5,Rdiv at 1;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(B e*B f/2))by lra.
      apply(Rmult_le_reg_r(B e*B f/2));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
      rewrite Rabs_pos_eq in Round by lra;exact Round. }
    (* Assemble: lower = tail(a) (1+d1)(1+d2)(1+d3)(1+d4)(1+d5). *)
    assert (Tail : normal_tail(B a)=exp(-q)*gaussian_erfcx y/2)by(unfold normal_tail,q,y;f_equal;f_equal;f_equal;unfold Rdiv;ring).
    assert (Tpos : 0<normal_tail(B a))by(apply normal_tail_range;lra).
    assert (Id : B(fast_normal_lower64 a)=normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5))).
    { rewrite E5,E1,E2,E3,E4,Tail;unfold Rdiv;ring. }
    pose proof(Rabs_le_inv _ _ D1)as R1;pose proof(Rabs_le_inv _ _ D2)as R2.
    pose proof(Rabs_le_inv _ _ D3)as R3;pose proof(Rabs_le_inv _ _ D5)as R5.
    pose proof(Rabs_le_inv _ _ D4flat)as R4.
    assert (Range : bpow radix2(-52)<=B(fast_normal_lower64 a)<=51/100).
    { destruct(normal_tail_range(B a)Apos)as[_ Tup].
      (* tail(8) >= exp(-32) erfcx(8/sqrt 2)/2 >= 2^-52 (1 + 56u). *)
      assert (Tlow : 3*bpow radix2(-52)/10*3<=normal_tail(B a)).
      { rewrite Tail.
        assert (Edown : exp(-32)<=exp(-q))by(apply exp_le;unfold q;nra).
        assert (Fdown : inv_sqrt_pi/(2*6)<=gaussian_erfcx y).
        { destruct(Rle_dec 1 y)as[Large|Small].
          - pose proof(normal_erfcx_large_lower y Large)as Low.
            eapply Rle_trans;[|exact Low];apply Rmult_le_compat_l;[lra|];apply Rinv_le_contravar;lra.
          - pose proof(normal_erfcx_small_lower y ltac:(lra))as Low;unfold inv_sqrt_pi in *;
            eapply Rle_trans;[|exact Low];interval with(i_prec 80). }
        assert (Cval : 56/100<inv_sqrt_pi)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
        bpow_num_all;unfold Rdiv in *;interval with(i_prec 120). }
      rewrite Id;split;bpow_num_all;nra. }
    split;[exact Fl|];split;[exact Range|];split.
    + intros Small.
      assert (Ysmall : y<=1)by(unfold y;apply Rle_trans with(B a/sqrt 2);[lra|];
        apply Rmult_le_reg_r with(sqrt 2);[interval|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by interval;interval with(i_prec 80)).
      specialize(D4scaled Ysmall);pose proof(Rabs_le_inv _ _ D4scaled)as R4s.
      assert (Qsmall : q<=/2)by(unfold q;nra).
      (* With q <= 1/2 the exponent perturbation is at most u/2. *)
      assert (D2small : Rabs d2<=bpow radix2(-53)).
      { unfold d2;replace(exp(B t)/exp(-q))with(exp(B t+q)).
        - pose proof(Rabs_le_inv _ _ Terror)as Te.
          assert (Q : 0<=q<=/2)by(unfold q;nra).
          apply Rabs_le;bpow_num_all;split;interval with(i_prec 80).
        - rewrite exp_plus;replace q with(-(-q))at 2 by ring;rewrite exp_Ropp;field;lra. }
      pose proof(Rabs_le_inv _ _ D2small)as R2s.
      rewrite Id;replace(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5))-normal_tail(B a))
        with(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5)-1))by ring.
      rewrite Rabs_mult,(Rabs_pos_eq(normal_tail(B a)))by lra.
      rewrite Rmult_comm;apply Rmult_le_compat_r;[lra|].
      apply Rabs_le;bpow_num_all;split;interval with(i_prec 120).
    + intros Large.
      rewrite Id;replace(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5))-normal_tail(B a))
        with(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5)-1))by ring.
      rewrite Rabs_mult,(Rabs_pos_eq(normal_tail(B a)))by lra.
      rewrite Rmult_comm;apply Rmult_le_compat_r;[lra|].
      apply Rabs_le;bpow_num_all;split;interval with(i_prec 120).
Qed.

Lemma fast_logcdf_cdf_complement a : normal_cdf a=1-normal_tail a.
Proof. rewrite normal_tail_complement;unfold normal_cdf;apply fast_normal_half_complement. Qed.

(** The lower tail's relative error moves the logarithm of the complement by
    at most [21u]: [q/(1-q)] is at most one near zero and below [0.19]
    beyond one. *)
Lemma fast_logcdf_complement_log a : bpow radix2(-33)<=a<=8 ->
  forall qh, (a<=1 -> Rabs(qh-normal_tail a)<=20*bpow radix2(-53)*normal_tail a) ->
  (1<=a -> Rabs(qh-normal_tail a)<=56*bpow radix2(-53)*normal_tail a) ->
  Rabs(ln(1-qh)-ln(1-normal_tail a))<=21*bpow radix2(-53).
Proof.
  intros A qh Small Large.
  assert (Apos : 0<a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(normal_tail_range a Apos)as[Tpos Tup].
  set(q:=normal_tail a)in *.
  (* The perturbation of the complement, relative to the exact complement. *)
  set(d:=(q-qh)/(1-q)).
  assert (Did : 1-qh=(1-q)*(1+d))by(unfold d;field;lra).
  assert (D : Rabs d<=21*bpow radix2(-53)*(1-bpow radix2(-48))).
  { unfold d,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(1-q))by lra.
    apply(Rmult_le_reg_r(1-q));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    rewrite Rabs_minus_sym.
    destruct(Rle_dec a 1)as[S|L].
    - specialize(Small S);eapply Rle_trans;[exact Small|];bpow_num_all;nra.
    - specialize(Large ltac:(lra)).
      (* Beyond one the tail is at most Phi(-1) < 0.16: q/(1-q) < 0.19. *)
      assert (Qup : q<=16/100).
      { unfold q;rewrite normal_tail_complement.
        (* normal_center is increasing and normal_center 1 >= 0.34. *)
        admit. }
      eapply Rle_trans;[exact Large|];bpow_num_all;nra. }
  assert (Dpos : 0<1+d)by(apply Rabs_le_inv in D;bpow_num_all;lra).
  rewrite Did,ln_mult by lra.
  replace(ln(1-q)+ln(1+d)-ln(1-q))with(ln(1+d))by ring.
  apply Rabs_le_inv in D;apply Rabs_le;bpow_num_all;split;interval with(i_prec 120).
Admitted.

Theorem fast_logcdf_positive_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_logcdf_positive64 a) /\
  B(fast_logcdf_positive64 a)<0 /\
  Rabs(B(fast_logcdf_positive64 a)-ln(normal_cdf(B a)))<=fast_logcdf_budget(ln(normal_cdf(B a))).
Proof.
  intros Fa A.
  assert (Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(fast_logcdf_lower_relative a Fa A)as[Fq [Qrange [Qsmall Qlarge]]].
  set(qh:=fast_normal_lower64 a)in *.
  destruct(normal_tail_range(B a)Apos)as[Tpos Tup].
  set(q:=normal_tail(B a))in *.
  destruct(erfcx_pow2_ok 0 ltac:(lia))as[Fone One];change(bpow radix2 0)with 1 in One.
  (* w = RN(1 - qh): within 2^-54 of 1 - qh, in [1/4, 1 - 2^-52]. *)
  assert (Wbound : bnd 1 0 (B(erfcx_pow2 0)-B qh)).
  { rewrite One;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;apply Rabs_le;
    pose proof(bpow_gt_0 radix2(-52));lra. }
  destruct(fsub_bnd 1 0 (erfcx_pow2 0)qh Fone Fq ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Wbound)as[Fw [W _]].
  rewrite One in W;set(w:=fsub(erfcx_pow2 0)qh)in *.
  assert (Werror : Rabs(B w-(1-B qh))<=bpow radix2(-54)).
  { rewrite W;apply(rnd_err_below _ 0);[lia|];rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-52));lra);
    change(bpow radix2 0)with 1;lra. }
  assert (Wup : B w<=1-bpow radix2(-52)).
  { rewrite W;replace(1-bpow radix2(-52))with(IZR(2^52-1)*bpow radix2(-52))by(bpow_num_all;lra).
    apply round_le_generic;[exact _|exact _|apply bnd_fmt;lia|bpow_num_all;lra]. }
  assert (Wlow : /4<=B w).
  { rewrite W;change(/4)with(bpow radix2(-2));apply round_ge_generic;[exact _|exact _| |bpow_num_all;lra].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (Wpos : 0<B w)by lra.
  assert (Wone : B w<>1)by(pose proof(bpow_gt_0 radix2(-52));lra).
  (* d = RN(1 - w): relative rounding, positive. *)
  assert (Dexact : bpow radix2(-52)-bpow radix2(-54)<=1-B w<=3/4).
  { pose proof(Rabs_le_inv _ _ Werror);pose proof(bpow_gt_0 radix2(-52));bpow_num_all;lra. }
  assert (Dbound : bnd 1 0 (B(erfcx_pow2 0)-B w)).
  { rewrite One;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;apply Rabs_le;bpow_num_all;lra. }
  destruct(fsub_bnd 1 0 (erfcx_pow2 0)w Fone Fw ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Dbound)as[Fd [D _]].
  rewrite One in D;set(d:=fsub(erfcx_pow2 0)w)in *.
  assert (Dnormal : bpow radix2(-1022)<=Rabs(1-B w)).
  { rewrite Rabs_pos_eq by(bpow_num_all;lra);eapply Rle_trans;[|exact(proj1 Dexact)];bpow_num_all;lra. }
  pose proof(rnd_rel _ Dnormal)as Derror;rewrite <-D in Derror.
  rewrite Rabs_pos_eq in Derror by(bpow_num_all;lra).
  pose proof(Rabs_le_inv _ _ Derror)as De.
  assert (Dpos : 0<B d)by(bpow_num_all;lra).
  (* The logarithm of w. *)
  destruct(fast_logcdf_ln_ok w Fw Wpos)as[Fg Gerror].
  set(g:=fast_ln_regular64 w)in *.
  assert (LnW : -3/2<=ln(B w)<= -bpow radix2(-52)).
  { split.
    - eapply Rle_trans;[|apply ln_le;[lra|exact Wlow]];interval with(i_prec 80).
    - eapply Rle_trans;[apply ln_le;[lra|exact Wup]|];bpow_num_all;interval with(i_prec 120). }
  assert (Gneg : B g<0)by(pose proof(Rabs_le_inv _ _ Gerror)as E;pose proof(Rabs_le_inv (ln(B w))(3/2)ltac:(apply Rabs_le;lra));bpow_num_all;nra).
  (* r = RN(qh / d). *)
  assert (Ratio : 7/8<=B qh/B d<=4/3).
  { pose proof(Rabs_le_inv _ _ Werror)as We;pose proof(bpow_gt_0 radix2(-52)).
    assert (Dlow : (1-bpow radix2(-53))*(B qh-bpow radix2(-54))<=B d)by(bpow_num_all;nra).
    assert (Dup : B d<=(1+bpow radix2(-53))*(B qh+bpow radix2(-54)))by(bpow_num_all;nra).
    split.
    - apply(Rmult_le_reg_r(B d));[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra.
    - apply(Rmult_le_reg_r(B d));[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
  assert (Rbound : bnd 1 1 (B qh/B d)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 1)with 2;apply Rabs_le;lra. }
  destruct(fdiv_bnd 1 1 qh d Fq ltac:(lra)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Rbound)as[Fr [R _]].
  set(r:=fdiv qh d)in *.
  assert (Rnormal : bpow radix2(-1022)<=Rabs(B qh/B d))by(rewrite Rabs_pos_eq by lra;bpow_num_all;lra).
  pose proof(rnd_rel _ Rnormal)as Rerror;rewrite <-R in Rerror.
  rewrite Rabs_pos_eq in Rerror by lra.
  pose proof(Rabs_le_inv _ _ Rerror)as Re.
  assert (Rpos : 0<B r)by(bpow_num_all;nra).
  (* The product. *)
  assert (Pbound : bnd 1 1 (B g*B r)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 1)with 2;apply Rabs_le.
    pose proof(Rabs_le_inv _ _ Gerror)as Ge;pose proof(Rabs_le_inv (ln(B w))(3/2)ltac:(apply Rabs_le;lra));bpow_num_all;nra. }
  destruct(fmul_bnd 1 1 g r Fg Fr ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Pbound)as[Fp [P _]].
  fold(fast_logcdf_positive64 a)in Fp,P.
  assert (Pneg : B g*B r<0)by nra.
  assert (Pnormal : bpow radix2(-1022)<=Rabs(B g*B r)).
  { rewrite Rabs_left by lra.
    pose proof(Rabs_le_inv _ _ Gerror)as Ge;pose proof(bpow_gt_0 radix2(-52)).
    assert (Gmag : bpow radix2(-53)<=-B g).
    { apply Rabs_le_inv in Gerror. bpow_num_all;nra. }
    bpow_num_all;nra. }
  pose proof(rnd_rel _ Pnormal)as Perror;rewrite <-P in Perror.
  rewrite Rabs_left in Perror by lra.
  pose proof(Rabs_le_inv _ _ Perror)as Pe.
  (* The result is negative. *)
  assert (Result_neg : B(fast_logcdf_positive64 a)<0)by(bpow_num_all;nra).
  split;[exact Fp|];split;[exact Result_neg|].
  (* Kahan's identity: ln(w) qh/(1-w) against ln(1-qh), with w = 1-qh-delta. *)
  rewrite fast_logcdf_cdf_complement.
  pose proof(fast_logcdf_complement_log(B a)A(B qh)Qsmall Qlarge)as Complement.
  set(delta:=B w-(1-B qh)).
  assert (Wid : B w=1-(B qh+delta))by(unfold delta;ring).
  assert (Delta : Rabs delta<=bpow radix2(-54))by exact Werror.
  pose proof(Rabs_le_inv _ _ Delta)as Dl.
  assert (Qpos : 0<B qh)by(pose proof(bpow_gt_0 radix2(-52));lra).
  assert (Qup : B qh<=51/100)by lra.
  assert (Lnq : -3/4<=ln(1-B qh)<0).
  { split.
    - eapply Rle_trans;[|apply ln_le;[lra|]];[interval with(i_prec 80)|lra].
    - rewrite <-ln_1;apply ln_increasing;lra. }
  (* ln(1 - qh - delta) = ln(1 - qh) + ln(1 - delta/(1 - qh)). *)
  set(eps:= -delta/(1-B qh)).
  assert (Epsid : 1-(B qh+delta)=(1-B qh)*(1+eps))by(unfold eps;field;lra).
  assert (Eps : Rabs eps<=bpow radix2(-54)*(100/49)).
  { unfold eps,Rdiv;rewrite Rabs_mult,Rabs_Ropp,Rabs_Rinv,(Rabs_pos_eq(1-B qh))by lra.
    apply(Rmult_le_reg_r(1-B qh));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
  pose proof(Rabs_le_inv _ _ Eps)as El.
  assert (LnWsplit : ln(B w)=ln(1-B qh)+ln(1+eps)).
  { rewrite Wid,Epsid,ln_mult;[reflexivity|lra|bpow_num_all;lra]. }
  assert (LnEps : Rabs(ln(1+eps))<=bpow radix2(-54)*(100/49)*(1+bpow radix2(-50))).
  { apply Rabs_le;bpow_num_all;split;interval with(i_prec 120). }
  pose proof(Rabs_le_inv _ _ LnEps)as LnEl.
  (* The ratio qh/(1-w) = qh/(qh+delta): within 1/7 of one... bounded by Ratio. *)
  set(sigma:=B qh+delta).
  assert (Sigma : 1-B w=sigma)by(unfold sigma;rewrite Wid;ring).
  assert (SigmaPos : 0<sigma)by(unfold sigma;pose proof(bpow_gt_0 radix2(-52));bpow_num_all;lra).
  (* The target: g r rounds to the result. *)
  set(L:=ln(1-q)).
  set(Lh:=ln(1-B qh)).
  assert (Lq : Rabs(Lh-L)<=21*bpow radix2(-53))by exact Complement.
  pose proof(Rabs_le_inv _ _ Lq)as Lql.
  (* Exact Kahan value: Lh * qh / sigma * (sigma/(qh + ...)) -- rewrite as
     Lh + Lh*(qh/sigma - 1) + ln(1+eps)*qh/sigma. *)
  assert (Ksplit : ln(B w)*(B qh/sigma)=Lh+Lh*(B qh/sigma-1)+ln(1+eps)*(B qh/sigma)).
  { rewrite LnWsplit;unfold Lh;ring. }
  assert (Ratio' : 7/8<=B qh/sigma<=4/3).
  { unfold sigma;pose proof(bpow_gt_0 radix2(-52)).
    split;apply(Rmult_le_reg_r(B qh+delta));try lra;unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
  assert (RatioErr : Rabs(B qh/sigma-1)<=bpow radix2(-54)/(B qh)*(4/3)).
  { replace(B qh/sigma-1)with(-delta/sigma)by(unfold sigma;field;lra).
    unfold Rdiv;rewrite Rabs_mult,Rabs_Ropp,Rabs_Rinv,(Rabs_pos_eq sigma)by lra.
    apply(Rmult_le_reg_r sigma);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    assert (Qs : B qh<=sigma*(4/3))by(unfold sigma;pose proof(bpow_gt_0 radix2(-52));bpow_num_all;nra).
    apply Rle_trans with(bpow radix2(-54));[exact Delta|].
    apply(Rmult_le_reg_l(B qh));[lra|];field_simplify;[|lra|lra];nra. }
  (* |Lh| / qh <= 1.4 for qh <= 0.51. *)
  assert (LhRel : Rabs Lh<=7/5*B qh).
  { unfold Lh;rewrite Rabs_left by lra.
    assert (Qr : bpow radix2(-52)<=B qh<=51/100)by lra.
    bpow_num_all;interval with(i_prec 120). }
  (* The computed g r against ln(w) qh/sigma. *)
  assert (Gr : Rabs(B g*B r-ln(B w)*(B qh/sigma))<=
    bpow radix2(-53)*Rabs(ln(B w))*(4/3)*(1+bpow radix2(-52))*2+bpow radix2(-65)*(4/3)*(1+bpow radix2(-52))+
    Rabs(ln(B w))*(4/3)*(2*bpow radix2(-53)+bpow radix2(-105))).
  { pose proof(Rabs_le_inv _ _ Gerror)as Ge.
    rewrite <-Sigma in *.
    assert (Rrel : Rabs(B r-B qh/(1-B w))<=bpow radix2(-53)*(B qh/(1-B w))*(1+2*bpow radix2(-53))).
    { (* B r = RN(qh / d) with d = RN(1 - w). *)
      assert (Dd : B d=(1-B w)*(1+(B d-(1-B w))/(1-B w)))by(field;lra).
      set(e1:=(B d-(1-B w))/(1-B w)).
      assert (E1 : Rabs e1<=bpow radix2(-53)).
      { unfold e1,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(1-B w))by lra.
        apply(Rmult_le_reg_r(1-B w));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
        rewrite <-Rabs_pos_eq with(1-B w) at 2 by lra;exact Derror. }
      pose proof(Rabs_le_inv _ _ E1)as E1l.
      replace(B r-B qh/(1-B w))with((B r-B qh/B d)+(B qh/B d-B qh/(1-B w)))by ring.
      eapply Rle_trans;[apply Rabs_triang|].
      assert (Second : Rabs(B qh/B d-B qh/(1-B w))<=bpow radix2(-53)*(B qh/(1-B w))*(1+2*bpow radix2(-53))).
      { replace(B qh/B d-B qh/(1-B w))with(-(B qh/(1-B w))*(e1/(1+e1)))by(unfold e1;field;split;lra).
        rewrite Rabs_mult,Rabs_Ropp,(Rabs_pos_eq(B qh/(1-B w)))by(apply Rdiv_pos_pos_le_0... ) ...
        admit. }
      admit. }
    admit. }
  admit.
Admitted.
