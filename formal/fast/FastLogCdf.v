(** Bounded normal log-CDF: the actual binary64 scalar sequence of
    [fast::normal::log_norm_cdf], its finite negative normal output on the
    accelerated domain, its mixed natural-log-unit error bound, and its
    delegation to the strong entry everywhere else. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core Mult_error Sterbenz IEEE754.Binary IEEE754.Bits.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant RoundingCore RoundingTest Encodings.
Require Import ExpFast StageGappa ErfcxConstants ErfcxDecision ErfcxGaussianTarget ErfcxPublicModel NormalConstants
  NormalComparisons NormalErfcxSensitivity NormalErfcxFastScaled NormalTailAnalytic
  NormalTailRange NormalFastDispatch NormalAccurateCentralCdf NormalPublicEntry NormalPublicModel
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
Proof.
  split.
  - exact(bits_finite 4627026404658118656 false 6333186975989760 (-48) eq_refl).
  - unfold fast_logcdf_limit;rewrite(bits_val 4627026404658118656 false 6333186975989760 48 eq_refl).
    assert (P : 2^48=281474976710656)by(simpl;ring).
    rewrite P;simpl;lra.
Qed.

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
      (* inv_sqrt_pi / y <= 2 F(y), and 3u/(1-3u)² <= 7u/2. *)
      assert (Q : inv_sqrt_pi/y<=2*gaussian_erfcx y).
      { replace(inv_sqrt_pi/y)with(2*(inv_sqrt_pi/(2*y)))by(field;lra);lra. }
      assert (Qpos : 0<=inv_sqrt_pi/y)by(apply Rmult_le_pos;[lra|left;apply Rinv_0_lt_compat;lra]).
      assert (Rewrite : inv_sqrt_pi/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53))*(y*y))*(3*bpow radix2(-53)*y)=
        inv_sqrt_pi/y*(3*bpow radix2(-53)/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53))))).
      { field;bpow_num_all;repeat split;try lra;nra. }
      rewrite Rewrite.
      assert (K : 3*bpow radix2(-53)/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53)))<=7/2*bpow radix2(-53)).
      { bpow_num_all;interval with(i_prec 80). }
      assert (Kpos : 0<=3*bpow radix2(-53)/((1-3*bpow radix2(-53))*(1-3*bpow radix2(-53)))).
      { apply Rmult_le_pos;[bpow_num_all;lra|left;apply Rinv_0_lt_compat;bpow_num_all;nra]. }
      pose proof(Rmult_le_compat _ _ _ _ Qpos Kpos Q K)as P.
      bpow_num_all;nra.
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
  bpow radix2(-9)<=B(fast_erfcx_table64 z)<=1+bpow radix2(-51) /\
  Rabs(ln(B(fast_erfcx_table64 z)))<=56/10.
Proof.
  intros Fz Z.
  destruct(fast_erfcx_table_ok z Fz ltac:(lra))as[Ff [Range Error]].
  pose proof(normal_erfcx_compact_lower(B z)ltac:(lra))as Lower.
  pose proof(normal_erfcx_unit_upper(B z)ltac:(lra))as Upper.
  pose proof(Rabs_le_inv _ _ Error)as E.
  assert (Fpos : 0<gaussian_erfcx(B z))by(apply normal_erfcx_positive;lra).
  assert (Ru : B(fast_erfcx_table64 z)<=1+bpow radix2(-51))by(bpow_num_all;nra).
  assert (Rl : (1-bpow radix2(-51))/256<=B(fast_erfcx_table64 z))by(bpow_num_all;nra).
  assert (Rpos : 0<B(fast_erfcx_table64 z))by(bpow_num_all;lra).
  split;[split;[exact(proj1 Range)|exact Ru]|].
  apply Rabs_le;split.
  - apply Rle_trans with(ln((1-bpow radix2(-51))/256));[bpow_num_all;interval with(i_prec 80)|].
    apply ln_le;[bpow_num_all;lra|exact Rl].
  - apply Rle_trans with(ln(1+bpow radix2(-51)));[apply ln_le;[lra|exact Ru]|].
    bpow_num_all;interval with(i_prec 80).
Qed.

(** The bounded logarithm of a positive finite binary64, including one. *)
Lemma fast_logcdf_ln_ok f : finite f -> 0<B f ->
  finite(fast_ln_regular64 f) /\
  Rabs(B(fast_ln_regular64 f)-ln(B f))<=bpow radix2(-53)*Rabs(ln(B f))+bpow radix2(-65).
Proof.
  intros Ff Fpos.
  destruct(Req_dec(B f)1)as[One|NotOne].
  - destruct(erfcx_pow2_ok 0 ltac:(lia))as[Fone Vone];change(bpow radix2 0)with 1 in Vone.
    assert (Fid : f=erfcx_pow2 0).
    { apply B2R_inj.
      - destruct f as[s|s|s p Hp|s m e Hm];try reflexivity;exfalso;simpl in One;lra.
      - vm_compute;reflexivity.
      - exact(eq_trans One(eq_sym Vone)). }
    assert (Zero : fast_ln_regular64 f=c_zero)by(rewrite Fid;exact fast_ln_regular_one).
    rewrite Zero,One,ln_1.
    split;[exact c_zero_finite|].
    rewrite c_zero_val,Rminus_0_r,!Rabs_R0;pose proof(bpow_gt_0 radix2(-65));lra.
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
  unfold normal_tail.
  replace(exp(-a*a/2)*gaussian_erfcx(a/sqrt 2)/2)with(exp(-a*a/2)*gaussian_erfcx(a/sqrt 2)*/2)by(unfold Rdiv;ring).
  rewrite ln_mult;[|nra|apply Rinv_0_lt_compat;lra].
  rewrite ln_mult by lra.
  rewrite ln_exp,ln_Rinv by lra.
  ring.
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
  assert (Fpos : 0<B f)by(pose proof(bpow_gt_0 radix2(-9));lra).
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
  assert (Gabs : Rabs(B g)<=6).
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
    - pose proof(rnd_rel _ Normal)as R0.
      change(Rabs(rndF(B t+B g)-(B t+B g))<=bpow radix2(-53)*Rabs(B t+B g))in R0.
      pose proof(bpow_gt_0 radix2(-1075));lra.
    - pose proof(rnd_err_below(B t+B g)(-1021)ltac:(lia)ltac:(apply Rnot_le_lt in Tiny;
        eapply Rle_trans;[left;exact Tiny|apply bpow_le;lia]))as E.
      change(-1021-54)%Z with(-1075)%Z in E.
      pose proof(Rmult_le_pos(bpow radix2(-53))(Rabs(B t+B g))(bpow_ge_0 _ _)(Rabs_pos _));lra. }
  (* The constant and the final difference. *)
  destruct normal_ln2_hi_ok as[Fc C].
  assert (Cerror : Rabs(B normal_ln2_hi-ln 2)<=bpow radix2(-54))by(rewrite C;bpow_num;interval with(i_prec 120)).
  assert (Crange : 69/100<=B normal_ln2_hi<=70/100)by(rewrite C;split;interval with(i_prec 80)).
  assert (SumAbs : Rabs(B t+B g)<=260)by(apply Rabs_le;apply Rabs_le_inv in Gabs;lra).
  pose proof(Rabs_pos(B t+B g))as SumPos.
  assert (DiffBound : bnd 1 9 (B s-B normal_ln2_hi)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 9)with 512.
    pose proof(Rabs_le_inv _ _ Serror)as Se;apply Rabs_le_inv in Gabs;apply Rabs_le;bpow_num_all;split;lra. }
  destruct(fsub_bnd 1 9 s normal_ln2_hi Fs Fc ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)DiffBound)as[Fr [R _]].
  unfold fast_logcdf_negative64;fold z;fold f;fold g;fold t;fold s.
  (* The exact target and its size. *)
  assert (Target : ln(normal_tail(B a))= -q+ln(gaussian_erfcx y)-ln 2).
  { rewrite(fast_logcdf_tail_log(B a)Apos);unfold q,y;first[ring|field|nra|lra]. }
  rewrite Target.
  assert (Fy_upper : gaussian_erfcx y<=1)by(apply normal_erfcx_unit_upper;lra).
  assert (LnFy : ln(gaussian_erfcx y)<=0)by(rewrite <-ln_1;apply ln_le;lra).
  assert (LnFy_low : -56/10<=ln(gaussian_erfcx y)).
  { pose proof(normal_erfcx_compact_lower y ltac:(lra))as Low.
    apply Rle_trans with(ln(/256));[interval with(i_prec 80)|apply ln_le;[lra|exact Low]]. }
  assert (Ln2 : 69/100<ln 2<70/100)by(split;interval with(i_prec 80)).
  set(L:= -q+ln(gaussian_erfcx y)-ln 2).
  assert (Qnonneg : 0<=q)by(unfold q;nra).
  assert (Lneg : L<= -q-69/100)by(unfold L;lra).
  assert (Labs : Rabs L=q+ln 2-ln(gaussian_erfcx y))by(unfold L;rewrite Rabs_left1 by lra;ring).
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
  (* Explicit linear bounds for the sums; every product below is a constant
     times one quantity. *)
  assert (Tq : -q*(1+bpow radix2(-53))<=B t<=0)by(bpow_num_all;nra).
  assert (Gsmall : B g<=1/100)by(bpow_num_all;lra).
  (* |g| follows ln F(y), so the sums are dominated by |L|. *)
  assert (Gabs2 : Rabs(B g)<= -ln(gaussian_erfcx y)+27*bpow radix2(-53))by(apply Rabs_le;bpow_num_all;lra).
  pose proof(Rabs_le_inv _ _ Gabs2)as Gl.
  assert (SumAbs2 : Rabs(B t+B g)<=q*(1+bpow radix2(-53))-ln(gaussian_erfcx y)+27*bpow radix2(-53))by(apply Rabs_le;bpow_num_all;lra).
  assert (Sup : B s<=2/100)by(bpow_num_all;lra).
  assert (Sdown : -300<=B s)by(bpow_num_all;lra).
  assert (Diff : B s-B normal_ln2_hi<= -6/10)by lra.
  assert (DiffAbs : Rabs(B s-B normal_ln2_hi)=-(B s-B normal_ln2_hi))by(apply Rabs_left1;lra).
  rewrite DiffAbs in Re.
  assert (Rneg : B(fsub s normal_ln2_hi)<= -/2)by(bpow_num_all;lra).
  split;[exact Fr|];split;[exact Rneg|].
  unfold fast_logcdf_budget;fold L;rewrite Labs.
  (* Every rounding is relative to a quantity dominated by |L|. *)
  assert (Slow : -(B s-B normal_ln2_hi)<=q*(1+bpow radix2(-53))-ln(gaussian_erfcx y)+28*bpow radix2(-53)+7/10)by(bpow_num_all;lra).
  pose proof(Rabs_pos(B t+B g))as SumPos'.
  apply Rabs_le;unfold L;bpow_num_all;split;lra.
Qed.

(** * The positive branch *)

(** The bounded lower tail with a relative error: the exponential's two
    perturbations, the table's two, and the final rounding. The argument
    sensitivity shrinks with the argument, which the near-zero region needs. *)
(** The relative allowance by region: the exponent perturbation grows with
    [a²/2] and the argument sensitivity with [a/sqrt 2] up to one. *)
(** A small exponent perturbation moves the exponential by at most [v + v²]. *)
Lemma fast_logcdf_exp_small v : -/2<=v<=/2 -> v<=exp v-1<=v+2*v*v.
Proof.
  intros V.
  pose proof(exp_ineq1_le v)as Lower.
  pose proof(exp_ineq1_le(-v))as Upper;rewrite exp_Ropp in Upper.
  pose proof(exp_pos v)as E.
  assert (U : (1-v)*exp v<=1).
  { apply Rmult_le_reg_r with(/exp v);[apply Rinv_0_lt_compat;exact E|].
    rewrite Rmult_assoc,Rinv_r,Rmult_1_r,Rmult_1_l by lra;exact Upper. }
  split;[lra|nra].
Qed.

(** Relative-perturbation identities, proved once in an empty context: the
    field tactic is slow in a large one. *)
Lemma fast_logcdf_split_rel x y : y<>0 -> x=y*(1+(x-y)/y).
Proof. intros Y;field;exact Y. Qed.
Lemma fast_logcdf_split_ratio x y : y<>0 -> x=y*(1+(x/y-1)).
Proof. intros Y;field;exact Y. Qed.
Lemma fast_logcdf_ratio_split x s e1 e2 : s<>0 -> 1+e1<>0 ->
  x/(s*(1+e1))*(1+e2)=x/s*((1+e2)/(1+e1)).
Proof. intros S E;field;split;assumption. Qed.
Lemma fast_logcdf_ratio_minus x s e1 e2 : s<>0 -> 1+e1<>0 ->
  x/s*((1+e2)/(1+e1))-x/s=x/s*((e2-e1)/(1+e1)).
Proof. intros S E;field;split;assumption. Qed.
Lemma fast_logcdf_div_minus_one x y : y<>0 -> x/y-1=(x-y)/y.
Proof. intros Y;field;exact Y. Qed.
Lemma fast_logcdf_mul_div_cancel a b c : c<>0 -> a*c*(b/c)=a*b.
Proof. intros C;field;exact C. Qed.

(** One more relative factor: the bounds add, plus their product's dust. *)
Lemma fast_logcdf_factor_step p d a b : Rabs(p-1)<=a*bpow radix2(-53) ->
  Rabs d<=b*bpow radix2(-53) -> 0<=a<=200 -> 0<=b<=200 ->
  Rabs(p*(1+d)-1)<=(a+b+/100)*bpow radix2(-53).
Proof.
  intros P D A Bb;apply Rabs_le_inv in P,D.
  replace(p*(1+d)-1)with((p-1)+d+(p-1)*d)by ring.
  apply Rabs_le;bpow_num_all;split;nra.
Qed.

Definition fast_logcdf_lower_allowance a :=
  if Rle_dec a 1 then 20 else if Rle_dec a 2 then 26 else 57.

Theorem fast_logcdf_lower_relative a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_normal_lower64 a) /\
  5/4*bpow radix2(-52)<=B(fast_normal_lower64 a)<=51/100 /\
  Rabs(B(fast_normal_lower64 a)-normal_tail(B a))<=
    fast_logcdf_lower_allowance(B a)*bpow radix2(-53)*normal_tail(B a).
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
  assert (Y16 : 0<y<=16)by lra.
  destruct(fast_logcdf_erfcx_sensitivity y (B z) Y16 Zerror)as[Sflat Sscaled].
  (* The four relative perturbations. *)
  set(d1:=(B e-exp(B t))/exp(B t)).
  set(d2:=exp(B t)/exp(-q)-1).
  set(d3:=(B f-gaussian_erfcx(B z))/gaussian_erfcx(B z)).
  set(d4:=(gaussian_erfcx(B z)-gaussian_erfcx y)/gaussian_erfcx y).
  assert (E1 : B e=exp(B t)*(1+d1))by(exact(fast_logcdf_split_rel(B e)(exp(B t))ltac:(lra))).
  assert (E2 : exp(B t)=exp(-q)*(1+d2))by(exact(fast_logcdf_split_ratio(exp(B t))(exp(-q))ltac:(lra))).
  assert (E3 : B f=gaussian_erfcx(B z)*(1+d3))by(exact(fast_logcdf_split_rel(B f)(gaussian_erfcx(B z))ltac:(lra))).
  assert (E4 : gaussian_erfcx(B z)=gaussian_erfcx y*(1+d4))by(exact(fast_logcdf_split_rel(gaussian_erfcx(B z))(gaussian_erfcx y)ltac:(lra))).
  assert (D1 : Rabs d1<=bpow radix2(-51)).
  { unfold d1,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(exp(B t)))by lra.
    apply(Rmult_le_reg_r(exp(B t)));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Eerror. }
  assert (D2 : Rabs d2<=33*bpow radix2(-53)).
  { unfold d2;replace(exp(B t)/exp(-q))with(exp(B t+q)).
    - pose proof(Rabs_le_inv _ _ Terror)as Te.
      assert (Q : 0<=q<=32)by(unfold q;clear - A;bpow_num_all;nra).
      assert (V : -/2<=B t+q<=/2)by(clear - Te Q;bpow_num_all;nra).
      pose proof(fast_logcdf_exp_small(B t+q)V)as X.
      clear - X V Q Te;apply Rabs_le;bpow_num_all;split;nra.
    - rewrite exp_plus;unfold Rdiv;f_equal;rewrite <-exp_Ropp;f_equal;ring. }
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
    (* As in FastNormal: build the equality directly; rewriting He stalls. *)
    assert (Product : B(fmul(erfcx_pow2(-1))e)*B f=B e*B f/2).
    { transitivity((/2*B e)*B f).
      - exact(f_equal(fun h:R=>h*B f)He).
      - exact(fast_normal_half_product(B e)(B f)). }
    assert (Ppos : 0<B e*B f/2)by(pose proof(bpow_gt_0 radix2(-47));pose proof(bpow_gt_0 radix2(-9));nra).
    (* The exact product is the tail times the four perturbation factors. *)
    assert (Tail : normal_tail(B a)=exp(-q)*gaussian_erfcx y/2).
    { assert (Esq : exp(-B a*B a/2)=exp(-q))by(f_equal;unfold q,Rdiv;ring).
      unfold normal_tail;rewrite Esq;reflexivity. }
    destruct(normal_tail_range(B a)Apos)as[Tpos Tup].
    assert (Pid : B e*B f/2=normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)))by(rewrite E1,E2,E3,E4,Tail;unfold Rdiv;ring).
    pose proof(Rabs_le_inv _ _ D1)as R1;pose proof(Rabs_le_inv _ _ D2)as R2.
    pose proof(Rabs_le_inv _ _ D3)as R3;pose proof(Rabs_le_inv _ _ D4flat)as R4.
    assert (Pup : B e*B f/2<=1)by(rewrite Pid;bpow_num_all;interval with(i_prec 80)).
    assert(Mbound : bnd 1 0 (B(fmul(erfcx_pow2(-1))e)*B f)).
    { rewrite Product;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;lra. }
    destruct(fmul_bnd 1 0 (fmul(erfcx_pow2(-1))e)f Fhe Ff ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Mbound)as[Fl' [L _]].
    assert (Lv : B(fast_normal_lower64 a)=rndF(B e*B f/2))by exact(eq_trans L(f_equal rndF Product)).
    clear L;rename Lv into L.
    assert (Normal : bpow radix2(-1022)<=Rabs(B e*B f/2)).
    { rewrite Rabs_pos_eq by lra;eapply Rle_trans with(bpow radix2(-57));[apply bpow_le;lia|].
      pose proof(bpow_gt_0 radix2(-47))as P47;pose proof(bpow_gt_0 radix2(-9))as P9;clear - E F P47 P9;bpow_num_all;nra. }
    pose proof(rnd_rel _ Normal)as Round0.
    change(Rabs(rndF(B e*B f/2)-B e*B f/2)<=bpow radix2(-53)*Rabs(B e*B f/2))in Round0.
    (* Transport along L without a rewrite search over the entry's terms. *)
    pose proof(eq_ind_r(fun v=>Rabs(v-B e*B f/2)<=bpow radix2(-53)*Rabs(B e*B f/2))Round0 L)as Round.
    set(d5:=(B(fast_normal_lower64 a)-B e*B f/2)/(B e*B f/2)).
    assert (E5 : B(fast_normal_lower64 a)=B e*B f/2*(1+d5))by(exact(fast_logcdf_split_rel(B(fast_normal_lower64 a))(B e*B f/2)ltac:(lra))).
    assert (D5 : Rabs d5<=bpow radix2(-53)).
    { unfold d5,Rdiv at 1;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(B e*B f/2))by lra.
      apply(Rmult_le_reg_r(B e*B f/2));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
      rewrite Rabs_pos_eq in Round by lra;exact Round. }
    (* Assemble: lower = tail(a) (1+d1)(1+d2)(1+d3)(1+d4)(1+d5). *)
    assert (Id : B(fast_normal_lower64 a)=normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5))).
    { rewrite E5,Pid;unfold Rdiv;ring. }
    pose proof(Rabs_le_inv _ _ D5)as R5.
    (* The five factors chained two at a time, first with the flat bounds. *)
    assert (S1 : Rabs((1+d1)-1)<=4*bpow radix2(-53))by(replace(1+d1-1)with d1 by ring;bpow_num_all;lra).
    assert (D3' : Rabs d3<=4*bpow radix2(-53))by(bpow_num_all;lra).
    assert (D5' : Rabs d5<=1*bpow radix2(-53))by(bpow_num_all;lra).
    assert (Pflat : Rabs((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5)-1)<=57*bpow radix2(-53)).
    { pose proof(fast_logcdf_factor_step _ _ _ _ S1 D2 ltac:(lra)ltac:(lra))as S2.
      pose proof(fast_logcdf_factor_step _ _ _ _ S2 D3' ltac:(lra)ltac:(lra))as S3.
      pose proof(fast_logcdf_factor_step _ _ _ _ S3 D4flat ltac:(lra)ltac:(lra))as S4.
      pose proof(fast_logcdf_factor_step _ _ _ _ S4 D5' ltac:(lra)ltac:(lra))as S5.
      eapply Rle_trans;[exact S5|bpow_num_all;lra]. }
    pose proof(Rabs_le_inv _ _ Pflat)as Pf.
    assert (Range : 5/4*bpow radix2(-52)<=B(fast_normal_lower64 a)<=51/100).
    { (* tail(a) >= exp(-32) erfcx(8/sqrt 2)/2 > 1.3 2^-52. *)
      assert (Tlow : 13/10*bpow radix2(-52)<=normal_tail(B a)).
      { rewrite Tail.
        assert (Edown : exp(-32)<=exp(-q))by(apply exp_le;unfold q;clear - A;bpow_num_all;nra).
        assert (Fdown : inv_sqrt_pi/(2*6)<=gaussian_erfcx y).
        { destruct(Rle_dec 1 y)as[Large|Small].
          - pose proof(normal_erfcx_large_lower y Large)as Low.
            eapply Rle_trans;[|exact Low];apply Rmult_le_compat_l;[apply Rlt_le,inv_sqrt_pi_positive|];apply Rinv_le_contravar;lra.
          - pose proof(normal_erfcx_small_lower y ltac:(lra))as Low;unfold inv_sqrt_pi in *;
            eapply Rle_trans;[|exact Low];interval with(i_prec 80). }
        assert (Cval : 56/100<inv_sqrt_pi)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
        assert (Fdown' : 46/1000<=gaussian_erfcx y)by lra.
        assert (Estep : 13/10*bpow radix2(-52)<=exp(-32)*(46/1000)/2)by(bpow_num_all;interval with(i_prec 80)).
        eapply Rle_trans;[exact Estep|].
        unfold Rdiv;apply Rmult_le_compat_r;[lra|].
        apply Rmult_le_compat;[left;apply exp_pos|lra|exact Edown|exact Fdown']. }
      rewrite Id;clear - Pf Tlow Tup Tpos;bpow_num_all;split;nra. }
    split;[exact Fl|];split;[exact Range|].
    rewrite Id;replace(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5))-normal_tail(B a))
      with(normal_tail(B a)*((1+d1)*(1+d2)*(1+d3)*(1+d4)*(1+d5)-1))by ring.
    rewrite Rabs_mult,(Rabs_pos_eq(normal_tail(B a)))by lra.
    rewrite(Rmult_comm(fast_logcdf_lower_allowance(B a)*bpow radix2(-53)));apply Rmult_le_compat_l;[lra|].
    (* The exponent perturbation at a given square: exp(u q) - 1 <= u q (1 + 33u). *)
    assert (D2of : forall qmax, q<=qmax -> 0<=qmax<=32 ->
      Rabs d2<=(qmax+2*qmax*qmax*bpow radix2(-53))*bpow radix2(-53)).
    { intros qmax Qm Qr;unfold d2;replace(exp(B t)/exp(-q))with(exp(B t+q)).
      - pose proof(Rabs_le_inv _ _ Terror)as Te.
        assert (Q : 0<=q)by(unfold q;clear - A;bpow_num_all;nra).
        assert (Tq : -(qmax*bpow radix2(-53))<=B t+q<=qmax*bpow radix2(-53))by(clear - Te Q Qm Qr;bpow_num_all;nra).
        assert (V : -/2<=B t+q<=/2)by(clear - Tq Qr;bpow_num_all;nra).
        pose proof(fast_logcdf_exp_small(B t+q)V)as X.
        clear - X Tq Qr;apply Rabs_le;bpow_num_all;split;nra.
      - rewrite exp_plus;unfold Rdiv;f_equal;rewrite <-exp_Ropp;f_equal;ring. }
    unfold fast_logcdf_lower_allowance.
    (* Chain the five factors two at a time with the region's bounds. *)
    destruct(Rle_dec(B a)1)as[Small|NotSmall].
    + assert (Ysmall : y<=70711/100000).
      { unfold y;apply Rmult_le_reg_r with(sqrt 2);[interval|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by interval;interval with(i_prec 80). }
      assert (D4' : Rabs d4<=99/10*bpow radix2(-53)).
      { eapply Rle_trans;[apply D4scaled;lra|];clear - Ysmall Ypos;bpow_num_all;nra. }
      pose proof(D2of(/2)ltac:(unfold q;clear - Small A;bpow_num_all;nra)ltac:(lra))as D2s.
      pose proof(fast_logcdf_factor_step _ _ _ _ S1 D2s ltac:(lra)ltac:(bpow_num_all;lra))as S2.
      pose proof(fast_logcdf_factor_step _ _ _ _ S2 D3' ltac:(bpow_num_all;lra)ltac:(lra))as S3.
      pose proof(fast_logcdf_factor_step _ _ _ _ S3 D4' ltac:(bpow_num_all;lra)ltac:(lra))as S4.
      pose proof(fast_logcdf_factor_step _ _ _ _ S4 D5' ltac:(bpow_num_all;lra)ltac:(lra))as S5.
      eapply Rle_trans;[exact S5|bpow_num_all;lra].
    + destruct(Rle_dec(B a)2)as[Middle|Large].
      * pose proof(D2of 2 ltac:(unfold q;clear - Middle A;bpow_num_all;nra)ltac:(lra))as D2m.
        pose proof(fast_logcdf_factor_step _ _ _ _ S1 D2m ltac:(lra)ltac:(bpow_num_all;lra))as S2.
        pose proof(fast_logcdf_factor_step _ _ _ _ S2 D3' ltac:(bpow_num_all;lra)ltac:(lra))as S3.
        pose proof(fast_logcdf_factor_step _ _ _ _ S3 D4flat ltac:(bpow_num_all;lra)ltac:(lra))as S4.
        pose proof(fast_logcdf_factor_step _ _ _ _ S4 D5' ltac:(bpow_num_all;lra)ltac:(lra))as S5.
        eapply Rle_trans;[exact S5|bpow_num_all;lra].
      * pose proof(fast_logcdf_factor_step _ _ _ _ S1 D2 ltac:(lra)ltac:(lra))as S2.
        pose proof(fast_logcdf_factor_step _ _ _ _ S2 D3' ltac:(lra)ltac:(lra))as S3.
        pose proof(fast_logcdf_factor_step _ _ _ _ S3 D4flat ltac:(lra)ltac:(lra))as S4.
        pose proof(fast_logcdf_factor_step _ _ _ _ S4 D5' ltac:(lra)ltac:(lra))as S5.
        eapply Rle_trans;[exact S5|bpow_num_all;lra].
Qed.

Lemma fast_logcdf_cdf_complement a : normal_cdf a=1-normal_tail a.
Proof. rewrite normal_tail_complement;unfold normal_cdf;apply fast_normal_half_complement. Qed.

(** The tail is at most half the Gaussian factor, since erfcx is at most one. *)
Lemma fast_logcdf_tail_upper a : 0<a -> normal_tail a<=exp(-a*a/2)/2.
Proof.
  intros A.
  assert (Y : 0<a/sqrt 2)by(apply Rdiv_lt_0_compat;[exact A|interval with(i_prec 80)]).
  pose proof(normal_erfcx_unit_upper _ Y)as F.
  pose proof(exp_pos(-a*a/2))as E.
  unfold normal_tail;apply Rmult_le_compat_r;[lra|];nra.
Qed.

(** The lower tail's relative error moves the logarithm of the complement by
    at most [21u]: [q/(1-q)] is at most one below [a = 1], below [0.44]
    on [[1, 2]] and below [0.073] beyond two. *)
Lemma fast_logcdf_complement_log a qh : bpow radix2(-33)<=a<=8 ->
  Rabs(qh-normal_tail a)<=fast_logcdf_lower_allowance a*bpow radix2(-53)*normal_tail a ->
  Rabs(ln(1-qh)-ln(1-normal_tail a))<=21*bpow radix2(-53).
Proof.
  intros A Relative.
  assert (Apos : 0<a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(normal_tail_range a Apos)as[Tpos Tup].
  set(q:=normal_tail a)in *.
  (* The perturbation of the complement, relative to the exact complement. *)
  set(d:=(q-qh)/(1-q)).
  assert (Did : 1-qh=(1-q)*(1+d))by(unfold d;field;lra).
  assert (D : Rabs d<=20*bpow radix2(-53)).
  { unfold d,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(1-q))by lra.
    apply(Rmult_le_reg_r(1-q));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    rewrite Rabs_minus_sym.
    unfold fast_logcdf_lower_allowance in Relative.
    destruct(Rle_dec a 1)as[S|L].
    - eapply Rle_trans;[exact Relative|];bpow_num_all;nra.
    - destruct(Rle_dec a 2)as[M|L2].
      + assert (Qup : q<=exp(-/2)/2).
        { unfold q;eapply Rle_trans;[apply(normal_tail_decreasing 1 a);lra|].
          eapply Rle_trans;[apply fast_logcdf_tail_upper;lra|];right;f_equal;f_equal;field. }
        assert (Qnum : q<=31/100)by(eapply Rle_trans;[exact Qup|interval with(i_prec 80)]).
        eapply Rle_trans;[exact Relative|];bpow_num_all;nra.
      + assert (Qup : q<=exp(-2)/2).
        { unfold q;eapply Rle_trans;[apply(normal_tail_decreasing 2 a);lra|].
          eapply Rle_trans;[apply fast_logcdf_tail_upper;lra|];right;f_equal;f_equal;field. }
        assert (Qnum : q<=7/100)by(eapply Rle_trans;[exact Qup|interval with(i_prec 80)]).
        eapply Rle_trans;[exact Relative|];bpow_num_all;nra. }
  assert (Dpos : 0<1+d)by(apply Rabs_le_inv in D;bpow_num_all;lra).
  rewrite Did,ln_mult by lra.
  replace(ln(1-q)+ln(1+d)-ln(1-q))with(ln(1+d))by ring.
  apply Rabs_le_inv in D;apply Rabs_le;bpow_num_all;split;interval with(i_prec 120).
Qed.

(** The quantities of the positive branch as reals: [Q] the rounded lower
    tail, [Wv = RN(1 - Q)], [Dv = RN(1 - Wv)], [Gv] the bounded logarithm of
    [Wv], [Rv = RN(Q / Dv)] and [Y = RN(Gv Rv)]. These lemmas carry the
    arithmetic in a small context; the theorem below supplies the IEEE facts. *)

Lemma fast_logcdf_ratio_range Q Wv Dv :
  5/4*bpow radix2(-52)<=Q<=51/100 ->
  Rabs(Wv-(1-Q))<=bpow radix2(-54) ->
  Rabs(Dv-(1-Wv))<=bpow radix2(-53)*(1-Wv) ->
  0<Dv /\ 4/5<=Q/Dv<=4/3.
Proof.
  intros HQ HW HD.
  pose proof(Rabs_le_inv _ _ HW)as We;pose proof(Rabs_le_inv _ _ HD)as De;pose proof(bpow_gt_0 radix2(-52))as P52.
  destruct HQ as[Qlo Qhi].
  assert (Dlow : (1-bpow radix2(-53))*(Q-bpow radix2(-54))<=Dv)by(bpow_num_all;nra).
  assert (Dup : Dv<=(1+bpow radix2(-53))*(Q+bpow radix2(-54)))by(bpow_num_all;nra).
  assert (Dpos : 0<Dv)by(bpow_num_all;nra).
  split;[exact Dpos|].
  split.
  - apply(Rmult_le_reg_r Dv);[lra|];unfold Rdiv;rewrite(Rmult_assoc Q),(Rinv_l Dv),Rmult_1_r by lra;bpow_num_all;nra.
  - apply(Rmult_le_reg_r Dv);[lra|];unfold Rdiv;rewrite(Rmult_assoc Q),(Rinv_l Dv),Rmult_1_r by lra;bpow_num_all;nra.
Qed.

Lemma fast_logcdf_log_range Wv : /4<=Wv<=1-bpow radix2(-52) ->
  -7/5<=ln Wv<= -bpow radix2(-52) /\ Rabs(ln Wv)=-ln Wv.
Proof.
  intros HWr.
  assert (LnW : -7/5<=ln Wv<= -bpow radix2(-52)).
  { split.
    - apply Rle_trans with(ln(/4));[interval with(i_prec 80)|apply ln_le;lra].
    - apply Rle_trans with(ln(1-bpow radix2(-52)));[apply ln_le;lra|bpow_num_all;interval with(i_prec 120)]. }
  split;[exact LnW|apply Rabs_left1;pose proof(bpow_gt_0 radix2(-52));lra].
Qed.

Lemma fast_logcdf_product_range Q Wv Dv Gv Rv :
  5/4*bpow radix2(-52)<=Q<=51/100 ->
  Rabs(Wv-(1-Q))<=bpow radix2(-54) ->
  /4<=Wv<=1-bpow radix2(-52) ->
  Rabs(Dv-(1-Wv))<=bpow radix2(-53)*(1-Wv) ->
  Rabs(Gv-ln Wv)<=bpow radix2(-53)*Rabs(ln Wv)+bpow radix2(-65) ->
  Rabs(Rv-Q/Dv)<=bpow radix2(-53)*(Q/Dv) ->
  Gv<0 /\ 3/4<=Rv<=134/100 /\ Gv*Rv<0 /\ -2<=Gv*Rv<=2 /\ bpow radix2(-1022)<=Rabs(Gv*Rv).
Proof.
  intros HQ HW HWr HD HG HR.
  destruct(fast_logcdf_ratio_range Q Wv Dv HQ HW HD)as[Dpos Ratio].
  destruct(fast_logcdf_log_range Wv HWr)as[LnW LabsEq].
  pose proof(Rabs_le_inv _ _ HG)as Ge;pose proof(Rabs_le_inv _ _ HR)as Re.
  rewrite LabsEq in Ge.
  assert (Gneg : Gv<0)by(bpow_num_all;lra).
  assert (Gabs : -141/100<=Gv<=141/100)by(bpow_num_all;lra).
  assert (Gmag : bpow radix2(-53)<=-Gv)by(bpow_num_all;lra).
  assert (Rr : 3/4<=Rv<=134/100)by(bpow_num_all;lra).
  assert (Pneg : Gv*Rv<0)by nra.
  assert (P1 : -2<=Gv*Rv)by nra.
  assert (P2 : Gv*Rv<=2)by nra.
  assert (P3 : bpow radix2(-1022)<=Rabs(Gv*Rv))by(rewrite Rabs_left by exact Pneg;bpow_num_all;nra).
  destruct Rr as[Rr1 Rr2].
  repeat split;assumption.
Qed.

(** The whole positive branch over the reals: the complement's logarithm,
    Kahan's corrected ratio, the two roundings, and the final budget. *)
Lemma fast_logcdf_positive_real Q Wv Dv Gv Rv Y L :
  5/4*bpow radix2(-52)<=Q<=51/100 ->
  Rabs(Wv-(1-Q))<=bpow radix2(-54) ->
  /4<=Wv<=1-bpow radix2(-52) ->
  Rabs(Dv-(1-Wv))<=bpow radix2(-53)*(1-Wv) ->
  Rabs(Gv-ln Wv)<=bpow radix2(-53)*Rabs(ln Wv)+bpow radix2(-65) ->
  Rabs(Rv-Q/Dv)<=bpow radix2(-53)*(Q/Dv) ->
  Rabs(Y-Gv*Rv)<=bpow radix2(-53)*Rabs(Gv*Rv) ->
  Rabs(ln(1-Q)-L)<=21*bpow radix2(-53) ->
  Y<0 /\ Rabs(Y-L)<=fast_logcdf_budget L.
Proof.
  intros HQ HW HWr HD HG HR HY HL.
  destruct(fast_logcdf_ratio_range Q Wv Dv HQ HW HD)as[Dpos Ratio].
  destruct(fast_logcdf_log_range Wv HWr)as[LnW LabsEq].
  destruct(fast_logcdf_product_range Q Wv Dv Gv Rv HQ HW HWr HD HG HR)as[Gneg [RvRange [Pneg [Pbox Pnormal]]]].
  pose proof(Rabs_le_inv _ _ HY)as Yr0.
  rewrite(Rabs_left(Gv*Rv))in Yr0 by exact Pneg.
  assert (Yneg : Y<0)by(bpow_num_all;lra).
  split;[exact Yneg|].
  destruct HQ as[Qlo Qhi].
  set(Lh:=ln(1-Q))in *.
  set(delta:=Wv-(1-Q))in *.
  pose proof(Rabs_le_inv _ _ HW)as Dl.
  pose proof(bpow_gt_0 radix2(-52))as P52.
  assert (Qpos : 0<Q)by lra.
  assert (Qup : Q<=51/100)by lra.
  (* sigma = 1 - w = Q - delta, within a quarter of Q. *)
  set(sigma:=1-Wv)in *.
  assert (SigmaId : sigma=Q-delta)by(unfold sigma,delta;ring).
  assert (SigmaRange : 3/4*Q<=sigma<=5/4*Q)by(bpow_num_all;lra).
  assert (SigmaPos : 0<sigma)by lra.
  assert (Ratio' : 4/5<=Q/sigma<=4/3).
  { split;apply(Rmult_le_reg_r sigma);try lra;unfold Rdiv;rewrite(Rmult_assoc Q),(Rinv_l sigma),Rmult_1_r by lra;lra. }
  (* The logarithm of w splits as Lh + ln(1 + eps). *)
  set(eps:=delta/(1-Q)).
  assert (Epsid : Wv=(1-Q)*(1+eps))by(exact(fast_logcdf_split_rel Wv(1-Q)ltac:(lra))).
  assert (Eps : Rabs eps<=bpow radix2(-54)*(100/49)).
  { unfold eps,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(1-Q))by lra.
    apply(Rmult_le_reg_r(1-Q));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
  pose proof(Rabs_le_inv _ _ Eps)as El.
  assert (LnWsplit : ln Wv=Lh+ln(1+eps)).
  { rewrite Epsid,ln_mult;[reflexivity|lra|bpow_num_all;lra]. }
  assert (LnEps : Rabs(ln(1+eps))<=21/10*bpow radix2(-54)).
  { apply Rabs_le;bpow_num_all;split;interval with(i_prec 120). }
  pose proof(Rabs_le_inv _ _ LnEps)as LnEl.
  (* |Lh| <= 1.41 Q and |Lh| <= 3/4. *)
  assert (Lhneg : Lh<0)by(unfold Lh;rewrite <-ln_1;apply ln_increasing;lra).
  assert (LhRel : -Lh<=141/100*Q).
  { unfold Lh;assert (Qr : bpow radix2(-52)<=Q<=51/100)by(bpow_num_all;lra).
    clear - Qr;bpow_num_all.
    destruct(Rle_dec Q(/4))as[Small|Large].
    - (* ln z <= z - 1 at z = 1/(1-Q): -ln(1-Q) <= Q/(1-Q) <= 4/3 Q. *)
      assert (Z : 0<1-Q)by lra.
      pose proof(exp_ineq1_le(/(1-Q)-1))as E.
      assert (Lx : ln(/(1-Q))<=/(1-Q)-1).
      { rewrite <-(ln_exp(/(1-Q)-1));apply ln_le;[apply Rinv_0_lt_compat;lra|lra]. }
      rewrite ln_Rinv in Lx by lra.
      assert (R : /(1-Q)-1=Q/(1-Q))by(field;lra).
      assert (R2 : Q/(1-Q)<=4/3*Q).
      { apply Rmult_le_reg_r with(1-Q);[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
      lra.
    - assert (Q4 : /4<=Q<=51/100)by lra.
      assert (H0 : -ln(1-Q)-141/100*Q<=0)by(clear - Q4;interval with(i_bisect Q,i_prec 60)).
      lra. }
  assert (LhAbs : -Lh<=3/4).
  { unfold Lh;eapply Rle_trans with(-ln(1-51/100));[apply Ropp_le_contravar,ln_le;lra|interval with(i_prec 80)]. }
  (* Kahan's identity: ln(w) Q/sigma - Lh = Lh (Q/sigma - 1) + ln(1+eps) Q/sigma. *)
  assert (RatioMinus : Rabs(Q/sigma-1)<=4/3*bpow radix2(-54)/Q).
  { rewrite(fast_logcdf_div_minus_one Q sigma)by lra.
    replace(Q-sigma)with delta by(rewrite SigmaId;ring).
    unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq sigma)by lra.
    apply(Rmult_le_reg_r sigma);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    apply Rle_trans with(bpow radix2(-54));[exact HW|].
    apply(Rmult_le_reg_r Q);[lra|].
    replace(4*/3*bpow radix2(-54)*/Q*sigma*Q)with(4*/3*bpow radix2(-54)*sigma*(Q*/Q))by ring.
    rewrite Rinv_r by lra;rewrite Rmult_1_r;bpow_num_all;lra. }
  assert (Kahan : Rabs(ln Wv*(Q/sigma)-Lh)<=5/2*bpow radix2(-53)).
  { rewrite LnWsplit;replace((Lh+ln(1+eps))*(Q/sigma)-Lh)with(Lh*(Q/sigma-1)+ln(1+eps)*(Q/sigma))by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite !Rabs_mult,(Rabs_pos_eq(Q/sigma))by lra.
    pose proof(Rabs_le_inv _ _ RatioMinus)as Rm.
    assert (First : Rabs Lh*Rabs(Q/sigma-1)<=141/100*Q*(4/3*bpow radix2(-54)/Q)).
    { apply Rmult_le_compat;try apply Rabs_pos;[rewrite Rabs_left by lra;lra|exact RatioMinus]. }
    rewrite(fast_logcdf_mul_div_cancel(141/100)(4/3*bpow radix2(-54))Q)in First by lra.
    assert (Second : Rabs(ln(1+eps))*(Q/sigma)<=21/10*bpow radix2(-54)*(4/3)).
    { apply Rmult_le_compat;try apply Rabs_pos;try lra;exact LnEps. }
    bpow_num_all;lra. }
  (* The computed ratio against Q/sigma: two relative roundings. *)
  assert (Dv_id : Dv=sigma*(1+(Dv-sigma)/sigma))by(exact(fast_logcdf_split_rel Dv sigma ltac:(lra))).
  set(e1:=(Dv-sigma)/sigma).
  assert (E1 : Rabs e1<=bpow radix2(-53)).
  { unfold e1,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq sigma)by lra.
    apply(Rmult_le_reg_r sigma);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact HD. }
  pose proof(Rabs_le_inv _ _ E1)as E1l.
  set(e2:=(Rv-Q/Dv)/(Q/Dv)).
  assert (QD : 0<Q/Dv)by(apply Rdiv_lt_0_compat;lra).
  assert (Rv_id : Rv=Q/Dv*(1+e2))by(exact(fast_logcdf_split_rel Rv(Q/Dv)ltac:(lra))).
  assert (E2 : Rabs e2<=bpow radix2(-53)).
  { unfold e2,Rdiv at 1;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(Q/Dv))by lra.
    apply(Rmult_le_reg_r(Q/Dv));[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact HR. }
  pose proof(Rabs_le_inv _ _ E2)as E2l.
  assert (Rv_sigma : Rv=Q/sigma*((1+e2)/(1+e1))).
  { rewrite Rv_id,Dv_id;fold e1;apply fast_logcdf_ratio_split;[lra|bpow_num_all;lra]. }
  assert (RvErr : Rabs(Rv-Q/sigma)<=4/3*(201/100*bpow radix2(-53))).
  { rewrite Rv_sigma,fast_logcdf_ratio_minus by(bpow_num_all;lra).
    rewrite Rabs_mult,(Rabs_pos_eq(Q/sigma))by lra.
    apply Rmult_le_compat;try apply Rabs_pos;try lra.
    apply Rabs_le;bpow_num_all;split;interval with(i_prec 80). }
  pose proof(Rabs_le_inv _ _ RvErr)as RvE.
  (* |ln w| against |Lh|. *)
  assert (LnWabs : Rabs(ln Wv)<= -Lh+21/10*bpow radix2(-54)).
  { rewrite LnWsplit;eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_left Lh)by lra;lra. }
  pose proof(Rabs_pos(ln Wv))as LnWpos.
  (* Assemble: Y - L = (Y - Gv Rv) + (Gv Rv - ln w Q/sigma) + (ln w Q/sigma - Lh) + (Lh - L). *)
  assert (Prod : Rabs(Gv*Rv-ln Wv*(Q/sigma))<=(bpow radix2(-53)*Rabs(ln Wv)+bpow radix2(-65))*(27/20)+Rabs(ln Wv)*(4/3*(201/100*bpow radix2(-53)))).
  { replace(Gv*Rv-ln Wv*(Q/sigma))with((Gv-ln Wv)*Rv+ln Wv*(Rv-Q/sigma))by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite !Rabs_mult,(Rabs_pos_eq Rv)by lra.
    assert (A1 : Rabs(Gv-ln Wv)*Rv<=(bpow radix2(-53)*Rabs(ln Wv)+bpow radix2(-65))*(27/20)).
    { apply Rmult_le_compat;try apply Rabs_pos;try lra;exact HG. }
    assert (A2 : Rabs(ln Wv)*Rabs(Rv-Q/sigma)<=Rabs(ln Wv)*(4/3*(201/100*bpow radix2(-53)))).
    { apply Rmult_le_compat_l;[apply Rabs_pos|exact RvErr]. }
    lra. }
  pose proof(Rabs_le_inv _ _ Prod)as Pr.
  assert (GvRv : Rabs(Gv*Rv)<=(Rabs(ln Wv)*(1+bpow radix2(-53))+bpow radix2(-65))*(27/20)).
  { rewrite Rabs_mult,(Rabs_pos_eq Rv)by lra;apply Rmult_le_compat;try apply Rabs_pos;try lra.
    pose proof(Rabs_le_inv _ _ HG)as Ge2;pose proof(Rle_abs(ln Wv))as La2;
    pose proof(Rabs_le_inv(ln Wv)(Rabs(ln Wv))(Rle_refl _))as Lb;apply Rabs_le;split;lra. }
  pose proof(Rabs_le_inv _ _ HY)as Yr.
  assert (Labs : Rabs L>= -Lh-21*bpow radix2(-53)).
  { pose proof(Rabs_le_inv _ _ HL)as C2;pose proof(Rle_abs(-L))as C3;rewrite Rabs_Ropp in C3;lra. }
  assert (Lsmall : Rabs L<=1).
  { pose proof(Rabs_le_inv _ _ HL)as C2;apply Rabs_le;bpow_num_all;lra. }
  pose proof(Rabs_le_inv _ _ Kahan)as Kl.
  pose proof(Rabs_le_inv _ _ HL)as Lql.
  unfold fast_logcdf_budget.
  clear - Yr Pr Kl Lql LnWabs GvRv Labs Lsmall LnWpos.
  apply Rabs_le;bpow_num_all;split;lra.
Qed.

(** The IEEE sequence: each rounding is one correctly rounded operation whose
    value and error the real lemmas consume. *)
Theorem fast_logcdf_positive_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_logcdf_positive64 a) /\
  B(fast_logcdf_positive64 a)<0 /\
  Rabs(B(fast_logcdf_positive64 a)-ln(normal_cdf(B a)))<=fast_logcdf_budget(ln(normal_cdf(B a))).
Proof.
  intros Fa A.
  assert (Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  destruct(fast_logcdf_lower_relative a Fa A)as[Fq [Qrange Qrel]].
  set(qh:=fast_normal_lower64 a)in *.
  destruct(erfcx_pow2_ok 0 ltac:(lia))as[Fone One];change(bpow radix2 0)with 1 in One.
  pose proof(bpow_gt_0 radix2(-52))as P52.
  (* w = RN(1 - qh): within 2^-54 of 1 - qh, in [1/4, 1 - 2^-52]. *)
  assert (Wbound : bnd 1 0 (B(erfcx_pow2 0)-B qh)).
  { rewrite One;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;apply Rabs_le;bpow_num_all;lra. }
  destruct(fsub_bnd 1 0 (erfcx_pow2 0)qh Fone Fq ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Wbound)as[Fw [W _]].
  rewrite One in W;set(w:=fsub(erfcx_pow2 0)qh)in *.
  assert (Werror : Rabs(B w-(1-B qh))<=bpow radix2(-54)).
  { rewrite W;apply(rnd_err_below _ 0);[lia|];rewrite Rabs_pos_eq by(bpow_num_all;lra);
    change(bpow radix2 0)with 1;bpow_num_all;lra. }
  assert (Wup : B w<=1-bpow radix2(-52)).
  { rewrite W;replace(1-bpow radix2(-52))with(IZR 4503599627370495*bpow radix2(-52))by(bpow_num_all;lra).
    apply round_le_generic;[exact _|exact _|apply bnd_fmt;lia|bpow_num_all;lra]. }
  assert (Wlow : /4<=B w).
  { rewrite W;change(/4)with(bpow radix2(-2));apply round_ge_generic;[exact _|exact _| |bpow_num_all;lra].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (Wrange : /4<=B w<=1-bpow radix2(-52))by lra.
  (* d = RN(1 - w): one relative rounding. *)
  assert (Dexact : bpow radix2(-52)-bpow radix2(-54)<=1-B w<=3/4).
  { pose proof(Rabs_le_inv _ _ Werror);bpow_num_all;lra. }
  assert (Dbound : bnd 1 0 (B(erfcx_pow2 0)-B w)).
  { rewrite One;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;apply Rabs_le;bpow_num_all;lra. }
  destruct(fsub_bnd 1 0 (erfcx_pow2 0)w Fone Fw ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Dbound)as[Fd [D _]].
  rewrite One in D;set(d:=fsub(erfcx_pow2 0)w)in *.
  assert (Dnormal : bpow radix2(-1022)<=Rabs(1-B w)).
  { rewrite Rabs_pos_eq by(bpow_num_all;lra);eapply Rle_trans;[|exact(proj1 Dexact)];bpow_num_all;lra. }
  pose proof(rnd_rel _ Dnormal)as Derror.
  change(Rabs(rndF(1-B w)-(1-B w))<=bpow radix2(-53)*Rabs(1-B w))in Derror.
  rewrite <-D in Derror.
  rewrite(Rabs_pos_eq(1-B w))in Derror by(bpow_num_all;lra).
  destruct(fast_logcdf_ratio_range(B qh)(B w)(B d)Qrange Werror Derror)as[Dpos Ratio].
  (* g = ln_fast(w). *)
  assert (Wpos : 0<B w)by lra.
  destruct(fast_logcdf_ln_ok w Fw Wpos)as[Fg Gerror].
  set(g:=fast_ln_regular64 w)in *.
  (* r = RN(qh / d). *)
  assert (Rbound : bnd 1 1 (B qh/B d)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 1)with 2;apply Rabs_le;lra. }
  destruct(fdiv_bnd 1 1 qh d Fq ltac:(lra)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Rbound)as[Fr [R _]].
  set(r:=fdiv qh d)in *.
  assert (Rnormal : bpow radix2(-1022)<=Rabs(B qh/B d))by(rewrite Rabs_pos_eq by lra;bpow_num_all;lra).
  pose proof(rnd_rel _ Rnormal)as Rerror.
  change(Rabs(rndF(B qh/B d)-B qh/B d)<=bpow radix2(-53)*Rabs(B qh/B d))in Rerror.
  rewrite <-R in Rerror.
  rewrite(Rabs_pos_eq(B qh/B d))in Rerror by lra.
  (* The product: its range from the real lemma, then one rounding. *)
  destruct(fast_logcdf_product_range(B qh)(B w)(B d)(B g)(B r)Qrange Werror Wrange Derror Gerror Rerror)
    as[Gneg [Rr [Pneg [Pbox Pnormal]]]].
  assert (Pbound : bnd 1 1 (B g*B r)).
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 1)with 2;apply Rabs_le;exact Pbox. }
  destruct(fmul_bnd 1 1 g r Fg Fr ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Pbound)as[Fp [P _]].
  unfold fast_logcdf_positive64;fold qh;fold w;fold d;fold g;fold r.
  pose proof(rnd_rel _ Pnormal)as Perror.
  change(Rabs(rndF(B g*B r)-B g*B r)<=bpow radix2(-53)*Rabs(B g*B r))in Perror.
  rewrite <-P in Perror.
  (* The target and the complement's perturbation. *)
  rewrite fast_logcdf_cdf_complement.
  pose proof(fast_logcdf_complement_log(B a)(B qh)A Qrel)as Complement.
  destruct(fast_logcdf_positive_real(B qh)(B w)(B d)(B g)(B r)(B(fmul g r))(ln(1-normal_tail(B a)))
    Qrange Werror Wrange Derror Gerror Rerror Perror Complement)as[Neg Error].
  split;[exact Fp|];split;[exact Neg|exact Error].
Qed.

(** * Dispatch *)

Theorem fast_logcdf_screen_finite x : finite x ->
  (fast_logcdf_screen64 x=true <->
    (B x<0 /\ bpow radix2(-33)<=Rabs(B x)<=45/2) \/ (0<=B x /\ bpow radix2(-33)<=Rabs(B x)<=8)).
Proof.
  intros Fx;assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fmin Min].
  destruct(erfcx_pow2_ok 3 ltac:(lia))as[Fmax Max].
  destruct fast_logcdf_limit_ok as[Flim Lim].
  assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  unfold fast_logcdf_screen64;rewrite andb_true_iff,(normal_le_true _ _ Fmin Fa),Min,B_abs.
  destruct(normal_lt x normal_zero)eqn:Sign.
  - apply normal_lt_true in Sign;try assumption;rewrite Zero in Sign.
    rewrite(normal_le_true _ _ Fa Flim),Lim,B_abs;cbv iota.
    split;[intros[H1 H2];left;repeat split;lra|intros[[_ [H1 H2]]|[H0 _]];[split;lra|lra]].
  - apply normal_lt_false in Sign;try assumption;rewrite Zero in Sign.
    rewrite(normal_le_true _ _ Fa Fmax),Max,B_abs;change(bpow radix2 3)with 8;cbv iota.
    split;[intros[H1 H2];right;repeat split;lra|intros[[H0 _]|[_ [H1 H2]]];[lra|split;lra]].
Qed.

(** The accelerated entry: finite, negative, within the mixed budget of
    [ln Φ(x)], on both branches. *)
Theorem fast_logcdf_entry_ok x : finite x -> fast_logcdf_screen64 x=true ->
  finite(fast_logcdf_entry64 x) /\
  B(fast_logcdf_entry64 x)<0 /\
  Rabs(B(fast_logcdf_entry64 x)-ln(normal_cdf(B x)))<=fast_logcdf_budget(ln(normal_cdf(B x))).
Proof.
  intros Fx Screen.
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  pose proof(proj1(fast_logcdf_screen_finite x Fx)Screen)as Domain.
  unfold fast_logcdf_entry64;rewrite Screen.
  destruct(normal_lt x normal_zero)eqn:Sign.
  - apply normal_lt_true in Sign;try assumption;rewrite Zero in Sign.
    destruct Domain as[[_ D]|[P _]];[|lra].
    rewrite Rabs_left in D by exact Sign.
    destruct(fast_logcdf_negative_ok(b64_abs x)Fa ltac:(rewrite B_abs,(Rabs_left(B x)Sign);exact D))as[F [Neg Error]].
    rewrite B_abs,(Rabs_left(B x)Sign)in Error.
    assert(Target : normal_cdf(B x)=normal_tail(-B x)).
    { symmetry;rewrite <-(Rabs_left(B x)Sign);apply normal_negative_cdf;lra. }
    rewrite Target;split;[exact F|];split;[lra|exact Error].
  - apply normal_lt_false in Sign;try assumption;rewrite Zero in Sign.
    destruct Domain as[[N _]|[_ D]];[lra|].
    rewrite Rabs_pos_eq in D by exact Sign.
    destruct(fast_logcdf_positive_ok(b64_abs x)Fa ltac:(rewrite B_abs,(Rabs_pos_eq(B x)Sign);exact D))as[F [Neg Error]].
    rewrite B_abs,(Rabs_pos_eq(B x)Sign)in Error.
    split;[exact F|];split;[exact Neg|exact Error].
Qed.

Theorem fast_logcdf_fallback x : fast_logcdf_screen64 x=false ->
  fast_logcdf_entry64 x=normal_entry64 NormalLogCdf x.
Proof. intros Screen;unfold fast_logcdf_entry64;rewrite Screen;reflexivity. Qed.

Theorem fast_logcdf_fallback_contract x : fast_logcdf_screen64 x=false ->
  normal_contract NormalLogCdf x (fast_logcdf_entry64 x).
Proof. intros Screen;rewrite fast_logcdf_fallback by exact Screen;apply normal_public_contract. Qed.

Theorem fast_logcdf_nonfinite x : Binary.is_finite 53 1024 x=false ->
  fast_logcdf_entry64 x=normal_entry64 NormalLogCdf x.
Proof.
  intros Nonfinite;destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;reflexivity.
  - reflexivity.
Qed.

Theorem fast_logcdf_zeros :
  fast_logcdf_entry64(B754_zero 53 1024 false)=normal_entry64 NormalLogCdf(B754_zero 53 1024 false) /\
  fast_logcdf_entry64(B754_zero 53 1024 true)=normal_entry64 NormalLogCdf(B754_zero 53 1024 true).
Proof. split;reflexivity. Qed.
