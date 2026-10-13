(** Both negative fast branches against the finite Gaussian definition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ErfcxGaussianTarget ErfcxGaussianReflection
  ErfcxReflectionSquare ErfcxReflectionExp ErfcxReflectionSubtract
  ErfcxReflectionValue ErfcxReflectionOmitted ErfcxTableEntry ErfcxTableReflectionEntry.
Open Scope R_scope.
Theorem reflection_value_analytic_ieee x : finite x -> B reflection_limit<B x< -/2 ->
  let '(h,l,m):=reflection_value64 x in
  let F:=gaussian_erfcx(B x)/bpow radix2 m in
  finite h /\ finite l /\ (1<=m<=1024)%Z /\ /2<=B h<=4 /\
  /4<=F<=3 /\ B h=rndF(B h+B l) /\
  Rabs((B h+B l-F)/F)<=bpow radix2 (-67).
Proof.
  intros Fx X.
  pose proof(reflection_square_ieee x Fx X) as Square.
  pose proof(reflection_square_exp_ieee x Fx X) as Exp.
  pose proof(reflection_dispatch_range x Fx X) as Dispatch.
  pose proof(reflection_omitted_input x Fx X) as OmittedInput.
  unfold reflection_value64. destruct(two_prod64 x x) as [s se].
  destruct Square as [Fs [Fse [Exact [S Low]]]].
  pose proof(reflection_exp_ideal_range s se Fs ltac:(rewrite Rabs_pos_eq;lra) Fse Low) as Ideal.
  rewrite Exact in Ideal.
  destruct(reflection_exp64 s se) as [[eh el]k].
  destruct Exp as [Feh [Fel [K0 [Eh [El [Norm Error]]]]]].
  destruct Dispatch as [K Small].
  set(E:=exp(B x*B x)/bpow radix2 k) in *.
  set(de:=B eh+B el-E).
  assert (De : Rabs de<=IZR 209*bpow radix2 (-78))
    by (unfold de;rewrite Rabs_minus_sym;exact Error).
  set(G:=gaussian_erfcx(-B x)).
  assert (Reflection : gaussian_erfcx(B x)=2*exp(B x*B x)-G).
  { unfold G;rewrite gaussian_erfcx_reflection;ring. }
  assert (Target : gaussian_erfcx(B x)/bpow radix2 (k+1)=E-G*bpow radix2 (-k-1)).
  { rewrite Reflection,reflection_scaled_identity;reflexivity. }
  destruct(104<?k)%Z eqn:Branch.
  - apply Z.ltb_lt in Branch. specialize(OmittedInput Branch).
    pose proof(gaussian_scaled_omission (-B x) k OmittedInput) as Correction.
    replace (-B x * -B x) with (B x*B x) in Correction by ring.
    fold E G in Correction.
    destruct(reflection_omitted_gaussian_budget E (G*bpow radix2 (-k-1)) de Ideal Correction De)
      as [Range Bound].
    cbv zeta. rewrite Target.
    split;[exact Feh|]. split;[exact Fel|]. split;[lia|].
    split;[split;lra|]. split;[exact Range|]. split;[exact Norm|].
    replace (B eh+B el) with (E+de) by (unfold de;ring).
    eapply Rle_trans;[exact Bound|apply bpow_le;lia].
  - apply Z.ltb_ge in Branch. specialize(Small Branch).
    assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
    assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
    pose proof(reflection_table_value_bounds (fneg x) Fn ltac:(rewrite Bn;exact Small)) as Table.
    pose proof(table_eval_ieee (fneg x) Fn ltac:(rewrite Bn;lra)) as Finite.
    rewrite Bn in Table. fold G in Table.
    destruct(table_eval64(fneg x)) as [gh gl].
    destruct Finite as [Fgh [Fgl _]]. destruct Table as [Gr [Gh [Gl Gerror]]].
    pose proof(reflection_subtract_ieee eh el gh gl k de (B gh+B gl-G)
      Feh Fel Fgh Fgl Eh El Gh Gl ltac:(lia) De Gerror) as Sub.
    destruct(reflection_subtract64 eh el gh gl k) as [h l].
    destruct Sub as [Fh [Fl [Hr [N Err]]]]. cbv zeta. rewrite Target.
    assert (Sc : 0<bpow radix2 (-k-1)<=/2).
    { split;[apply bpow_gt_0|]. change (/2) with (bpow radix2 (-1));apply bpow_le;lia. }
    split;[exact Fh|]. split;[exact Fl|]. split;[lia|]. split;[exact Hr|].
    split;[split;nra|]. split;[exact N|].
    replace (B eh+B el-de) with E in Err by (unfold de;ring).
    replace (B gh+B gl-(B gh+B gl-G)) with G in Err by ring;exact Err.
Qed.
