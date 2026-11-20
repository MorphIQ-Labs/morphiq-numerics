(** The table index and exact residual formation in the scalar trig fast
    path. This stage starts from the signed Q256 split's absolute-value
    words; its split and grid premises are discharged separately. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative Sterbenz IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
Require Import StageGappa ExpReduction.
Open Scope R_scope.

Definition trig_64 : f64 := b64_of_bits 0x4050000000000000%Z.
Definition trig_inv64 : f64 := b64_of_bits 0x3f90000000000000%Z.
Definition trig_shifter : f64 := b64_of_bits 0x4338000000000000%Z.

Lemma trig_sixty_four_value : B trig_64=64 /\ finite trig_64.
Proof.
  split.
  - unfold trig_64. rewrite (bits_val 0x4050000000000000 false 4503599627370496%positive 46 eq_refl).
    simpl; field.
  - exact (bits_finite 0x4050000000000000 false 4503599627370496%positive (-46) eq_refl).
Qed.

(** The low-word bound is relative to the rounded head, not the exact sum.
    The common grid excludes an unrepresentable nonzero sum at underflow. *)
Theorem trig_residual_split x l : finite x -> finite l ->
  Rabs(B x)<=/128 -> Rabs(B l)<=bpow radix2 (-53) ->
  on_grid (-320) (B x) -> on_grid (-320) (B l) ->
  let '(th,tl):=two_sum64 x l in
  finite th /\ finite tl /\ B th+B tl=B x+B l /\
  B th=rndF(B th+B tl) /\
  Rabs(B th)<=0.0078126 /\ Rabs(B th+B tl)<=0.0078126 /\
  (B th=0 \/ bpow radix2 (-320)<=Rabs(B th)) /\
  Rabs(B tl)<=bpow radix2 (-53)*Rabs(B th) /\ on_grid (-320) (B tl).
Proof.
  intros Fx Fl X L Gx Gl.
  assert (WideX:Rabs(B x)<=bpow radix2 1020).
  { apply Rle_trans with 1; [lra|change 1 with (bpow radix2 0);apply bpow_le;lia]. }
  assert (WideL:Rabs(B l)<=bpow radix2 1020).
  { eapply Rle_trans; [exact L|apply bpow_le;lia]. }
  pose proof (two_sum_ieee x l Fx Fl WideX WideL) as Sum.
  pose proof (two_sum64_ok 1 0 x l Fx Fl
    ltac:(unfold bnd;change (bpow radix2 0) with 1;rewrite Rmult_1_r;change (IZR 1) with 1;lra)
    ltac:(unfold bnd;change (bpow radix2 0) with 1;rewrite Rmult_1_r;change (IZR 1) with 1;change (bpow radix2 (-53)) with (/9007199254740992) in L;lra)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Words.
  pose proof (grid_two_sum (-320) (B x) (B l) Gx Gl) as Grids.
  destruct (two_sum64 x l) as [th tl] eqn:E. cbn zeta iota in Sum |- *.
  destruct Sum as [Fth [Ftl [Head Exact]]].
  cbn [fst snd] in Words. destruct Words as [_ [_ [Words _]]].
  rewrite <-Words in Grids. cbn [fst snd] in Grids.
  destruct Grids as [Gh Gt].
  assert (GridSum:on_grid (-320) (B x+B l)) by (apply grid_plus;assumption).
  assert (Full:Rabs(B x+B l)<=/128+bpow radix2 (-53)).
  { eapply Rle_trans; [apply Rabs_triang|lra]. }
  assert (Small:Rabs(B x+B l)<=0.0078126).
  { change (bpow radix2 (-53)) with (/9007199254740992) in Full; lra. }
  assert (Low:Rabs(B tl)<=bpow radix2 (-53)*Rabs(B th)).
  { destruct (Req_dec (B x+B l) 0) as [Zero|Nonzero].
    - assert (H0:B th=0) by (rewrite Head,Zero;apply round_0;exact _).
      assert (L0:B tl=0) by lra. rewrite H0,L0,Rabs_R0; lra.
    - assert (Normal:bpow radix2 (-1022)<=Rabs(B x+B l)).
      { apply Rle_trans with (bpow radix2 (-320)); [apply bpow_le;lia|apply grid_nonzero;assumption]. }
      pose proof (relative_error_N_FLT_round radix2 (-1074) 53 ltac:(lia) ne (B x+B l) Normal) as Error.
      change (Rabs(rndF(B x+B l)-(B x+B l))<=
        /2*bpow radix2 (-52)*Rabs(rndF(B x+B l))) in Error.
      rewrite <-Head,<-Exact in Error.
      replace (B th-(B th+B tl)) with (-B tl) in Error by ring.
      rewrite Rabs_Ropp in Error.
      change (bpow radix2 (-53)) with (/9007199254740992).
      change (bpow radix2 (-52)) with (/4503599627370496) in Error; lra. }
  assert (HeadBound:Rabs(B th)<=0.0078126).
  { pose proof (rnd_abs_err (B x+B l)) as Error. rewrite <-Head in Error.
    pose proof (Rabs_triang (B th-(B x+B l)) (B x+B l)) as Triangle.
    replace (B th-(B x+B l)+(B x+B l)) with (B th) in Triangle by ring.
    assert (Tiny:bpow radix2 (-1074)<=bpow radix2 (-53)) by (apply bpow_le;lia).
    change (bpow radix2 (-53)) with (/9007199254740992) in Full,Tiny.
    nra. }
  split; [exact Fth|]. split; [exact Ftl|]. split; [exact Exact|].
  split; [rewrite Exact;exact Head|]. split; [exact HeadBound|].
  split; [rewrite Exact;exact Small|]. split.
  - destruct (Req_dec (B th) 0) as [Zero|Nonzero]; [left;exact Zero|right;apply grid_nonzero;assumption].
  - split; assumption.
Qed.

Lemma trig_shifter_eq : trig_shifter=shifter.
Proof.
  assert (Bits:bits_of_b64 shifter=0x4338000000000000%Z) by (vm_compute; reflexivity).
  unfold trig_shifter. rewrite <-Bits. unfold b64_of_bits,bits_of_b64.
  exact (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl shifter).
Qed.

Definition trig_index_float h :=
  fsub (fadd (fmul h trig_64) trig_shifter) trig_shifter.

Lemma trig_times_64 h : finite h -> Rabs(B h)<=1 ->
  finite(fmul h trig_64) /\ B(fmul h trig_64)=B h*64.
Proof.
  intros F Bound. destruct trig_sixty_four_value as [Value Fc].
  assert (Grid:on_grid (-1074) (B h)).
  { apply grid_le with (cexp radix2 (FLT_exp emin prec) (B h)).
    - unfold cexp,FLT_exp,emin,prec; lia.
    - apply grid_fmt,B_fmt. }
  assert (Format:fmtF(B h*bpow radix2 6)).
  { apply (scaled_fmt_grid (B h) (-1074) 6); [apply B_fmt|exact Grid|lia]. }
  assert (Range:bnd 1 6 (B h*B trig_64)).
  { unfold bnd. rewrite Value,Rabs_mult. rewrite (Rabs_pos_eq 64) by lra.
    change (IZR 1) with 1. rewrite Rmult_1_l. change (bpow radix2 6) with 64. nra. }
  destruct (fmul_bnd 1 6 h trig_64 F Fc ltac:(lia) ltac:(lia)
    ltac:(apply Z.pow_gt_1;lia) ltac:(lia) Range) as [Finite [Exact _]].
  split; [exact Finite|]. rewrite Exact,Value.
  change 64 with (bpow radix2 6). apply round_generic; [exact _|exact Format].
Qed.

Theorem trig_index_value h : finite h -> 0<=B h<=0.7854 ->
  finite(trig_index_float h) /\
  B(trig_index_float h)=IZR(Znearest ne (B h*64)) /\
  (0<=Znearest ne (B h*64)<=50)%Z /\
  Rabs(B h-IZR(Znearest ne (B h*64))/64)<=/128.
Proof.
  intros F Range.
  destruct (trig_times_64 h F ltac:(rewrite Rabs_pos_eq by lra;lra)) as [F64 V64].
  assert (Wide:Rabs(B(fmul h trig_64))<=bpow radix2 50).
  { rewrite V64,Rabs_pos_eq by nra. change (bpow radix2 50) with 1125899906842624; lra. }
  pose proof (shifter_round (fmul h trig_64) F64 Wide) as Index.
  unfold trig_index_float. rewrite trig_shifter_eq. cbn zeta in Index.
  destruct Index as [Fi Vi]. rewrite V64 in Vi.
  split; [exact Fi|]. split; [exact Vi|].
  pose proof (Znearest_half ne (B h*64)) as Half.
  assert (IndexRange:(0<=Znearest ne (B h*64)<=50)%Z).
  { apply Rabs_le_inv in Half.
    assert (-1<IZR(Znearest ne (B h*64))<51) by lra.
    destruct H as [L U]. change (-1) with (IZR (-1)) in L.
    change 51 with (IZR 51) in U. apply lt_IZR in L,U; lia. }
  split; [exact IndexRange|].
  replace (B h-IZR(Znearest ne (B h*64))/64) with
    ((B h*64-IZR(Znearest ne (B h*64)))/64) by field.
  unfold Rdiv. rewrite Rabs_mult. rewrite (Rabs_pos_eq (/64)) by lra. lra.
Qed.

Lemma trig_inv64_value : B trig_inv64=/64 /\ finite trig_inv64.
Proof.
  split.
  - unfold trig_inv64.
    rewrite (bits_val 0x3f90000000000000 false 4503599627370496%positive 58 eq_refl).
    simpl (cond_Zopp false _); field.
  - exact (bits_finite 0x3f90000000000000 false 4503599627370496%positive (-58) eq_refl).
Qed.

Lemma trig_scaled_index i k : finite i -> B i=IZR k -> (0<=k<=50)%Z ->
  finite(fmul i trig_inv64) /\ B(fmul i trig_inv64)=IZR k/64.
Proof.
  intros Fi Vi K. destruct trig_inv64_value as [V F].
  assert (RealK:0<=IZR k<=50).
  { split; [change 0 with (IZR 0)|change 50 with (IZR 50)]; apply IZR_le; lia. }
  assert (G:fmtF(IZR k/64)).
  { replace (IZR k/64) with (IZR k*bpow radix2 (-6))
      by (change (bpow radix2 (-6)) with (/64); field).
    apply bnd_fmt; lia. }
  assert (Range:bnd 1 0 (B i*B trig_inv64)).
  { unfold bnd. change (bpow radix2 0) with 1;rewrite Rmult_1_r. rewrite Vi,V. change (IZR 1) with 1. apply Rabs_le; lra. }
  destruct (fmul_bnd 1 0 i trig_inv64 Fi F ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Range) as [Finite [Exact _]].
  split; [exact Finite|]. rewrite Exact,Vi,V.
  apply round_generic; [exact _|exact G].
Qed.

Lemma trig_sub_table h a k : finite h -> finite a -> B a=IZR k/64 ->
  (0<=k<=50)%Z -> Rabs(B h-IZR k/64)<=/128 ->
  finite(fsub h a) /\ B(fsub h a)=B h-IZR k/64.
Proof.
  intros Fh Fa A K Distance.
  assert (Format:fmtF(B h-B a)).
  { destruct (Z.eq_dec k 0) as [Zero|Nonzero].
    - rewrite A,Zero. replace (IZR 0/64) with 0 by (simpl;field). rewrite Rminus_0_r; apply B_fmt.
    - assert (One:1<=IZR k) by (change 1 with (IZR 1);apply IZR_le;lia).
      apply Rabs_le_inv in Distance.
      apply (sterbenz radix2 (FLT_exp emin prec) (B h) (B a) (B_fmt h) (B_fmt a)).
      rewrite A; lra. }
  assert (Range:bnd 1 0 (B h-B a)).
  { unfold bnd. change (bpow radix2 0) with 1;rewrite Rmult_1_r. rewrite A. change (IZR 1) with 1; lra. }
  destruct (fsub_bnd 1 0 h a Fh Fa ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Range) as [Finite [Exact _]].
  split; [exact Finite|]. rewrite Exact,round_generic by (try exact _;exact Format).
  rewrite A; reflexivity.
Qed.

Definition trig_table_residual h l :=
  let i:=trig_index_float h in
  (i,two_sum64 (fsub h (fmul i trig_inv64)) l).

Theorem trig_table_residual_correct h l : finite h -> finite l ->
  0<=B h<=0.7854 -> Rabs(B l)<=bpow radix2 (-53) ->
  on_grid (-320) (B h) -> on_grid (-320) (B l) ->
  let '(i,(th,tl)):=trig_table_residual h l in
  finite i /\ (0<=Znearest ne (B h*64)<=50)%Z /\
  B i=IZR(Znearest ne (B h*64)) /\
  finite th /\ finite tl /\ B th+B tl=B h+B l-B i/64 /\
  B th=rndF(B th+B tl) /\
  Rabs(B th)<=0.0078126 /\ Rabs(B th+B tl)<=0.0078126 /\
  (B th=0 \/ bpow radix2 (-320)<=Rabs(B th)) /\
  Rabs(B tl)<=bpow radix2 (-53)*Rabs(B th) /\ on_grid (-320) (B tl).
Proof.
  intros Fh Fl H L Gh Gl.
  destruct (trig_index_value h Fh H) as [Fi [Vi [K Distance]]].
  destruct (trig_scaled_index _ _ Fi Vi K) as [Fa Va].
  destruct (trig_sub_table _ _ _ Fh Fa Va K Distance) as [Fx Vx].
  assert (Gtable:on_grid (-320) (B(fmul (trig_index_float h) trig_inv64))).
  { rewrite Va. apply grid_le with (-6)%Z; [lia|].
    exists (Znearest ne (B h*64)). change (bpow radix2 (-6)) with (/64);reflexivity. }
  assert (Gx:on_grid (-320) (B(fsub h (fmul (trig_index_float h) trig_inv64)))).
  { rewrite Vx,<-Va. apply grid_minus;assumption. }
  pose proof (trig_residual_split _ _ Fx Fl ltac:(rewrite Vx;exact Distance) L Gx Gl) as Residual.
  unfold trig_table_residual.
  destruct (two_sum64 (fsub h (fmul (trig_index_float h) trig_inv64)) l) as [th tl].
  cbn zeta iota in Residual |- *.
  destruct Residual as [Fth [Ftl [Sum Rest]]].
  split;[exact Fi|]. split;[exact K|]. split;[exact Vi|].
  split;[exact Fth|]. split;[exact Ftl|]. split.
  - rewrite Sum,Vx,Vi;ring.
  - exact Rest.
Qed.
