(** Q256-to-double-word splitting for the trig fast path. The grid bound
    follows the actual limb addition, including cancellation and zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Q Require Import QSpec Q256 Q256Real Limbs Shifts LimbScan.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid RoundingCore.
Require Import ErfcxAccurateInputs.
From Interval Require Import Tactic.
Open Scope R_scope.

Lemma trig_q_grid q g : (g<=Q256.e q)%Z -> on_grid g (qval q).
Proof.
  intros E. apply grid_le with (Q256.e q); [exact E|].
  unfold qval,val,F2R; cbn [Fnum Fexp].
  exists (if neg q then (-v(m q))%Z else v(m q)); reflexivity.
Qed.

Lemma trig_q_small_conversion q : valid q -> Rabs(qval q)<=1 ->
  finite(Q256.to_f64 q) /\ B(Q256.to_f64 q)=rndF(qval q).
Proof.
  intros V Bound. apply q_to_float_round; [exact V|].
  apply Rle_lt_trans with 1.
  - apply abs_round_le_generic; [exact _|exact _|replace 1 with (IZR 1*bpow radix2 0) by (simpl;ring);apply bnd_fmt;lia|exact Bound].
  - change 1 with (bpow radix2 0);apply bpow_lt;lia.
Qed.

Definition trig_q_split r :=
  let h:=Q256.to_f64 r in
  (h,Q256.to_f64(Q256.add r (q_float(fneg h)))).

Lemma trig_q_exponent q g : valid q -> bpow radix2 g<=Rabs(qval q) ->
  (g-255<=Q256.e q)%Z.
Proof.
  intros [O [Zero|Normal]] Lower.
  - rewrite (qval_zero q Zero),Rabs_R0 in Lower.
    pose proof (bpow_gt_0 radix2 g); lra.
  - pose proof (mag_bounds q Normal) as [_ Upper].
    rewrite (mag_abs q O) in Upper.
    assert (Pow:bpow radix2 g<bpow radix2 (Q256.e q+256)) by lra.
    destruct (Z_le_gt_dec (g-255) (Q256.e q)); [assumption|].
    assert (Back:bpow radix2 (Q256.e q+256)<=bpow radix2 g) by (apply bpow_le;lia). lra.
Qed.

Lemma trig_q_ordered_grid big small g : valid big -> valid small ->
  normalized 256 (v(m big)) -> normalized 256 (v(m small)) ->
  Q256.mag small<=Q256.mag big -> (g<=Q256.e big)%Z ->
  on_grid g (qval(add_ordered big small)).
Proof.
  intros [Ob Nb] [Os Ns] Big Small Order Grid.
  assert (Exponents:(Q256.e small<=Q256.e big)%Z).
  { destruct (Z_le_gt_dec (Q256.e small) (Q256.e big)); [assumption|].
    pose proof (mag_bounds big Big) as [_ U].
    pose proof (mag_bounds small Small) as [L _].
    assert (P:bpow radix2 (Q256.e big+256)<=bpow radix2 (Q256.e small+255))
      by (apply bpow_le;lia). lra. }
  unfold add_ordered. cbn zeta.
  destruct (Bool.eqb (neg big) (neg small)).
  - destruct (add_limbs (m big) (shr (m small) (Q256.e big-Q256.e small))) as [sum carry].
    destruct carry; apply trig_q_grid; cbn [Q256.e];lia.
  - assert (Shift:ok4(shr (m small) (Q256.e big-Q256.e small))).
    { destruct (shr_ok (m small) (Q256.e big-Q256.e small) (proj1 Os) (proj2 Os) ltac:(lia)) as [_ [O L]].
      split; assumption. }
    assert (Sub:ok4(sub_limbs (m big) (shr (m small) (Q256.e big-Q256.e small)))).
    { unfold sub_limbs.
      pose proof (sub_chain_ok (m big) _ 0 ltac:(rewrite (proj2 Ob),(proj2 Shift);reflexivity)
        (proj1 Ob) (proj1 Shift) ltac:(lia)) as S.
      destruct (sub_chain (m big) (shr (m small) (Q256.e big-Q256.e small)) 0) as [out borrow].
      cbn [fst]. destruct S as [_ [O [_ L]]]. split; [exact O|rewrite L;exact (proj2 Ob)]. }
    rewrite new_val by exact Sub. apply grid_le with (Q256.e big); [exact Grid|].
    unfold val,F2R; cbn [Fnum Fexp].
    eexists; reflexivity.
Qed.

Theorem trig_q_add_grid a b g : valid a -> valid b ->
  (g<=Q256.e a)%Z -> (g<=Q256.e b)%Z -> on_grid g (qval(Q256.add a b)).
Proof.
  intros Va Vb Ea Eb. destruct Va as [Oa Na],Vb as [Ob Nb].
  unfold Q256.add. rewrite !is_zero_ok by (apply Oa || apply Ob).
  destruct (Z.eqb_spec (v(m a)) 0) as [Za|Za].
  - apply trig_q_grid;exact Eb.
  - destruct (Z.eqb_spec (v(m b)) 0) as [Zb|Zb].
    + apply trig_q_grid;exact Ea.
    + destruct Na as [Na|Na]; [contradiction|].
      destruct Nb as [Nb|Nb]; [contradiction|].
      pose proof (cmp_abs_ok a b Oa Ob Na Nb) as Order.
      destruct (cmp_abs a b); apply trig_q_ordered_grid;
        try (split;[assumption|right;assumption]);try assumption;lra.
Qed.

Theorem trig_q_split_correct r : valid r ->
  bpow radix2 (-64)<=Rabs(qval r)<=0.785399 ->
  let '(h,l):=trig_q_split r in
  finite h /\ finite l /\
  bpow radix2 (-65)<=Rabs(B h)<=0.7854 /\
  Rabs(B l)<=bpow radix2 (-53) /\
  on_grid (-320) (B h) /\ on_grid (-320) (B l) /\
  Rabs(B h+B l-qval r)<=bpow radix2 (-104)*Rabs(qval r).
Proof.
  intros V [Lower Upper]. unfold trig_q_split; cbn zeta.
  set (h:=Q256.to_f64 r).
  destruct (trig_q_small_conversion r V ltac:(lra)) as [Fh Head]. fold h in Fh,Head.
  assert (Normal:bpow radix2 (-1022)<=Rabs(qval r)).
  { eapply Rle_trans;[|exact Lower];apply bpow_le;lia. }
  pose proof (rnd_rel _ Normal) as HE. change (RNE(qval r)) with (rndF(qval r)) in HE.
  rewrite <-Head in HE.
  assert (Hupper:Rabs(B h)<=0.7854).
  { pose proof (Rabs_triang (B h-qval r) (qval r)) as T.
    replace (B h-qval r+qval r) with (B h) in T by ring.
    change (bpow radix2 (-53)) with (/9007199254740992) in HE. lra. }
  assert (Hlower:bpow radix2 (-65)<=Rabs(B h)).
  { pose proof (Rabs_triang (qval r-B h) (B h)) as T.
    replace (qval r-B h+B h) with (qval r) in T by ring.
    rewrite Rabs_minus_sym in T.
    change (bpow radix2 (-53)) with (/9007199254740992) in HE.
    change (bpow radix2 (-64)) with (/18446744073709551616) in Lower.
    change (bpow radix2 (-65)) with (/36893488147419103232). lra. }
  assert (Gh:on_grid (-320) (B h)).
  { apply grid_le with (-117)%Z; [lia|].
    apply (grid_fmt_bound (FLT_exp emin prec) (-65));
      [intros e;unfold FLT_exp,prec;lia|apply B_fmt|right;exact Hlower]. }
  assert (Fneg:finite(fneg h)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fh).
  assert (Neg:B(fneg h) = -B h) by apply B2R_Bopp.
  destruct (q_float_ok (fneg h) Fneg) as [Vneg Nvalue]. rewrite Neg in Nvalue.
  set (d:=Q256.add r (q_float(fneg h))).
  destruct (add_any r _ V Vneg) as [Vd DE]. fold d in Vd,DE. rewrite Nvalue in DE.
  replace (qval r+-B h) with (qval r-B h) in DE by ring.
  rewrite Rabs_Ropp in DE.
  assert (Max:Rmax(Rabs(qval r)) (Rabs(B h))<=2*Rabs(qval r)).
  { apply Rmax_case;[pose proof (Rabs_pos(qval r));lra|].
    pose proof (Rabs_triang (B h-qval r) (qval r)) as T.
    replace (B h-qval r+qval r) with (B h) in T by ring.
    change (bpow radix2 (-53)) with (/9007199254740992) in HE. pose proof (Rabs_pos(qval r)); lra. }
  assert (DEsmall:Rabs(qval d-(qval r-B h))<=bpow radix2 (-253)*Rabs(qval r)).
  { eapply Rle_trans;[exact DE|].
    replace (bpow radix2 (-253)) with (bpow radix2 (-254)*2)
      by (replace (-253)%Z with (-254+1)%Z by lia;rewrite bpow_plus;reflexivity).
    rewrite Rmult_assoc. apply Rmult_le_compat_l;[apply bpow_ge_0|exact Max]. }
  assert (Dsize:Rabs(qval d)<=(bpow radix2 (-53)+bpow radix2 (-253))*Rabs(qval r)).
  { pose proof (Rabs_triang (qval d-(qval r-B h)) (qval r-B h)) as T.
    replace (qval d-(qval r-B h)+(qval r-B h)) with (qval d) in T by ring.
    rewrite (Rabs_minus_sym (qval r) (B h)) in T. nra. }
  assert (Dsmall:Rabs(qval d)<=1).
  { assert (Budget:0<=bpow radix2 (-53)+bpow radix2 (-253)<=/2) by interval.
    nra. }
  assert (Er:(-320<=Q256.e r)%Z).
  { pose proof (trig_q_exponent r (-64) V Lower);lia. }
  assert (En:(-320<=Q256.e(q_float(fneg h)))%Z).
  { assert (L:bpow radix2 (-65)<=Rabs(qval(q_float(fneg h))))
      by (rewrite Nvalue,Rabs_Ropp;exact Hlower).
    pose proof (trig_q_exponent _ (-65) Vneg L);lia. }
  assert (Gd:on_grid (-320) (qval d)) by (apply trig_q_add_grid;assumption).
  destruct (trig_q_small_conversion d Vd Dsmall) as [Fl Low].
  assert (LE:Rabs(B(Q256.to_f64 d)-qval d)<=bpow radix2 (-53)*Rabs(qval d)).
  { rewrite Low. destruct (Req_dec (qval d) 0) as [Zero|Nonzero].
    - rewrite Zero,round_0 by exact _. rewrite Rminus_0_r,Rabs_R0,Rmult_0_r;lra.
    - apply rnd_rel. apply Rle_trans with (bpow radix2 (-320));
        [apply bpow_le;lia|apply grid_nonzero;assumption]. }
  assert (LowBound:Rabs(B(Q256.to_f64 d))<=bpow radix2 (-53)).
  { pose proof (Rabs_triang (B(Q256.to_f64 d)-qval d) (qval d)) as T.
    replace (B(Q256.to_f64 d)-qval d+qval d) with (B(Q256.to_f64 d)) in T by ring.
    assert (Budget:(1+bpow radix2 (-53))*(bpow radix2 (-53)+bpow radix2 (-253))*0.785399<=bpow radix2 (-53)) by interval.
    assert (P:0<=1+bpow radix2 (-53)) by (pose proof (bpow_gt_0 radix2 (-53));lra).
    assert (Q:0<=bpow radix2 (-53)+bpow radix2 (-253)) by (pose proof (bpow_gt_0 radix2 (-53));pose proof (bpow_gt_0 radix2 (-253));lra).
    assert (A:Rabs(B(Q256.to_f64 d))<=(1+bpow radix2 (-53))*Rabs(qval d)) by nra.
    eapply Rle_trans;[exact A|]. eapply Rle_trans;[apply Rmult_le_compat_l;[exact P|exact Dsize]|].
    rewrite <-Rmult_assoc. eapply Rle_trans;[apply Rmult_le_compat_l;[apply Rmult_le_pos;assumption|exact Upper]|exact Budget]. }
  assert (Error:Rabs(B h+B(Q256.to_f64 d)-qval r)<=bpow radix2 (-104)*Rabs(qval r)).
  { replace (B h+B(Q256.to_f64 d)-qval r) with
      ((B(Q256.to_f64 d)-qval d)+(qval d-(qval r-B h))) by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert (Budget:bpow radix2 (-53)*(bpow radix2 (-53)+bpow radix2 (-253))+bpow radix2 (-253)<=bpow radix2 (-104)) by interval.
    assert (A:bpow radix2 (-53)*Rabs(qval d)<=bpow radix2 (-53)*(bpow radix2 (-53)+bpow radix2 (-253))*Rabs(qval r)).
    { rewrite Rmult_assoc;apply Rmult_le_compat_l;[apply bpow_ge_0|exact Dsize]. }
    eapply Rle_trans with ((bpow radix2 (-53)*(bpow radix2 (-53)+bpow radix2 (-253))+bpow radix2 (-253))*Rabs(qval r));
      [nra|apply Rmult_le_compat_r;[apply Rabs_pos|exact Budget]]. }
  split;[exact Fh|]. split;[exact Fl|]. split;[split;assumption|].
  split;[exact LowBound|]. split;[exact Gh|]. split.
  - rewrite Low;apply grid_round;auto with typeclass_instances.
  - exact Error.
Qed.
