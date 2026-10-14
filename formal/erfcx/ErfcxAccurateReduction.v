(** Q256 reduction of the exact double-word square for negative erfcx. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxAccurateTranscendentals.
Require ExpReduction.
Open Scope R_scope.

Definition accurate_n s := fsub (fadd (fmul s ExpReduction.c_inv_l) ExpReduction.shifter) ExpReduction.shifter.
Definition accurate_residual s se n :=
  add (add (q_float s) (q_float se)) (neg_q (mul (q_float n) q_logstep)).

Lemma accurate_n_ieee s : finite s -> -745.1333<=B s<=709.79 ->
  finite (accurate_n s) /\ exists ni : Z,
    B (accurate_n s)=IZR ni /\ (Z.abs ni<=137601)%Z /\
    Rabs (B s-IZR ni*(ln 2/128))<=0.002708.
Proof.
  intros F S.
  assert (L : 0.0054152123<=ln 2/128<=0.0054152124) by (split; interval with (i_prec 100)).
  assert (Inv : Rabs (B ExpReduction.c_inv_l-/(ln 2/128))<=bpow radix2 (-40)).
  { rewrite ExpReduction.c_inv_l_val. bpow_num. interval with (i_prec 100). }
  destruct (ExpReduction.reduce_n (ln 2/128) L Inv s F ltac:(lra)) as [N [ni [Value [Ni Error]]]].
  split; [exact N | ]. exists ni. split; [exact Value | ]. split; [exact Ni | ].
  replace (B s-IZR ni*(ln 2/128)) with ((B s/(ln 2/128)-IZR ni)*(ln 2/128)) by (field; lra).
  rewrite Rabs_mult,(Rabs_pos_eq (ln 2/128)) by lra.
  eapply Rle_trans with ((/2+/1000000000)*0.0054152124); [ | lra].
  apply Rmult_le_compat; try apply Rabs_pos; lra.
Qed.

Theorem accurate_residual_error s se n ni : finite s -> finite se -> finite n ->
  Rabs (B s)<=746 -> Rabs (B se)<=bpow radix2 (-44) ->
  B n=IZR ni -> (Z.abs ni<=137601)%Z ->
  valid (accurate_residual s se n) /\
  Rabs (qval (accurate_residual s se n)-(B s+B se-IZR ni*(ln 2/128)))<=bpow radix2 (-241).
Proof.
  intros Fs Fse Fn S Se N Ni.
  destruct (q_float_ok s Fs) as [Qs Vs]. destruct (q_float_ok se Fse) as [Qse Vse].
  destruct (q_float_ok n Fn) as [Qn Vn]. rewrite N in Vn.
  destruct q_logstep_ok as [L Le].
  assert (Ln : Rabs (qval q_logstep)<=0.006).
  { apply Rabs_le_inv in Le. assert (0.005<ln 2/128<0.0055) by (split; interval with (i_prec 80)).
    apply Rabs_le. bpow_num_all. lra. }
  assert (Nabs : Rabs (IZR ni)<=137601) by (rewrite Rabs_Zabs; apply IZR_le; exact Ni).
  destruct (add_any _ _ Qs Qse) as [A Ae]. rewrite Vs,Vse in Ae.
  assert (Aerror : Rabs (qval (add (q_float s) (q_float se))-(B s+B se))<=746*bpow radix2 (-254)).
  { eapply Rle_trans; [exact Ae | ]. replace (746*bpow radix2 (-254)) with (bpow radix2 (-254)*746) by ring.
    apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rmax_lub; [exact S | bpow_num_all; lra]]. }
  assert (Arange : Rabs (qval (add (q_float s) (q_float se)))<=747).
  { apply Rabs_le_inv in Aerror,S,Se. apply Rabs_le. bpow_num_all. lra. }
  destruct (mul_any _ _ Qn L) as [P Pe]. rewrite Vn in Pe.
  assert (Perror : Rabs (qval (mul (q_float n) q_logstep)-IZR ni*(ln 2/128))<=
    137601*0.006*bpow radix2 (-255)+137601*bpow radix2 (-263)).
  { replace (qval (mul (q_float n) q_logstep)-IZR ni*(ln 2/128)) with
      ((qval (mul (q_float n) q_logstep)-IZR ni*qval q_logstep)+IZR ni*(qval q_logstep-ln 2/128)) by ring.
    eapply Rle_trans; [apply Rabs_triang | ]. apply Rplus_le_compat.
    - eapply Rle_trans; [exact Pe | ]. rewrite Rabs_mult.
      replace (137601*0.006*bpow radix2 (-255)) with (bpow radix2 (-255)*(137601*0.006)) by ring.
      apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rmult_le_compat; try apply Rabs_pos; assumption].
    - rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Prange : Rabs (qval (mul (q_float n) q_logstep))<=827).
  { assert (Product : Rabs (IZR ni*qval q_logstep)<=137601*0.006).
    { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
    eapply Rle_trans with (Rabs (qval (mul (q_float n) q_logstep)-IZR ni*qval q_logstep)+Rabs (IZR ni*qval q_logstep)).
    - replace (qval (mul (q_float n) q_logstep)) with
        ((qval (mul (q_float n) q_logstep)-IZR ni*qval q_logstep)+IZR ni*qval q_logstep) at 1 by ring.
      apply Rabs_triang.
    - assert (Bound : Rabs (qval (mul (q_float n) q_logstep)-IZR ni*qval q_logstep)<=bpow radix2 (-255)*(137601*0.006)).
      { eapply Rle_trans; [exact Pe | ]. apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Product]. }
      bpow_num_all. lra. }
  destruct (neg_any _ P) as [Neg Negvalue].
  destruct (add_any _ _ A Neg) as [Result Error]. rewrite Negvalue,Rabs_Ropp in Error.
  assert (FinalError : Rabs (qval (accurate_residual s se n)-
    (qval (add (q_float s) (q_float se))-qval (mul (q_float n) q_logstep)))<=827*bpow radix2 (-254)).
  { eapply Rle_trans; [exact Error | ]. replace (827*bpow radix2 (-254)) with (bpow radix2 (-254)*827) by ring.
    apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rmax_lub; lra]. }
  split; [exact Result | ].
  apply Rabs_le_inv in Aerror,Perror,FinalError. apply Rabs_le. bpow_num_all. split; lra.
Qed.
