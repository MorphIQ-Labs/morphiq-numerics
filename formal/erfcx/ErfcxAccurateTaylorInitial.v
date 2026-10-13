(** The stored center value and first Q256 Taylor coefficient. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
From Q Require Limbs.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxTaylorCoefficients
  ErfcxAccurateData ErfcxAccurateConstants ErfcxAccurateCenterModel
  ErfcxAccurateCenters ErfcxAccurateCenterBounds ErfcxAccurateTaylorStep.
Open Scope R_scope.
Definition q_c2 := constant_q c2_data.
Theorem q_c2_ok : valid q_c2 /\ Rabs(qval q_c2-2*inv_sqrt_pi)<=bpow radix2 (-255).
Proof.
  destruct(constant_q_ok _ c2_data_checked) as [Q Value]. split; [exact Q|].
  unfold q_c2. rewrite Value. cbn [c2_data fst snd].
  let m := eval vm_compute in (Limbs.v(fst c2_data)) in change (Limbs.v _) with m.
  unfold inv_sqrt_pi. bpow_num. interval with (i_prec 400).
Qed.
Definition q_taylor_first c i :=
  let p:=mul c (q_center i) in add (add p p) (neg_q q_c2).
Lemma first_error_budget c d0 dc dm da ds : Rabs c<=16 ->
  Rabs d0<=bpow radix2 (-251) -> Rabs dc<=bpow radix2 (-255) ->
  Rabs dm<=bpow radix2 (-255)*16*4 -> Rabs da<=bpow radix2 (-254)*128 ->
  Rabs ds<=bpow radix2 (-254)*512 ->
  Rabs(ds+da+2*dm+2*c*d0-dc)<=bpow radix2 (-176).
Proof.
  intros C D0 DC DM DA DS. apply Rabs_le_inv in C,D0,DC,DM,DA,DS.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.
Theorem q_taylor_first_error c i : valid c -> (i<177)%nat -> qval c=accurate_center i ->
  valid(q_taylor_first c i) /\
  Rabs(qval(q_taylor_first c i)-taylor_coefficient 1 (accurate_center i))<=bpow radix2 (-176).
Proof.
  intros C I Cv. destruct(q_center_ok i I) as [A Ae].
  destruct(accurate_center_bounds i I) as [Cr Fr].
  destruct q_c2_ok as [C2 C2e].
  assert (Am : Rabs(qval(q_center i))<=4).
  { apply Rabs_le_inv in Ae. bpow_num_all. apply Rabs_le; lra. }
  assert (C2m : Rabs(qval q_c2)<=2).
  { apply Rabs_le_inv in C2e. unfold inv_sqrt_pi in C2e. bpow_num_all.
    apply Rabs_le; split; interval with (i_prec 300). }
  assert (Cmag : Rabs(qval c)<=16) by (rewrite Cv;exact Cr).
  destruct(q_mul_magnitude c (q_center i) 16 4 C A Cmag Am) as [P [Pe Pm]].
  assert (Pm' : Rabs(qval(mul c (q_center i)))<=128) by (bpow_num_all;lra).
  destruct(q_add_magnitude _ _ _ _ P P Pm' Pm') as [PP [PPe PPm]].
  rewrite Rmax_left in PPe,PPm by lra.
  assert (PPm' : Rabs(qval(add (mul c (q_center i))(mul c (q_center i))))<=512)
    by (bpow_num_all;lra).
  destruct(neg_any q_c2 C2) as [Neg Nv].
  assert (Nm : Rabs(qval(neg_q q_c2))<=2) by (rewrite Nv,Rabs_Ropp;exact C2m).
  destruct(q_add_magnitude _ _ _ _ PP Neg PPm' Nm) as [Result [Re Rm]].
  rewrite Rmax_left in Re,Rm by lra.
  unfold q_taylor_first. split; [exact Result|]. rewrite taylor_coefficient_one. rewrite <- Cv at 1.
  set (d0:=qval(q_center i)-gaussian_erfcx(accurate_center i)) in *.
  set (dc:=qval q_c2-2*inv_sqrt_pi) in *.
  set (dm:=qval(mul c (q_center i))-qval c*qval(q_center i)) in *.
  set (da:=qval(add (mul c (q_center i))(mul c (q_center i)))-
    (qval(mul c (q_center i))+qval(mul c (q_center i)))) in *.
  set (ds:=qval(add (add (mul c (q_center i))(mul c (q_center i))) (neg_q q_c2))-
    (qval(add (mul c (q_center i))(mul c (q_center i)))+qval(neg_q q_c2))) in *.
  replace (qval(add (add (mul c (q_center i))(mul c (q_center i))) (neg_q q_c2))-
    (2*qval c*gaussian_erfcx(accurate_center i)-2*inv_sqrt_pi)) with
    (ds+da+2*dm+2*qval c*d0-dc) by (unfold ds,da,dm,d0,dc;rewrite Nv;ring).
  apply first_error_budget; assumption.
Qed.
