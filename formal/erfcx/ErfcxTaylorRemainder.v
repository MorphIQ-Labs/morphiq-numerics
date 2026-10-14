(** Taylor's theorem on a parameterized segment, including either residual
    sign, using the ODE derivative majorant. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxFactorial ErfcxGaussianTarget
  ErfcxTaylorDerivatives ErfcxTaylorBounds ErfcxTaylorLocal.
Open Scope R_scope.

Lemma taylor_affine_derivative n c h t :
  is_derive_n (fun z => gaussian_erfcx(c+h*z)) n t
    (h^n*Derive_n gaussian_erfcx n (c+h*t)).
Proof.
  eapply is_derive_n_ext with (f:=fun z => gaussian_erfcx(h*z+c)).
  - intros z. f_equal; ring.
  - replace (c+h*t) with (h*t+c) by ring.
    apply (is_derive_n_comp_scal (fun y => gaussian_erfcx(y+c))).
    + apply filter_forall. intros y [|k] K; [exact I|].
      exists (Derive_n gaussian_erfcx (S k) (y+c)).
      change (is_derive_n (fun z => gaussian_erfcx(z+c)) (S k) y (Derive_n gaussian_erfcx (S k) (y+c))).
      apply is_derive_n_comp_trans,Derive_n_correct,taylor_derivatives_exist.
    + apply is_derive_n_comp_trans,Derive_n_correct,taylor_derivatives_exist.
Qed.
Lemma taylor_affine_derive_n n c h t :
  Derive_n (fun z => gaussian_erfcx(c+h*z)) n t=
    h^n*Derive_n gaussian_erfcx n (c+h*t).
Proof. apply is_derive_n_unique,taylor_affine_derivative. Qed.
Definition taylor_polynomial n c h :=
  sum_f_R0 (fun k => h^k/INR(fact k)*Derive_n gaussian_erfcx k c) n.

Lemma taylor_segment n c h : exists t,0<t<1 /\
  gaussian_erfcx(c+h)=taylor_polynomial n c h+
    h^S n/INR(fact(S n))*Derive_n gaussian_erfcx (S n) (c+h*t).
Proof.
  destruct (Taylor_Lagrange (fun z => gaussian_erfcx(c+h*z)) n 0 1 ltac:(lra)) as [t [T E]].
  - intros z Z [|k] K; [exact I|].
    exists (h^S k*Derive_n gaussian_erfcx (S k) (c+h*z)).
    change (is_derive_n (fun y => gaussian_erfcx(c+h*y)) (S k) z (h^S k*Derive_n gaussian_erfcx (S k) (c+h*z))).
    apply taylor_affine_derivative.
  - exists t. split; [exact T|]. rewrite Rmult_1_r in E.
    rewrite taylor_affine_derive_n in E.
    assert (Sum : sum_f_R0 (fun m => (1-0)^m/INR(fact m)*
      Derive_n (fun z => gaussian_erfcx(c+h*z)) m 0) n=taylor_polynomial n c h).
    { apply sum_eq. intros k K. rewrite taylor_affine_derive_n,Rmult_0_r,Rplus_0_r.
      replace (1-0) with 1 by ring. rewrite pow1. unfold Rdiv; ring. }
    rewrite Sum in E. replace (1-0) with 1 in E by ring. rewrite pow1 in E.
    rewrite E. f_equal. unfold Rdiv; ring.
Qed.

Theorem taylor_local_remainder n c h : (n<=99)%nat -> Rabs c<=16 -> Rabs h<=/8 ->
  Rabs(gaussian_erfcx c)<=3 ->
  Rabs(gaussian_erfcx(c+h)-taylor_polynomial n c h)<=512*5^S n/INR(fact(S n)).
Proof.
  intros N C H F. destruct (taylor_segment n c h) as [t [T Error]].
  assert (Ht : Rabs(h*t)<=/8).
  { rewrite Rabs_mult. pose proof(Rabs_pos h). rewrite (Rabs_right t) by lra. nra. }
  assert (X : Rabs(c+h*t)<=17).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  pose proof (taylor_derivative_bound (S n) (c+h*t) ltac:(lia) X (gaussian_local_bound c (h*t) C Ht F)) as D.
  rewrite Error. replace (taylor_polynomial n c h+
    h^S n/INR(fact(S n))*Derive_n gaussian_erfcx (S n) (c+h*t)-taylor_polynomial n c h) with
    (h^S n/INR(fact(S n))*Derive_n gaussian_erfcx (S n) (c+h*t)) by ring.
  assert (Fact : 0<INR(fact(S n))) by (apply lt_0_INR,lt_O_fact).
  unfold Rdiv. rewrite !Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(INR(fact(S n)))) by lra.
  rewrite <- RPow_abs.
  eapply Rle_trans with (Rabs h^S n*/INR(fact(S n))*(512*40^S n)).
  - apply Rmult_le_compat_l; [apply Rmult_le_pos; [apply pow_le,Rabs_pos|apply Rlt_le,Rinv_0_lt_compat;exact Fact]|exact D].
  - replace (Rabs h^S n*/INR(fact(S n))*(512*40^S n)) with
      (512*((Rabs h*40)^S n)*/INR(fact(S n))) by (rewrite Rpow_mult_distr; ring).
    apply Rmult_le_compat_r; [apply Rlt_le,Rinv_0_lt_compat;exact Fact|].
    apply Rmult_le_compat_l; [lra|]. apply pow_incr. pose proof(Rabs_pos h); nra.
Qed.

Theorem taylor_cap_remainder c h : Rabs c<=16 -> Rabs h<=/8 ->
  Rabs(gaussian_erfcx c)<=3 ->
  Rabs(gaussian_erfcx(c+h)-taylor_polynomial 99 c h)<=bpow radix2 (-280).
Proof.
  intros C H F. eapply Rle_trans; [apply (taylor_local_remainder 99 c h ltac:(lia) C H F)|].
  binary_factorials. bpow_num. interval with (i_prec 400).
Qed.

Require Import ErfcxAccurateCenterModel ErfcxAccurateCenterBounds.
Theorem table_taylor_cap_remainder i h : (i<177)%nat -> Rabs h<=/8 ->
  Rabs(gaussian_erfcx(accurate_center i+h)-taylor_polynomial 99 (accurate_center i) h)<=bpow radix2 (-280).
Proof.
  intros I H. destruct (accurate_center_bounds i I) as [C F].
  apply taylor_cap_remainder; [exact C|exact H|]. apply Rabs_le; lra.
Qed.
