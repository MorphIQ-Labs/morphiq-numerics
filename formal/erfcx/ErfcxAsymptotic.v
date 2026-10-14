(** Integrating the exponential Taylor polynomial against exp(-u).
    Factorial moments turn it into the erfcx asymptotic polynomial. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import Expm1Series ErfcxExpRemainder ErfcxMoments ErfcxTailIntegral.
Open Scope R_scope.

Definition asym_coefficient k t := (-t/4)^k/INR(fact k).
Definition moment_series n t u :=
  sum_f_R0 (fun k => asym_coefficient k t*exponential_moment (2*k) u) n.
Definition asym_polynomial n t :=
  sum_f_R0 (fun k => asym_coefficient k t*INR(fact(2*k))) n.
Definition integrated_moment_series n t b :=
  sum_f_R0 (fun k => asym_coefficient k t*RInt (exponential_moment (2*k)) 0 b) n.

Lemma moment_series_integrable n t a b : ex_RInt (moment_series n t) a b.
Proof.
  induction n as [ | n IH].
  - change (ex_RInt (fun u => asym_coefficient 0 t*exponential_moment (2*0) u) a b).
    exact (@ex_RInt_scal R_NormedModule (exponential_moment (2*0)) a b (asym_coefficient 0 t)
      (exponential_moment_integrable (2*0) a b)).
  - change (ex_RInt (fun u => moment_series n t u+
      asym_coefficient (S n) t*exponential_moment (2*S n) u) a b).
    apply (@ex_RInt_plus R_NormedModule).
    + exact IH.
    + exact (@ex_RInt_scal R_NormedModule (exponential_moment (2*S n)) a b (asym_coefficient (S n) t)
        (exponential_moment_integrable (2*S n) a b)).
Qed.

Lemma moment_series_integral n t b :
  RInt (moment_series n t) 0 b=integrated_moment_series n t b.
Proof.
  induction n as [ | n IH].
  - exact (@RInt_scal R_CompleteNormedModule (exponential_moment (2*0)) 0 b (asym_coefficient 0 t)
      (exponential_moment_integrable (2*0) 0 b)).
  - change (RInt (fun u => moment_series n t u+
      asym_coefficient (S n) t*exponential_moment (2*S n) u) 0 b=
      integrated_moment_series n t b+asym_coefficient (S n) t*RInt (exponential_moment (2*S n)) 0 b).
    pose proof (@RInt_plus R_CompleteNormedModule (moment_series n t)
      (fun u => asym_coefficient (S n) t*exponential_moment (2*S n) u) 0 b
      (moment_series_integrable n t 0 b)
      (@ex_RInt_scal R_NormedModule (exponential_moment (2*S n)) 0 b (asym_coefficient (S n) t)
        (exponential_moment_integrable (2*S n) 0 b))) as Plus.
    change (RInt (fun u => moment_series n t u+
      asym_coefficient (S n) t*exponential_moment (2*S n) u) 0 b=
      RInt (moment_series n t) 0 b+RInt (fun u => asym_coefficient (S n) t*exponential_moment (2*S n) u) 0 b) in Plus.
    rewrite Plus, IH. f_equal.
    exact (@RInt_scal R_CompleteNormedModule (exponential_moment (2*S n)) 0 b (asym_coefficient (S n) t)
      (exponential_moment_integrable (2*S n) 0 b)).
Qed.

Theorem moment_series_integral_limit n t :
  is_lim_seq (fun k => integrated_moment_series n t (INR k)) (asym_polynomial n t).
Proof.
  induction n as [ | n IH].
  - change (is_lim_seq (fun k => asym_coefficient 0 t*RInt (exponential_moment (2*0)) 0 (INR k))
      (asym_coefficient 0 t*INR(fact(2*0)))).
    apply is_lim_seq_mult'; [apply is_lim_seq_const | apply exponential_moment_integral_limit].
  - change (is_lim_seq (fun k => integrated_moment_series n t (INR k)+
      asym_coefficient (S n) t*RInt (exponential_moment (2*S n)) 0 (INR k))
      (asym_polynomial n t+asym_coefficient (S n) t*INR(fact(2*S n)))).
    apply is_lim_seq_plus'; [exact IH | ].
    apply is_lim_seq_mult'; [apply is_lim_seq_const | apply exponential_moment_integral_limit].
Qed.

Lemma finite_sum_scale a f n :
  sum_f_R0 (fun k => a*f k) n=a*sum_f_R0 f n.
Proof. induction n; cbn [sum_f_R0]; [reflexivity | rewrite IHn; ring]. Qed.

Lemma moment_series_polynomial n t u :
  moment_series n t u=exp(-u)*exp_negative_polynomial n (t*u*u/4).
Proof.
  unfold moment_series, exp_negative_polynomial, esum. rewrite <- finite_sum_scale.
  apply sum_eq. intros k K. unfold asym_coefficient, exponential_moment.
  replace (-(t*u*u/4)) with ((-t/4)*(u^2)) by (simpl pow; field).
  rewrite Rpow_mult_distr, pow_mult. unfold Rdiv. ring.
Qed.

Lemma alternating_sign_square n : (-1)^n*(-1)^n=1.
Proof.
  rewrite <- Rpow_mult_distr. replace ((-1)*(-1)) with 1 by ring. apply pow1.
Qed.

Definition asym_next_coefficient n t := (t/4)^S n/INR(fact(S n)).

Lemma tail_integrand_signed_remainder n t u : 0<=t -> exists theta,
  0<=theta<=1 /\
  (-1)^S n*(tail_integrand t u-moment_series n t u)=
    theta*asym_next_coefficient n t*exponential_moment (2*S n) u.
Proof.
  intros T.
  assert (Spos : 0<=t*u*u/4) by nra.
  destruct (exp_negative_taylor_remainder n (t*u*u/4) Spos) as [theta [Theta Error]].
  exists theta. split; [exact Theta | ].
  rewrite moment_series_polynomial. unfold tail_integrand.
  replace (-t*u*u/4) with (-(t*u*u/4)) by field.
  replace ((-1)^S n*(exp(-u)*exp(-(t*u*u/4))-exp(-u)*exp_negative_polynomial n (t*u*u/4)))
    with ((-1)^S n*exp(-u)*(exp(-(t*u*u/4))-exp_negative_polynomial n (t*u*u/4))) by ring.
  rewrite Error. unfold asym_next_coefficient, exponential_moment.
  replace (t*u*u/4) with ((t/4)*(u^2)) by (simpl pow; field).
  rewrite Rpow_mult_distr, pow_mult. unfold Rdiv.
  replace ((-1)^S n*exp(-u)*((-1)^S n*theta*((t*/4)^S n*(u^2)^S n)* /INR(fact(S n))))
    with (((-1)^S n*(-1)^S n)*theta*((t*/4)^S n* /INR(fact(S n)))*((u^2)^S n*exp(-u))) by ring.
  rewrite alternating_sign_square. ring.
Qed.

Definition tail_signed_integrand n t u := (-1)^S n*(tail_integrand t u-moment_series n t u).

Lemma tail_signed_integrand_bounds n t u : 0<=t -> 0<=u ->
  0<=tail_signed_integrand n t u<=asym_next_coefficient n t*exponential_moment (2*S n) u.
Proof.
  intros T U. destruct (tail_integrand_signed_remainder n t u T) as [theta [Theta Error]].
  unfold tail_signed_integrand. rewrite Error.
  assert (A : 0<=asym_next_coefficient n t).
  { unfold asym_next_coefficient. apply Rdiv_le_0_compat.
    - apply pow_le. lra.
    - apply lt_0_INR, lt_O_fact. }
  assert (M : 0<=exponential_moment (2*S n) u).
  { unfold exponential_moment. apply Rmult_le_pos; [apply pow_le; exact U | apply Rlt_le,exp_pos]. }
  split.
  - apply Rmult_le_pos; [apply Rmult_le_pos; lra | exact M].
  - apply Rmult_le_compat_r; [exact M | ].
    replace (asym_next_coefficient n t) with (1*asym_next_coefficient n t) at 2 by ring.
    apply Rmult_le_compat_r; lra.
Qed.

Lemma tail_signed_integrand_integrable n t a b : ex_RInt (tail_signed_integrand n t) a b.
Proof.
  apply (@ex_RInt_scal R_NormedModule).
  apply (@ex_RInt_minus R_NormedModule); [apply tail_integrand_integrable | apply moment_series_integrable].
Qed.

Lemma tail_signed_integral n t b :
  RInt (tail_signed_integrand n t) 0 b=
  (-1)^S n*(RInt (tail_integrand t) 0 b-integrated_moment_series n t b).
Proof.
  assert (Difference : ex_RInt (fun u => tail_integrand t u-moment_series n t u) 0 b).
  { apply (@ex_RInt_minus R_NormedModule); [apply tail_integrand_integrable | apply moment_series_integrable]. }
  pose proof (@RInt_scal R_CompleteNormedModule
    (fun u => tail_integrand t u-moment_series n t u) 0 b ((-1)^S n) Difference) as Scale.
  pose proof (@RInt_minus R_CompleteNormedModule (tail_integrand t) (moment_series n t) 0 b
    (tail_integrand_integrable t 0 b) (moment_series_integrable n t 0 b)) as Minus.
  change (RInt (tail_signed_integrand n t) 0 b=
    (-1)^S n*RInt (fun u => tail_integrand t u-moment_series n t u) 0 b) in Scale.
  change (RInt (fun u => tail_integrand t u-moment_series n t u) 0 b=
    RInt (tail_integrand t) 0 b-RInt (moment_series n t) 0 b) in Minus.
  rewrite Scale, Minus, moment_series_integral. reflexivity.
Qed.

Lemma tail_signed_integral_bounds n t b : 0<=t -> 0<=b ->
  0<=RInt (tail_signed_integrand n t) 0 b<=
    asym_next_coefficient n t*RInt (exponential_moment (2*S n)) 0 b.
Proof.
  intros T B. split.
  - apply RInt_ge_0; [exact B | apply tail_signed_integrand_integrable | ].
    intros u U. exact (proj1 (tail_signed_integrand_bounds n t u T ltac:(lra))).
  - pose proof (@RInt_scal R_CompleteNormedModule (exponential_moment (2*S n)) 0 b
      (asym_next_coefficient n t) (exponential_moment_integrable (2*S n) 0 b)) as Scale.
    change (RInt (fun u => asym_next_coefficient n t*exponential_moment (2*S n) u) 0 b=
      asym_next_coefficient n t*RInt (exponential_moment (2*S n)) 0 b) in Scale.
    rewrite <- Scale. apply RInt_le; [exact B | apply tail_signed_integrand_integrable | | ].
    + exact (@ex_RInt_scal R_NormedModule (exponential_moment (2*S n)) 0 b
        (asym_next_coefficient n t) (exponential_moment_integrable (2*S n) 0 b)).
    + intros u U. exact (proj2 (tail_signed_integrand_bounds n t u T ltac:(lra))).
Qed.

Theorem tail_integral_asymptotic n t : 0<=t ->
  0<=(-1)^S n*(tail_integral t-asym_polynomial n t)<=
    asym_next_coefficient n t*INR(fact(2*S n)).
Proof.
  intros T. destruct (tail_integral_limit t T) as [Limit Range].
  assert (Signed : is_lim_seq (fun k => RInt (tail_signed_integrand n t) 0 (INR k))
    ((-1)^S n*(tail_integral t-asym_polynomial n t))).
  { eapply is_lim_seq_ext; [intros k; symmetry; apply tail_signed_integral | ].
    apply is_lim_seq_mult'; [apply is_lim_seq_const | ].
    apply is_lim_seq_minus'; [exact Limit | apply moment_series_integral_limit]. }
  assert (Upper : is_lim_seq (fun k => asym_next_coefficient n t*RInt (exponential_moment (2*S n)) 0 (INR k))
    (asym_next_coefficient n t*INR(fact(2*S n)))).
  { apply is_lim_seq_mult'; [apply is_lim_seq_const | apply exponential_moment_integral_limit]. }
  pose proof (is_lim_seq_le (fun _ => 0) _ 0 _
    (fun k => proj1 (tail_signed_integral_bounds n t (INR k) T (pos_INR k)))
    (is_lim_seq_const 0) Signed) as Low.
  pose proof (is_lim_seq_le _ _ _ _
    (fun k => proj2 (tail_signed_integral_bounds n t (INR k) T (pos_INR k)))
    Signed Upper) as High.
  split; assumption.
Qed.
