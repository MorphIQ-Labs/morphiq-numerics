(** Multiplying each accurate Taylor coefficient by its residual power. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxTaylorCoefficients
  ErfcxAccurateCenterModel ErfcxAccurateCenterBounds ErfcxAccurateTaylorStep
  ErfcxAccurateTaylorCoefficients ErfcxAccurateTaylorPower.
Open Scope R_scope.
Definition q_taylor_term c i h n := mul (snd(q_taylor_coefficients c i n)) (q_taylor_power h n).
Definition exact_taylor_term c h n := taylor_coefficient n c*h^n.
Theorem q_taylor_term_error c i h n : valid c -> valid h -> (i<177)%nat ->
  qval c=accurate_center i -> Rabs(qval h)<=/8 -> (n<=98)%nat ->
  valid(q_taylor_term c i h n) /\ Rabs(qval(q_taylor_term c i h n))<=bpow radix2 69 /\
  Rabs(qval(q_taylor_term c i h n)-exact_taylor_term (accurate_center i) (qval h) (S n))<=bpow radix2 (-135).
Proof.
  intros C H I Cv Hr N.
  destruct(q_taylor_coefficients_error c i n C I Cv N) as [_ [A _]].
  pose proof (proj2(q_taylor_coefficient_errors c i n C I Cv N)) as Ae.
  destruct(q_taylor_power_error h n H Hr) as [P [Pm Pe]].
  destruct(accurate_center_bounds i I) as [Cr Fr].
  assert (Exact : Rabs(taylor_coefficient (S n) (accurate_center i))<=bpow radix2 67)
    by (apply taylor_coefficient_bound;[lia|exact Cr|apply Rabs_le;lra]).
  assert (Am : Rabs(qval(snd(q_taylor_coefficients c i n)))<=bpow radix2 68).
  { replace (qval(snd(q_taylor_coefficients c i n))) with
      ((qval(snd(q_taylor_coefficients c i n))-taylor_coefficient (S n) (accurate_center i))+
        taylor_coefficient (S n) (accurate_center i)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. bpow_num_all;lra. }
  destruct(q_mul_magnitude _ _ _ _ A P Am Pm) as [Result [Error Magnitude]].
  unfold q_taylor_term. split; [exact Result|]. split.
  - eapply Rle_trans; [exact Magnitude|]. bpow_num;lra.
  - unfold exact_taylor_term.
    set (a:=qval(snd(q_taylor_coefficients c i n))) in *.
    set (p:=qval(q_taylor_power h n)) in *.
    set (ea:=taylor_coefficient (S n) (accurate_center i)) in *.
    replace (qval(mul (snd(q_taylor_coefficients c i n)) (q_taylor_power h n))-ea*(qval h)^S n) with
      ((qval(mul (snd(q_taylor_coefficients c i n)) (q_taylor_power h n))-a*p)+
        (a-ea)*p+ea*(p-(qval h)^S n)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof(Rabs_triang (qval(mul (snd(q_taylor_coefficients c i n)) (q_taylor_power h n))-a*p) ((a-ea)*p)) as Add.
    rewrite Rabs_mult in Add. rewrite Rabs_mult.
    assert (First : Rabs(a-ea)*Rabs p<=bpow radix2 (-136))
      by (eapply Rle_trans with (bpow radix2 (-136)*1);
          [apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Ae|exact Pm]|lra]).
    assert (Second : Rabs ea*Rabs(p-(qval h)^S n)<=bpow radix2 67*bpow radix2 (-255))
      by (apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Exact|exact Pe]).
    bpow_num_all;lra.
Qed.
