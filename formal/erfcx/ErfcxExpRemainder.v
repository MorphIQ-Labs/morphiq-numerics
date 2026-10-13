(** The signed Taylor remainder for exp(-s), the pointwise ingredient of
    the erfcx positive-tail asymptotic bound. Reuses the shared exponential
    segment theorem instead of a separate Taylor/derivative development. *)
From Coq Require Import Reals Lia Lra Psatz.
Require Import Expm1Series.
Open Scope R_scope.

Definition exp_negative_polynomial n s := esum n (-s).

Theorem exp_negative_taylor_remainder n s : 0<=s -> exists theta,
  0<=theta<=1 /\
  exp (-s)-exp_negative_polynomial n s = (-1)^S n*theta*s^S n/INR(fact(S n)).
Proof.
  intros Nonnegative. destruct (exp_taylor_segment n (-s)) as [t [T Value]].
  exists (exp (-s*t)). split.
  - split; [apply Rlt_le, exp_pos | ].
    assert (Neg : -s*t<=0) by nra.
    destruct (Rle_lt_or_eq_dec _ _ Neg) as [Strict | Zero].
    + apply Rlt_le. rewrite <- exp_0. apply exp_increasing. exact Strict.
    + rewrite Zero, exp_0. lra.
  - unfold exp_negative_polynomial. rewrite Value.
    replace ((-s)^S n) with (((-1)*s)^S n) by (f_equal; ring).
    rewrite Rpow_mult_distr. unfold Rdiv. ring.
Qed.
