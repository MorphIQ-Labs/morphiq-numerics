(** The ODE recurrence gives every derivative used by Taylor's theorem. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxGaussianTarget.
Open Scope R_scope.

Fixpoint taylor_derivatives n x : R*R :=
  match n with
  | O => (gaussian_erfcx x,2*x*gaussian_erfcx x-2*inv_sqrt_pi)
  | S k => let '(prev,cur):=taylor_derivatives k x in
      (cur,2*x*cur+2*INR(S k)*prev)
  end.

Lemma derive_ode_step (f g : R -> R) (x df dg a : R) : is_derive f x df -> is_derive g x dg ->
  is_derive (fun y => 2*y*f y+a*g y) x (2*f x+2*x*df+a*dg).
Proof.
  intros F G. auto_derive.
  - split; [exists df; exact F|]. split; [exists dg; exact G|exact I].
  - change (2*1*f x+2*x*(1*Derive f x)+a*(1*Derive g x)=2*f x+2*x*df+a*dg).
    rewrite (is_derive_unique f x df F),(is_derive_unique g x dg G). ring.
Qed.

Theorem taylor_derivatives_correct n x :
  is_derive (fun y => fst(taylor_derivatives n y)) x (snd(taylor_derivatives n x)) /\
  is_derive (fun y => snd(taylor_derivatives n y)) x
    (2*x*snd(taylor_derivatives n x)+2*INR(S n)*fst(taylor_derivatives n x)).
Proof.
  induction n as [|n [Prev Cur]].
  - split.
    + apply gaussian_erfcx_derivative.
    + cbn [taylor_derivatives fst snd].
      pose proof (derive_ode_step gaussian_erfcx (fun _ => 2*inv_sqrt_pi) x
        (2*x*gaussian_erfcx x-2*inv_sqrt_pi) 0 (-1)
        (gaussian_erfcx_derivative x) (is_derive_const _ x)) as Step.
      change (INR 1) with 1.
      replace (2*x*(2*x*gaussian_erfcx x-2*inv_sqrt_pi)+2*1*gaussian_erfcx x) with
        (2*gaussian_erfcx x+2*x*(2*x*gaussian_erfcx x-2*inv_sqrt_pi)+(-1)*0) by ring.
      eapply is_derive_ext; [|exact Step]. intros y. cbn. ring.
  - assert (First : forall y, fst(taylor_derivatives (S n) y)=snd(taylor_derivatives n y)).
    { intros y. cbn [taylor_derivatives]. destruct (taylor_derivatives n y); reflexivity. }
    assert (Second : forall y, snd(taylor_derivatives (S n) y)=
      2*y*snd(taylor_derivatives n y)+2*INR(S n)*fst(taylor_derivatives n y)).
    { intros y. cbn [taylor_derivatives]. destruct (taylor_derivatives n y); reflexivity. }
    split.
    + rewrite Second. eapply is_derive_ext; [|exact Cur]. intros y. symmetry; apply First.
    + rewrite Second,First.
      pose proof (derive_ode_step _ _ x _ _ (2*INR(S n)) Cur Prev) as Step.
      rewrite (S_INR (S n)).
      replace (2*x*(2*x*snd(taylor_derivatives n x)+2*INR(S n)*fst(taylor_derivatives n x))+
        2*(INR(S n)+1)*snd(taylor_derivatives n x)) with
        (2*snd(taylor_derivatives n x)+2*x*(2*x*snd(taylor_derivatives n x)+
          2*INR(S n)*fst(taylor_derivatives n x))+2*INR(S n)*snd(taylor_derivatives n x)) by ring.
      eapply is_derive_ext; [|exact Step]. intros y. symmetry; apply Second.
Qed.

Lemma taylor_derivative_next n x :
  fst(taylor_derivatives (S n) x)=snd(taylor_derivatives n x).
Proof. cbn [taylor_derivatives]. destruct (taylor_derivatives n x); reflexivity. Qed.

Theorem taylor_derivative_n n x :
  Derive_n gaussian_erfcx n x=fst(taylor_derivatives n x).
Proof.
  revert x. induction n as [|n IH]; intros x; [reflexivity|].
  change (Derive (fun y => Derive_n gaussian_erfcx n y) x=fst(taylor_derivatives (S n) x)).
  transitivity (Derive (fun y => fst(taylor_derivatives n y)) x).
  - apply Derive_ext. exact IH.
  - transitivity (snd(taylor_derivatives n x)).
    + apply is_derive_unique. exact (proj1(taylor_derivatives_correct n x)).
    + symmetry; apply taylor_derivative_next.
Qed.

Theorem taylor_derivatives_exist n x : ex_derive_n gaussian_erfcx n x.
Proof.
  destruct n as [|n]; [exact I|].
  change (ex_derive (fun y => Derive_n gaussian_erfcx n y) x).
  exists (snd(taylor_derivatives n x)). eapply is_derive_ext.
  - intros y. symmetry; apply taylor_derivative_n.
  - exact (proj1(taylor_derivatives_correct n x)).
Qed.
