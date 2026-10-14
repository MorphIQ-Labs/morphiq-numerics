(** A derivative majorant for every local Taylor interval. The hypotheses
    state the function range separately from the ODE calculation. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
Require Import ErfcxConstants ErfcxGaussianTarget ErfcxTaylorDerivatives.
Open Scope R_scope.

Theorem taylor_derivatives_bound n x : (n<=99)%nat -> Rabs x<=17 ->
  Rabs(gaussian_erfcx x)<=512 ->
  Rabs(fst(taylor_derivatives n x))<=512*40^n /\
  Rabs(snd(taylor_derivatives n x))<=512*40^S n.
Proof.
  intros N X F. induction n as [|n IH].
  - cbn [taylor_derivatives fst snd pow]. split; [lra|].
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_Ropp,!Rabs_mult,(Rabs_pos_eq 2) by lra.
    assert (C : Rabs inv_sqrt_pi<=1) by (unfold inv_sqrt_pi; interval with (i_prec 80)).
    pose proof (Rabs_pos x); pose proof (Rabs_pos(gaussian_erfcx x)); pose proof(Rabs_pos inv_sqrt_pi).
    nra.
  - destruct (IH ltac:(lia)) as [Prev Cur].
    cbn [taylor_derivatives]. destruct (taylor_derivatives n x) as [prev cur] eqn:Pair.
    cbn [fst snd] in Prev,Cur |- *. split; [exact Cur|].
    eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult.
    rewrite (Rabs_pos_eq 2),(Rabs_pos_eq(INR(S n))) by (try lra; apply pos_INR).
    assert (I : INR(S n)<=100) by (replace 100 with (INR 100) by (rewrite INR_IZR_INZ; reflexivity); apply le_INR; lia).
    assert (P : 0<=40^n) by (apply pow_le; lra).
    assert (Term1 : 2*Rabs x*Rabs cur<=34*(512*40^S n)).
    { apply Rmult_le_compat; [pose proof(Rabs_pos x);lra|apply Rabs_pos|lra|exact Cur]. }
    assert (Term2 : 2*INR(S n)*Rabs prev<=200*(512*40^n)).
    { apply Rmult_le_compat; [pose proof(pos_INR(S n));lra|apply Rabs_pos|lra|exact Prev]. }
    cbn [pow] in Cur,Term1 |- *. nra.
Qed.

Theorem taylor_derivative_bound n x : (n<=100)%nat -> Rabs x<=17 ->
  Rabs(gaussian_erfcx x)<=512 -> Rabs(Derive_n gaussian_erfcx n x)<=512*40^n.
Proof.
  intros N X F. rewrite taylor_derivative_n. destruct n as [|n].
  - cbn [taylor_derivatives fst pow]; lra.
  - rewrite taylor_derivative_next. exact (proj2(taylor_derivatives_bound n x ltac:(lia) X F)).
Qed.
