(** exp2's fallback fast kernel and its decision, including normal scaling. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingTest.
Require Import ExpFast Exp2FallbackReduction Exp2FallbackProduct Exp2Range Ln1pLemmas.
Open Scope R_scope.
Definition exp2_fast_value d j :=
 let '(rh,rl) := exp2_dwproduct d in fast_at rh rl j.
Definition exp2_fallback_fast x :=
 let '(_,j,k,d) := exp2_fallback_reduce x in
 if (-1021 <=? k)%Z then
 let '(yh,yl) := exp2_fast_value d (Z.to_nat j) in decide_scaled yh yl c_eps k
 else None.

Lemma exp2_fast_value_ok d j : finite d -> Rabs (B d) <= bpow radix2 (-8) ->
 (B d = 0 \/ bpow radix2 (-60) <= Rabs (B d)) -> (j < 128)%nat ->
 let Z := exp (INR j * ln 2 / 128) * exp (B d * ln 2) in
 let '(yh,yl) := exp2_fast_value d j in
 finite yh /\ finite yl /\ B yh = rndF (B yh + B yl) /\ 3/4 <= B yh <= 4 /\
 Rabs (Z - (B yh + B yl)) <= / 2 ^ 69 * Rabs Z.
Proof.
 intros Fd D Dlo J Z. pose proof (exp2_dwproduct_ok d Fd D Dlo) as P.
 unfold exp2_fast_value. revert P. generalize (exp2_dwproduct d).
 intros [rh rl] [Fh [Fl [Dw [Gh [Gl E]]]]].
 apply fast_reduced_ok; try assumption.
 rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-8) * Rabs (ln 2)).
 - apply Rmult_le_compat_r; [apply Rabs_pos | exact D].
 - bpow_num. interval with (i_prec 100).
Qed.

Theorem exp2_fallback_fast_ok x v : finite x ->
 bpow radix2 (-55) <= Rabs (B x) -> -1075 < B x < 1024 ->
 exp2_fallback_fast x = Some v -> finite v /\ B v = rndF (exp (B x * ln 2)).
Proof.
 intros Fx Xlo X.
 assert (Xa : Rabs (B x) <= 1075) by (apply Rabs_le; lra).
 pose proof (exp2_fallback_reduce_ok x Fx Xlo Xa) as RD.
 unfold exp2_fallback_fast. revert RD. generalize (exp2_fallback_reduce x).
 intros [[[n j] k] d] [ni [Fn [Bn [Ni [JK [J [K [Fd [Bd [D Dlo]]]]]]]]]].
 destruct (-1021 <=? k)%Z eqn:Kl; [apply Z.leb_le in Kl | discriminate].
 assert (Jn : (Z.to_nat j < 128)%nat) by lia.
 pose proof (exp2_fast_value_ok d (Z.to_nat j) Fd D Dlo Jn) as FV.
 cbv zeta in FV. revert FV. generalize (exp2_fast_value d (Z.to_nat j)).
 intros [yh yl] [Fh [Fl [Dw [Hy E]]]] Decide.
 set (z := exp (INR (Z.to_nat j) * ln 2 / 128) * exp (B d * ln 2)) in *.
 assert (Split : exp (B x * ln 2) = z * bpow radix2 k).
 { unfold z. rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia.
   rewrite <- JK, Bd. field. }
 assert (Ku : (k <= 1024)%Z).
 { assert (Nup : IZR ni < 131073).
   { apply Rabs_le_inv in D. bpow_num_in D. lra. }
   apply lt_IZR in Nup. lia. }
 assert (Zlo : 0.99 <= z).
 { assert (T : 1 <= exp (INR (Z.to_nat j) * ln 2 / 128)).
   { assert (0 <= INR (Z.to_nat j)) by apply pos_INR.
     assert (0 < ln 2) by interval with (i_prec 64).
     pose proof (exp_ineq1_le (INR (Z.to_nat j) * ln 2 / 128)). nra. }
   assert (ER : 0.99 <= exp (B d * ln 2)).
   { apply Rabs_le_inv in D. bpow_num_in D. interval with (i_prec 100). }
   unfold z. nra. }
 destruct (fast_decide_scaled_ok yh yl k z v Fh Fl Hy Dw Zlo E ltac:(lia)) as [Fv Bv].
 - rewrite <- Split. apply exp2_below_overflow; [exact Fx | lra].
 - exact Decide.
 - split; [exact Fv | rewrite Split; exact Bv].
Qed.
