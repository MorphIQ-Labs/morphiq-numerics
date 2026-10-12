(** The general expm1 fallback subtracts one in the executable Q128
    arithmetic. The cancellation and addition bounds discharge the generated
    accurate_general.g certificate's hypotheses. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Q Require Q128 QSpec QRound.
From Binary64 Require Import Binary64Add IEEE64.
Require Import ExpAccurate Expm1Scale Expm1GeneralBounds Ln1pLemmas StageGappa Expm1GeneralReduction.
Open Scope R_scope.
Definition em_qminusone := Q128.from_f64 13830554455654793216.
Lemma em_qminusone_ok : QSpec.normalized 128 (Q128.m em_qminusone) /\ Q128.qval em_qminusone = -1.
Proof.
 change (QSpec.normalized 128 (2^127) /\ - IZR (2^127) * bpow radix2 (-127) = -1).
 split; [unfold QSpec.normalized; split; lia | ].
 rewrite QSpec.IZR_pow2 by lia.
 replace (- bpow radix2 127 * bpow radix2 (-127)) with (- (bpow radix2 127 * bpow radix2 (-127))) by ring.
 rewrite <- bpow_plus. reflexivity.
Qed.
Definition em_subtract_accurate v := Q128.add v em_qminusone.

Theorem em_subtract_accurate_bound x v : /32 <= Rabs x ->
 QSpec.normalized 128 (Q128.m v) ->
 Rabs (Q128.qval v - exp x) <= 1097/2^134 * exp x ->
 QSpec.normalized 128 (Q128.m (em_subtract_accurate v)) /\
 Rabs (Q128.qval (em_subtract_accurate v) - (exp x-1)) <= /2^118 * Rabs (exp x-1).
Proof.
 intros X Nv Ev. destruct em_qminusone_ok as [Nm Vm].
 destruct (add_any v em_qminusone (or_intror Nv) (or_intror Nm)) as [Nq Eq].
 rewrite Vm in Eq. replace (Rabs (-1)) with 1 in Eq by (rewrite Rabs_left; lra). fold (em_subtract_accurate v) in Nq, Eq.
 set (w := exp x-1) in *.
 pose proof (em_nonzero x X) as W. fold w in W.
 assert (W0 : w <> 0) by (intros H; rewrite H, Rabs_R0 in W; lra).
 pose proof (exp_pos x) as P.
 destruct (em_ratio_bounds x X) as [R1 R2]. fold w in R1, R2.
 assert (Vb : Rabs (Q128.qval v) <= (1+1097/2^134)*exp x).
 { replace (Q128.qval v) with ((Q128.qval v-exp x)+exp x) at 1 by ring.
   apply Rle_trans with (1 := Rabs_triang _ _). rewrite (Rabs_pos_eq (exp x)) by lra. lra. }
 assert (Max : Rmax (Rabs (Q128.qval v)) 1 <= (542/16)*Rabs w).
 { apply Rmax_lub; [ | lra].
   assert (C : (1+1097/2^134)*32.51 <= 542/16) by interval with (i_prec 160).
   assert (A : 0 < 1+1097/2^134) by interval with (i_prec 160).
   apply Rle_trans with (1 := Vb).
   apply Rle_trans with ((1+1097/2^134)*(32.51*Rabs w)); [apply Rmult_le_compat_l; lra | nra]. }
 set (eV := (Q128.qval v-exp x)/exp x).
 set (sr := (Q128.qval (em_subtract_accurate v)-(Q128.qval v-1))/w).
 assert (EV : -1097/2^134 <= eV <= 1097/2^134).
 { assert (A : Rabs eV <= 1097/2^134).
   { apply ratio_bound; [rewrite (Rabs_pos_eq (exp x)); lra | rewrite (Rabs_pos_eq (exp x)) by lra; exact Ev]. }
   apply Rabs_le_inv in A. lra. }
 assert (SR : -542/2^130 <= sr <= 542/2^130).
 { assert (A : Rabs sr <= 542/2^130).
   { apply ratio_bound; [lra | ].
   apply Rle_trans with (1 := Eq). apply Rle_trans with (bpow radix2 (-126)*((542/16)*Rabs w)).
   - apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Max].
   - bpow_num. right. field. }
   apply Rabs_le_inv in A. lra. }
 pose proof (em_accurate_certificate (exp x/w) eV sr (em_ratio_certificate x X) EV SR) as C.
 assert (Id : exp x/w*eV+sr = (Q128.qval (em_subtract_accurate v)-w)/w).
 { unfold eV, sr, w. field. split; [exact W0 | lra]. }
 rewrite Id in C. apply Rabs_le in C.
 assert (E : Rabs (Q128.qval (em_subtract_accurate v)-w) <= /2^118*Rabs w).
 { replace (Q128.qval (em_subtract_accurate v)-w) with
     (((Q128.qval (em_subtract_accurate v)-w)/w)*w) by (field; exact W0).
   rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact C]. }
 split; [ | exact E]. destruct Nq as [Z0 | N]; [ | exact N]. exfalso.
 rewrite (qval_zero _ Z0), Rminus_0_l, Rabs_Ropp in E.
 assert (/2^118 < 1) by interval with (i_prec 160). nra.
Qed.

Definition em_general_accurate x :=
 let '(j,k,n,r1,p2,e2,_,_) := em_reduce x in
 em_subtract_accurate (accurate_at (acc_r n r1 p2 e2) (Z.to_nat j) k).

Theorem em_general_accurate_bound x : finite x -> -37.43 <= B x ->
 B x < B ExpFast.c_x_overflow -> /32 <= Rabs (B x) ->
 QSpec.normalized 128 (Q128.m (em_general_accurate x)) /\
 Rabs (Q128.qval (em_general_accurate x)-(exp (B x)-1)) <= /2^118*Rabs (exp (B x)-1).
Proof.
 intros Fx Lo Hi X. pose proof (em_reduce_ok x Fx Lo Hi X) as RD.
 unfold em_general_accurate. revert RD. generalize (em_reduce x).
 intros [[[[[[[j k] n] r1] p2] e2] rh] rl]
   [J [K [Bn [Fh [Fl [Dw [Gh [Gl [Err [HR [Nr Er]]]]]]]]]]].
 destruct (accurate_bound (acc_r n r1 p2 e2) (Z.to_nat j) k
   (B x-IZR (128*k+j)*(ln 2/128)) Nr Er HR ltac:(lia)) as [N E].
 cbv zeta in E.
 assert (Split : exp (INR (Z.to_nat j)*ln 2/128)*
   exp (B x-IZR (128*k+j)*(ln 2/128))*bpow radix2 k = exp (B x)).
 { rewrite <- ExpFast.exp_split. f_equal. rewrite Z2Nat.id by lia. ring. }
 rewrite Split in E. apply em_subtract_accurate_bound; assumption.
Qed.

(** The conversion rounds the proved Q128 approximation once. This does not
    assume a worst-case midpoint separation for expm1. *)
Theorem em_general_accurate_round x : finite x -> -37.43 <= B x ->
 B x < B ExpFast.c_x_overflow -> /32 <= Rabs (B x) ->
 finite (Q128.to_f64 (em_general_accurate x)) /\
 B (Q128.to_f64 (em_general_accurate x)) = rndF (Q128.qval (em_general_accurate x)).
Proof.
 intros Fx Lo Hi X. destruct (em_general_accurate_bound x Fx Lo Hi X) as [N E].
 pose proof (ExpFast.exp_below_overflow x Fx Hi) as Eb. pose proof (exp_pos (B x)) as Ep.
 assert (Big : 1 <= 2^1024*(1-/2^46)) by interval with (i_prec 64).
 assert (Wb : Rabs (exp (B x)-1) <= 2^1024*(1-/2^46)) by (apply Rabs_le; lra).
 assert (Qb : Rabs (Q128.qval (em_general_accurate x)) <= (1+/2^118)*2^1024*(1-/2^46)).
 { pose proof (Rabs_triang_inv (Q128.qval (em_general_accurate x)) (exp (B x)-1)).
   pose proof (Rabs_pos (exp (B x)-1)). nra. }
 assert (Bd : bnd (2^53-64) 971 (Q128.qval (em_general_accurate x))).
 { unfold bnd. apply Rle_trans with (1:=Qb). interval with (i_prec 160). }
 assert (Ov : Rabs (rndF (Q128.qval (em_general_accurate x))) < bpow radix2 1024).
 { apply Rle_lt_trans with (1:=bnd_round (2^53-64) 971 _ ltac:(lia) ltac:(lia) Bd). apply bnd_lt; lia. }
 split; [ | apply to_f64_val; assumption].
 rewrite Q128.to_f64_ok by exact N. unfold QRound.bn.
 pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE
   (QRound.signed (Q128.neg (em_general_accurate x)) (Q128.m (em_general_accurate x)))
   (Q128.e (em_general_accurate x)) (Q128.neg (em_general_accurate x))) as C.
 rewrite Rlt_bool_true in C by exact Ov. exact (proj1 (proj2 C)).
Qed.
