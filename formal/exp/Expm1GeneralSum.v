(** Renormalization of a scaled double word, with a finite margin at the
    largest binade. The small trailing word keeps every 2Sum subtraction finite. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Double Require Import DWPlus F2Sum F2SumFLX.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid RoundingTest.
Require Import StageGappa.
Open Scope R_scope.
Lemma em_round_large_error v : Rabs v < bpow radix2 1024 ->
 Rabs (rndF v-v) <= bpow radix2 971.
Proof.
 intros V. destruct (Req_dec v 0) as [-> | N].
 - rewrite round_0 by apply valid_rnd_N. rewrite Rminus_0_r, Rabs_R0. apply bpow_ge_0.
 - apply Rle_trans with (/2 * ulp radix2 (FLT_exp emin prec) v).
   + apply error_le_half_ulp. exact _.
   + rewrite ulp_neq_0 by exact N. unfold cexp.
     pose proof (mag_le_bpow radix2 v 1024 N V) as M.
     apply Rle_trans with (bpow radix2 (FLT_exp emin prec (mag radix2 v))).
     * pose proof (bpow_ge_0 radix2 (FLT_exp emin prec (mag radix2 v))). lra.
     * apply bpow_le. unfold FLT_exp, emin, prec. lia.
Qed.
Theorem em_two_sum_large a b : finite a -> finite b ->
 B a = rndF (B a+B b) -> bnd (2^53-4) 971 (B a) -> bnd 2 971 (B b) ->
 let '(s,t) := two_sum64 a b in
 finite s /\ finite t /\ B s = B a /\ B s+B t = B a+B b.
Proof.
 intros Fa Fb DW A L.
 destruct (fadd_bnd (2^53-2) 971 a b Fa Fb ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia))
   as [Fs [Es Bs]].
 { replace (2^53-2)%Z with ((2^53-4)+2)%Z by ring. exact (bnd_plus _ _ _ _ _ A L). }
 assert (S : B (fadd a b) = B a) by (rewrite Es; symmetry; exact DW).
 set (s := fadd a b) in *.
 destruct (fsub_bnd (2^53-2) 971 s b Fs Fb ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia))
   as [Fp [Ep Bp]].
 { rewrite S. replace (2^53-2)%Z with ((2^53-4)+2)%Z by ring. exact (bnd_minus _ _ _ _ _ A L). }
 set (p := fsub s b) in *.
 assert (Er : Rabs (B p-(B a-B b)) <= bpow radix2 971).
 { rewrite Ep, S. apply em_round_large_error.
   apply Rle_lt_trans with (1 := bnd_minus _ _ _ _ _ A L).
   apply bnd_lt; lia. }
 assert (Ap : bnd 3 971 (B a-B p)).
 { unfold bnd in *. pose proof (Rabs_triang (B b) (- (B p-(B a-B b)))) as T.
   replace (B b + - (B p-(B a-B b))) with (B a-B p) in T by ring.
   rewrite Rabs_Ropp in T. lra. }
 destruct (fsub_bnd 3 971 s p Fs Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Fq [Eq Bq]].
 { rewrite S. exact Ap. }
 set (q := fsub s p) in *.
 destruct (fsub_bnd 3 971 a p Fa Fp ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ap) as [Fd [Ed Bd]].
 destruct (fsub_bnd 5 971 b q Fb Fq ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   (bnd_minus _ _ _ _ _ L Bq)) as [Fe [Ee Be]].
 destruct (fadd_bnd 8 971 (fsub a p) (fsub b q) Fd Fe ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   (bnd_plus _ _ _ _ _ Bd Be)) as [Ft [Et Bt]].
 assert (Pair : (B s, B (fadd (fsub a p) (fsub b q))) = two_sum (B a) (B b)).
 { unfold two_sum. rewrite Et, Ee, Ed, Eq, Ep, Es. reflexivity. }
 rewrite (two_sum_eq _ _ (B_fmt a) (B_fmt b)) in Pair. injection Pair as H T.
 unfold two_sum64. fold s p q. repeat split; try assumption.
 rewrite H, T, (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl (B a) (B b)
   (fmtF_fmtX _ (B_fmt a)) (fmtF_fmtX _ (B_fmt b))). ring.
Qed.
